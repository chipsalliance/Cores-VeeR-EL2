# Copyright (c) 2025 Antmicro
# SPDX-License-Identifier: Apache-2.0
import logging
import os
import random
from dataclasses import dataclass
from enum import IntEnum

import cocotb
import csrs
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, FallingEdge, RisingEdge, ReadOnly
from csrs import get_bit
from pyuvm import (
    ConfigDB,
    uvm_analysis_port,
    uvm_component,
    uvm_driver,
    uvm_env,
    uvm_get_port,
    uvm_report_object,
    uvm_sequence,
    uvm_sequence_item,
    uvm_sequencer,
    uvm_test,
    uvm_tlm_analysis_fifo,
)

# ==============================================================================


@dataclass
class TriggerAnyPktT:
    select: int = 0
    match: int = 0
    store: int = 0
    load: int = 0
    execute: int = 0
    m: int = 0
    tdata2: int = 0

    @staticmethod
    def get_from_dut(dut):
        trigger_pkt_any_select = int(dut.trigger_pkt_any_select.value)
        trigger_pkt_any_match = int(dut.trigger_pkt_any_match.value)
        trigger_pkt_any_store = int(dut.trigger_pkt_any_store.value)
        trigger_pkt_any_load = int(dut.trigger_pkt_any_load.value)
        trigger_pkt_any_execute = int(dut.trigger_pkt_any_execute.value)
        trigger_pkt_any_m = int(dut.trigger_pkt_any_m.value)
        trigger_pkt_any_tdata2 = int(dut.trigger_pkt_any_tdata2.value)
        return TriggerAnyPktT(
            trigger_pkt_any_select,
            trigger_pkt_any_match,
            trigger_pkt_any_store,
            trigger_pkt_any_load,
            trigger_pkt_any_execute,
            trigger_pkt_any_m,
            trigger_pkt_any_tdata2,
        )


def log_mismatch_error(logger, name, expected, got):
    logger.error(f"{name} {hex(expected)} != {hex(got)} (should be {hex(expected)})")


csr_list = [getattr(csrs, mod) for mod in dir(csrs) if isinstance(getattr(csrs, mod), csrs.CSR)]
CSR_OPCODE  = 0b1110011
ADDI_OPCODE = 0b0010011


class Funct3(IntEnum):
    CSRRW = 0b001
    CSRRS = 0b010
    CSRRC = 0b011
    CSRRWI = 0b101
    CSRRSI = 0b110
    CSRRCI = 0b111
    ZERO   = 0b000


def i_type_inst(csr, rs1, funct3, rd, opcode):
    csr_mask = (1 << 13) - 1
    rs1_mask = (1 << 6) - 1
    funct3_mask = (1 << 4) - 1
    rd_mask = (1 << 6) - 1
    opcode_mask = (1 << 8) - 1
    return (
        (csr & csr_mask) << 20
        | (rs1 & rs1_mask) << 15
        | (funct3 & funct3_mask) << 12
        | (rd & rd_mask) << 7
        | (opcode & opcode_mask)
    )


@dataclass
class ReadCSRInst:
    csr: int = 0
    funct3: Funct3 = Funct3.CSRRS

    def encode(self):
        return i_type_inst(self.csr, 0, self.funct3, 0, CSR_OPCODE)


@dataclass
class WriteCSRInst:
    csr: int = 0
    funct3: Funct3 = Funct3.CSRRW

    def encode(self):
        return i_type_inst(self.csr, 0, self.funct3, 0, CSR_OPCODE)


@dataclass
class ReadGPRInst:
    gpr: int = 0
    funct3: Funct3 = Funct3.ZERO

    def encode(self):
        return i_type_inst(0, self.gpr, self.funct3, 0, ADDI_OPCODE)


@dataclass
class WriteGPRInst:
    gpr: int = 0
    funct3: Funct3 = Funct3.ZERO

    def encode(self):
        return i_type_inst(0, 0, self.funct3, self.gpr, ADDI_OPCODE)


def randint(width=32):
    return random.randint(0, 2 ** (width) - 1)


class DecInputItem(uvm_sequence_item):
    """
    Trigger Logic input data
    """

    CSRS = (
        csrs.MCOUNTINHIBIT,
        csrs.MDCCMECT,
        csrs.MEICURPL,
        csrs.MEIPT,
        csrs.MFDC,
        csrs.MFDHT,
        csrs.MHPMC3,
        csrs.MHPMC3H,
        csrs.MHPMC4,
        csrs.MHPMC4H,
        csrs.MHPMC5,
        csrs.MHPMC5H,
        csrs.MHPMC6,
        csrs.MHPMC6H,
        csrs.MHPME3,
        csrs.MHPME4,
        csrs.MHPME5,
        csrs.MHPME6,
        csrs.MICCMECT,
        csrs.MICECT,
        csrs.MINSTRETH,
        csrs.MINSTRETL,
        csrs.MRAC,
        csrs.MTVEC,
    )

    def __init__(
        self,
        pic_pl=0,
        pic_claimid=0,
        exu_i0_result_x=0,
        ifu_ic_debug_rd_data=0,
        gpr_addr=0,
        gpr_data=0,
        gpr_oper=None,
        csrw_instr=0,
        csrr_instr=0,
        csr_addr=0,
        csr_data=0,
        csr_oper=None,
        mtdata1=0,
        mtdata2=0,
        mtsel=0,
    ):
        super().__init__("DecInputItem")
        self.exu_i0_result_x = exu_i0_result_x
        self.csr_addr = csr_addr
        self.csr_data = csr_data
        self.csr_oper = csr_oper
        self.csrw_instr = csrw_instr
        self.csrr_instr = csrr_instr
        self.gpr_addr = gpr_addr
        self.gpr_data = gpr_data
        self.gpr_oper = gpr_oper
        self.pic_pl = pic_pl
        self.pic_claimid = pic_claimid
        self.ifu_ic_debug_rd_data = ifu_ic_debug_rd_data
        self.mtdata1 = mtdata1
        self.mtdata2 = mtdata2
        self.mtsel = mtsel

    def randomize(self, test):
        if test == "meihap":
            self.pic_claimid = randint(8)
            self.exu_i0_result_x = randint(22) << 10
            self.csr_addr = csrs.MEIVT
            self.csrw_instr = WriteCSRInst(self.csr_addr).encode()
            self.csrr_instr = ReadCSRInst(self.csr_addr).encode()
        elif test == "mtdata":
            # bits 31:28 are hardcoded to 0x2
            mtdata1 = "0010"
            for _ in range(28):
                mtdata1 += random.choice(["0", "1"])
            # set DMODE (bit 27) to 0 so that the settings are actually taken into account
            # in the list, bits are numbered from 0
            tmp = list(mtdata1)
            tmp[31 - 27] = "0"
            mtdata1 = "".join(tmp)
            self.mtdata1 = int(mtdata1, 2)
            self.mtdata2 = randint(32)
            self.mtsel = randint(2)
        elif test == "csr_access":
            self.csr_addr = random.choice(DecInputItem.CSRS)
            self.exu_i0_result_x = randint()
            self.csrw_instr = WriteCSRInst(self.csr_addr).encode()
            self.csrr_instr = ReadCSRInst(self.csr_addr).encode()
        elif test == "debug_ic_cache":
            self.ifu_ic_debug_rd_data = randint(71)
        elif test == "debug_csrs_access":
            self.exu_i0_result_x = randint(32)
            self.csr_addr = random.choice(
                [csrs.DICAD0, csrs.DICAD0H, csrs.DICAWICS, csrs.DPC, csrs.DCSR]
            )
            self.csrw_instr = WriteCSRInst(self.csr_addr).encode()
            self.csrr_instr = ReadCSRInst(self.csr_addr).encode()
        elif test == "meicidpl":
            self.pic_pl = randint(4)
            self.csr_addr = csrs.MEICIDPL
            self.csrw_instr = WriteCSRInst(self.csr_addr).encode()
            self.csrr_instr = ReadCSRInst(self.csr_addr).encode()
        elif test == "recovery_gpr_access":
            self.gpr_addr = random.randint(0, 31)
            self.gpr_data = random.range(1 << 32) if self.gpr_addr != 0 else 0
            self.gpr_oper = random.choice(["wr_front", "wr_back", "rd_front", "rd_back"])
        elif test == "recovery_csr_access":
            self.csr_addr = random.choice(DecInputItem.CSRS)
            self.csr_data = random.range(1 << 32)
            self.csr_oper = random.choice(["wr_front", "wr_back", "rd_front", "rd_back"])


class DecOutputItem(uvm_sequence_item):
    """
    Trigger Logic output data
    """

    def __init__(
        self,
        csrr_instr=0,
        dec_csr_wrdata_r=0,
        dec_csr_rddata_d=0,
        dec_tlu_meihap=0,
        trigger_pkt_any=TriggerAnyPktT(),
        ifu_ic_debug_rd_data=0,
        gpr_addr=0,
        gpr_data=0,
        gpr_oper=None,
    ):
        super().__init__("DecOutputItem")
        self.csrr_instr = csrr_instr
        self.dec_csr_wrdata_r = dec_csr_wrdata_r
        self.dec_csr_rddata_d = dec_csr_rddata_d
        self.dec_tlu_meihap = dec_tlu_meihap
        self.trigger_pkt_any = trigger_pkt_any
        self.ifu_ic_debug_rd_data = ifu_ic_debug_rd_data
        self.gpr_addr = gpr_addr
        self.gpr_data = gpr_data
        self.gpr_oper = gpr_oper


# ==============================================================================


class DecDriver(uvm_driver):
    """
    Trigger Logic driver
    """

    def __init__(self, *args, **kwargs):
        self.dut = kwargs["dut"]
        del kwargs["dut"]
        super().__init__(*args, **kwargs)

    async def read_csr(self, instr):
        self.dut.ifu_i0_valid.value = 0
        await RisingEdge(self.dut.clk)
        self.dut.ifu_i0_valid.value = 1
        self.dut.ifu_i0_instr.value = instr
        await RisingEdge(self.dut.clk)
        self.dut.ifu_i0_valid.value = 0
        self.dut.ifu_i0_instr.value = 0

    async def write_csr(self, instr, data):
        self.dut.ifu_i0_valid.value = 0
        await RisingEdge(self.dut.clk)
        self.dut.ifu_i0_valid.value = 1
        self.dut.ifu_i0_instr.value = instr
        await RisingEdge(self.dut.clk)
        self.dut.ifu_i0_instr.value = 0
        self.dut.exu_i0_result_x.value = data
        self.dut.ifu_i0_valid.value = 0
        await RisingEdge(self.dut.clk)
        self.dut.exu_i0_result_x.value = 0

    async def read_gpr(self, instr):
        self.dut.ifu_i0_valid.value = 0
        await RisingEdge(self.dut.clk)
        self.dut.ifu_i0_valid.value = 1
        self.dut.ifu_i0_instr.value = instr
        await RisingEdge(self.dut.clk)
        self.dut.ifu_i0_valid.value = 0
        self.dut.ifu_i0_instr.value = 0

    async def write_gpr(self, instr, data):
        self.dut.ifu_i0_valid.value = 0
        await RisingEdge(self.dut.clk)
        self.dut.ifu_i0_valid.value = 1
        self.dut.ifu_i0_instr.value = instr
        await RisingEdge(self.dut.clk)
        self.dut.ifu_i0_instr.value = 0
        self.dut.exu_i0_result_x.value = data
        self.dut.ifu_i0_valid.value = 0
        await RisingEdge(self.dut.clk)
        self.dut.exu_i0_result_x.value = 0

    async def read_gpr_recovery(self, addr):
        await RisingEdge(self.dut.clk)
        self.dut.recovery_gpr_en.value = 1
        self.dut.recovery_gpr_rdaddr.value = addr
        await RisingEdge(self.dut.clk)
        data = self.dut.recovery_gpr_rddata.value
        self.dut.recovery_gpr_en.value = 0

    async def write_gpr_recovery(self, addr, data):
        await RisingEdge(self.dut.clk)
        self.dut.recovery_gpr_en.value = 1
        self.dut.recovery_gpr_wen.value = 1
        self.dut.recovery_gpr_wraddr.value = addr
        self.dut.recovery_gpr_wrdata.value = data
        await RisingEdge(self.dut.clk)
        # Disable wren and drive random data to check if its honored
        self.dut.recovery_gpr_en.value = 0
        self.dut.recovery_gpr_wen.value = 0
        self.dut.recovery_gpr_wrdata.value = random.randrange(1 << 32)

    async def read_csr_recovery(self, addr):
        """
        Reads a CSR through TMR recovery backdoor port
        """
        await RisingEdge(self.dut.clk)
        self.dut.recovery_csr_en.value = 1
        self.dut.recovery_csr_rdaddr.value = addr
        await RisingEdge(self.dut.clk)
        data = self.dut.recovery_csr_rddata.value
        self.dut.recovery_csr_en.value = 0
        return data

    async def write_csr_recovery(self, addr, data):
        """
        Writes a CSR through TMR recovery backdoor port
        """
        await RisingEdge(self.dut.clk)
        self.dut.recovery_csr_en.value = 1
        self.dut.recovery_csr_wen.value = 1
        self.dut.recovery_csr_wraddr.value = addr
        self.dut.recovery_csr_wrdata.value = data
        await RisingEdge(self.dut.clk)
        # Disable wren and drive random data to check if its honored
        self.dut.recovery_csr_wen.value = 0
        self.dut.recovery_csr_wrdata.value = random.randrange(1 << 32)
        await RisingEdge(self.dut.clk)
        self.dut.recovery_csr_en.value = 0

    async def run_phase(self):
        while True:
            it = await self.seq_item_port.get_next_item()
            if isinstance(it, DecInputItem):
                test = ConfigDB().get(self, "", "TEST")
                if test == "meihap":
                    # Write MEIVT
                    await self.write_csr(it.csrw_instr, it.exu_i0_result_x)
                    await ClockCycles(self.dut.clk, 2)
                    # Write pic_claimid via MEICPCT
                    self.dut.pic_claimid.value = it.pic_claimid
                    instr = WriteCSRInst(csrs.MEICPCT).encode()
                    await self.write_csr(instr, it.exu_i0_result_x)
                    # Allow output monitor to catch the data on the outputs
                    await ClockCycles(self.dut.clk, 2)
                elif test == "mtdata":
                    await self.write_csr(WriteCSRInst(csrs.MTSEL).encode(), it.mtsel)
                    await self.write_csr(WriteCSRInst(csrs.MTDATA1).encode(), it.mtdata1)
                    await self.write_csr(WriteCSRInst(csrs.MTDATA2).encode(), it.mtdata2)
                    await ClockCycles(self.dut.clk, 4)
                elif test in ["csr_access"]:
                    # Write CSR
                    await self.write_csr(it.csrw_instr, it.exu_i0_result_x)
                    await ClockCycles(self.dut.clk, 2)
                    # Read the CSR back
                    await self.read_csr(it.csrr_instr)
                    await RisingEdge(self.dut.clk)
                elif test == "debug_ic_cache":
                    self.dut.ifu_ic_debug_rd_data_valid.value = 1
                    self.dut.ifu_ic_debug_rd_data.value = it.ifu_ic_debug_rd_data
                    await RisingEdge(self.dut.clk)
                    self.dut.ifu_ic_debug_rd_data_valid.value = 0
                    await self.read_csr(ReadCSRInst(csrs.DICAD0).encode())
                    await self.read_csr(ReadCSRInst(csrs.DICAD0H).encode())
                    await self.read_csr(ReadCSRInst(csrs.DICAD1).encode())
                elif test == "debug_csrs_access":
                    await self.write_csr(it.csrw_instr, it.exu_i0_result_x)
                    await ClockCycles(self.dut.clk, 2)
                    await self.read_csr(it.csrr_instr)
                    await ClockCycles(self.dut.clk, 2)
                elif test == "meicidpl":
                    self.dut.pic_pl.value = it.pic_pl
                    await self.write_csr(it.csrw_instr, 0)
                    await ClockCycles(self.dut.clk, 2)
                    await self.read_csr(it.csrr_instr)
                    await RisingEdge(self.dut.clk)
                elif test == "recovery_gpr_access":
                    match it.gpr_oper:
                        case "wr_front":
                            await self.write_gpr(WriteGPRInst(it.gpr_addr).encode(), it.gpr_data)
                        case "rd_front":
                            await self.read_gpr(ReadGPRInst(it.gpr_addr).encode())
                        case "wr_back":
                            await self.write_gpr_recovery(it.gpr_addr, it.gpr_data)
                        case "rd_back":
                            await self.read_gpr_recovery(it.gpr_addr)
                        case _:
                            raise RuntimeError("Unknown GPR oper '{}'".format(it.gpr_oper))
                elif test == "recovery_csr_access":
                    if it.csr_oper == "wr_front":
                        await self.write_csr(WriteCSRInst(it.csr_addr).encode(), it.csr_data)
                    elif it.csr_oper == "wr_back":
                        await self.write_csr_recovery(it.csr_addr, it.csr_data)
                    elif it.csr_oper == "rd_front":
                        await self.read_csr(ReadCSRInst(it.csr_addr).encode())
                    elif it.csr_oper == "rd_back":
                        await self.read_csr_recovery(it.csr_addr)
                    else:
                        assert False, it.csr_oper
                else:
                    raise RuntimeError("Unknown test '{}'".format(test))
            else:
                raise RuntimeError("Unknown item '{}'".format(type(it)))

            self.seq_item_port.item_done()


class DecInputMonitor(uvm_component):
    """
    Monitor for Trigger Logic inputs
    """

    def __init__(self, *args, **kwargs):
        self.dut = kwargs["dut"]
        del kwargs["dut"]
        super().__init__(*args, **kwargs)

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    async def run_phase(self):
        while True:
            test = ConfigDB().get(self, "", "TEST")
            if test == "meihap":
                await RisingEdge(self.dut.ifu_i0_valid)
                await ClockCycles(self.dut.clk, 2)
                exu_i0_result_x = int(self.dut.exu_i0_result_x.value)
                await RisingEdge(self.dut.ifu_i0_valid)
                pic_claimid = int(self.dut.pic_claimid.value)
                self.ap.write(
                    DecInputItem(pic_claimid=pic_claimid, exu_i0_result_x=exu_i0_result_x)
                )
            elif test == "mtdata":
                await RisingEdge(self.dut.ifu_i0_valid)
                await ClockCycles(self.dut.clk, 2)
                mtsel = int(self.dut.exu_i0_result_x.value)
                await RisingEdge(self.dut.ifu_i0_valid)
                await ClockCycles(self.dut.clk, 2)
                mtdata1 = int(self.dut.exu_i0_result_x.value)
                await RisingEdge(self.dut.ifu_i0_valid)
                await ClockCycles(self.dut.clk, 2)
                mtdata2 = int(self.dut.exu_i0_result_x.value)
                self.ap.write(DecInputItem(mtdata1=mtdata1, mtdata2=mtdata2, mtsel=mtsel))
            elif test in ["csr_access"]:
                # Wait for CSR write
                await RisingEdge(self.dut.ifu_i0_valid)
                await RisingEdge(self.dut.clk)
                csrw_instr = int(self.dut.ifu_i0_instr.value)
                await RisingEdge(self.dut.clk)
                exu_i0_result_x = int(self.dut.exu_i0_result_x.value)
                # Wait for CSR read
                await RisingEdge(self.dut.ifu_i0_valid)
                await RisingEdge(self.dut.clk)
                csrr_instr = int(self.dut.ifu_i0_instr.value)
                self.ap.write(
                    DecInputItem(
                        csrw_instr=csrw_instr,
                        csrr_instr=csrr_instr,
                        exu_i0_result_x=exu_i0_result_x,
                    )
                )
            elif test == "debug_ic_cache":
                # Wait for CSR write
                await RisingEdge(self.dut.ifu_ic_debug_rd_data_valid)
                await RisingEdge(self.dut.clk)
                ic_debug_rd_data = int(self.dut.ifu_ic_debug_rd_data.value)
                self.ap.write(DecInputItem(ifu_ic_debug_rd_data=ic_debug_rd_data))
                # Wait for CSR reads
                await ClockCycles(self.dut.clk, 4)
            elif test == "debug_csrs_access":
                await RisingEdge(self.dut.ifu_i0_valid)
                await RisingEdge(self.dut.clk)
                csr_addr = int(self.dut.ifu_i0_instr.value) >> 20
                await ClockCycles(self.dut.clk, 1)
                exu_i0_result_x = int(self.dut.exu_i0_result_x.value)
                # Await CSR read
                await RisingEdge(self.dut.ifu_i0_valid)
                await RisingEdge(self.dut.clk)
                self.ap.write(DecInputItem(csr_addr=csr_addr, exu_i0_result_x=exu_i0_result_x))
            elif test == "meicidpl":
                await RisingEdge(self.dut.ifu_i0_valid)
                csr_addr = int(self.dut.ifu_i0_instr.value) >> 20
                await ClockCycles(self.dut.clk, 2)
                exu_i0_result_x = int(self.dut.exu_i0_result_x.value)
                await RisingEdge(self.dut.ifu_i0_valid)
                self.ap.write(DecInputItem(csr_addr=csr_addr, exu_i0_result_x=exu_i0_result_x))
            elif test == "recovery_gpr_access":
                await RisingEdge(self.dut.clk)
                # Backdoor access
                if self.dut.recovery_gpr_en.value and self.dut.recovery_gpr_wen.value:
                    addr = int(self.dut.recovery_gpr_wraddr.value)
                    data = int(self.dut.recovery_gpr_wrdata.value)
                    self.ap.write(DecInputItem(gpr_addr=addr, gpr_data=data, gpr_oper="wr_back"))
                # Frontdoor access
                elif self.dut.ifu_i0_valid.value:
                    func = (int(self.dut.ifu_i0_instr.value) >> 12) & 0x7
                    dst_addr =  (int(self.dut.ifu_i0_instr.value) >> 7) & 0x1f
                    if func == 0 and dst_addr != 0: # ZERO
                        await RisingEdge(self.dut.clk)
                        data = int(self.dut.exu_i0_result_x.value)
                        self.ap.write(DecInputItem(gpr_addr=dst_addr, gpr_oper="wr_front"))

            elif test == "recovery_csr_access":
                await RisingEdge(self.dut.clk)

                # Backdoor write
                if self.dut.recovery_csr_en.value:
                    if self.dut.recovery_csr_wen.value:
                        addr = int(self.dut.recovery_csr_wraddr.value)
                        data = int(self.dut.recovery_csr_wrdata.value)
                        self.ap.write(DecInputItem(csr_addr=addr, csr_data=data, csr_oper="wr_back"))

                # Frontdoor write
                else:
                    if self.dut.ifu_i0_valid.value:
                        addr =  int(self.dut.ifu_i0_instr.value) >> 20
                        func = (int(self.dut.ifu_i0_instr.value) >> 12) & 0x7
                        if func in [Funct3.CSRRW]:
                            await RisingEdge(self.dut.clk)
                            data = int(self.dut.exu_i0_result_x.value)
                            self.ap.write(DecInputItem(csr_addr=addr, csr_data=data, csr_oper="wr_front"))

class DecOutputMonitor(uvm_component):
    """
    Monitor for Trigger Logic outputs
    """

    def __init__(self, *args, **kwargs):
        self.dut = kwargs["dut"]
        del kwargs["dut"]
        super().__init__(*args, **kwargs)

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    async def run_phase(self):
        while True:
            test = ConfigDB().get(self, "", "TEST")
            if test == "meihap":
                for _ in range(2):
                    await RisingEdge(self.dut.ifu_i0_valid)
                await ClockCycles(self.dut.clk, 4)
                dec_tlu_meihap = int(self.dut.dec_tlu_meihap.value)
                self.ap.write(DecOutputItem(dec_tlu_meihap=dec_tlu_meihap))
            elif test == "mtdata":
                # Wait for CSR writes
                for _ in range(3):
                    await RisingEdge(self.dut.ifu_i0_valid)
                # Wait for the outputs
                await ClockCycles(self.dut.clk, 4)
                trigger_pkt_any = TriggerAnyPktT.get_from_dut(self.dut)
                self.ap.write(DecOutputItem(trigger_pkt_any=trigger_pkt_any))
            elif test in ["csr_access"]:
                for _ in range(2):
                    await RisingEdge(self.dut.ifu_i0_valid)
                await RisingEdge(self.dut.clk)
                csrr_instr = int(self.dut.ifu_i0_instr.value)
                dec_csr_rddata_d = int(self.dut.dec_csr_rddata_d.value)
                self.ap.write(
                    DecOutputItem(
                        csrr_instr=csrr_instr,
                        dec_csr_rddata_d=dec_csr_rddata_d,
                    )
                )
            elif test == "debug_ic_cache":
                await RisingEdge(self.dut.ifu_ic_debug_rd_data_valid)
                await RisingEdge(self.dut.ifu_i0_valid)
                await RisingEdge(self.dut.clk)
                dicad0 = int(self.dut.dec_csr_rddata_d.value)
                await RisingEdge(self.dut.ifu_i0_valid)
                await RisingEdge(self.dut.clk)
                dicad0h = int(self.dut.dec_csr_rddata_d.value)
                await RisingEdge(self.dut.ifu_i0_valid)
                await RisingEdge(self.dut.clk)
                dicad1 = int(self.dut.dec_csr_rddata_d.value)
                ifu_ic_debug_rd_data = dicad0 | (dicad0h << 32) | (dicad1 << 64)
                self.ap.write(DecOutputItem(ifu_ic_debug_rd_data=ifu_ic_debug_rd_data))
            elif test == "debug_csrs_access":
                for _ in range(2):
                    await RisingEdge(self.dut.ifu_i0_valid)
                await RisingEdge(self.dut.clk)
                dec_csr_rddata_d = int(self.dut.dec_csr_rddata_d.value)
                self.ap.write(DecOutputItem(dec_csr_rddata_d=dec_csr_rddata_d))
            elif test == "meicidpl":
                for _ in range(2):
                    await RisingEdge(self.dut.ifu_i0_valid)
                csrr_instr = int(self.dut.ifu_i0_instr.value)
                await RisingEdge(self.dut.clk)
                dec_csr_rddata_d = int(self.dut.dec_csr_rddata_d.value)
                self.ap.write(
                    DecOutputItem(
                        csrr_instr=csrr_instr,
                        dec_csr_rddata_d=dec_csr_rddata_d,
                    )
                )
            elif test == "recovery_gpr_access":
                await RisingEdge(self.dut.clk)
                if not self.dut.recovery_gpr_en.value and self.dut.dec_i0_rs1_en_d.value:
                    src_addr =  (int(self.dut.ifu_i0_instr.value) >> 15) & 0x1f
                    func = (int(self.dut.ifu_i0_instr.value) >> 12) & 0x7
                    if func == 0 and src_addr != 0: # ZERO
                        data = int(self.dut.gpr_i0_rs1_d.value)
                        self.ap.write(DecOutputItem(gpr_addr=src_addr, gpr_data=data, gpr_oper="rd_front"))
                elif self.dut.recovery_gpr_en.value and self.dut.recovery_gpr_wen.value == 0:
                    addr = int(self.dut.recovery_gpr_rdaddr.value)
                    data = int(self.dut.recovery_gpr_rddata.value)
                    self.ap.write(DecOutputItem(gpr_addr=addr, gpr_data=data, gpr_oper="rd_back"))
            elif test == "recovery_csr_access":
                await RisingEdge(self.dut.clk)
                await ReadOnly()

                # Backdoor read
                if self.dut.recovery_csr_en.value:
                    if not self.dut.recovery_csr_wen.value:
                        addr = int(self.dut.recovery_csr_rdaddr.value)
                        data = int(self.dut.recovery_csr_rddata.value)
                        self.ap.write(DecInputItem(csr_addr=addr, csr_data=data, csr_oper="rd_back"))

                # Frontdoor read
                else:
                    if self.dut.ifu_i0_valid.value:
                        addr =  int(self.dut.ifu_i0_instr.value) >> 20
                        func = (int(self.dut.ifu_i0_instr.value) >> 12) & 0x7
                        if func in [Funct3.CSRRS]:
                            data = int(self.dut.dec_csr_rddata_d.value)
                            self.ap.write(DecInputItem(csr_addr=addr, csr_data=data, csr_oper="rd_front"))

# ==============================================================================


class DecScoreboard(uvm_component):
    """
    Trigger Logic scoreboard
    """

    def __init__(self, name, parent):
        super().__init__(name, parent)

        self.passed = None

    def build_phase(self):
        self.fifo_inp = uvm_tlm_analysis_fifo("fifo_inp", self)
        self.fifo_out = uvm_tlm_analysis_fifo("fifo_out", self)
        self.port_inp = uvm_get_port("port_inp", self)
        self.port_out = uvm_get_port("port_out", self)

    def connect_phase(self):
        self.port_inp.connect(self.fifo_inp.get_export)
        self.port_out.connect(self.fifo_out.get_export)

    def check_phase(self):  # noqa: C901
        # Get item pairs
        while True:
            got_inp, item_inp = self.port_inp.try_get()
            got_out, item_out = self.port_out.try_get()

            if not got_inp and got_out:
                self.logger.error("No input item for output item")
                self.passed = False
                break

            if got_inp and not got_out:
                self.logger.error("No output item for input item")
                self.passed = False
                break

            if not got_inp and not got_out:
                if getattr(self, "unmatched_read", None) is not None:
                    self.passed = len(self.unmatched_read) == 0 if self.passed else False
                if getattr(self, "unmatched_write", None) is not None:
                    self.passed = len(self.unmatched_write) == 0 if self.passed else False
                break

            if self.passed is None:
                self.passed = True

            test = ConfigDB().get(self, "", "TEST")
            if test == "meihap":
                pic_claimid_i = item_inp.pic_claimid
                pic_claimid_o = item_out.dec_tlu_meihap & 0xFF
                meivt_i = item_inp.exu_i0_result_x >> 12
                meivt_o = item_out.dec_tlu_meihap >> 10

                if pic_claimid_i != pic_claimid_o:
                    log_mismatch_error(self.logger, "pic_claimid", pic_claimid_i, pic_claimid_o)
                    self.passed = False

                if meivt_i != meivt_o:
                    log_mismatch_error(self.logger, "meivt", meivt_i, meivt_o)
                    self.passed = False

            elif test == "mtdata":
                tdata2_mask = 0xFFFFFFFF
                mtsel = item_inp.mtsel

                mtdata1_i = item_inp.mtdata1
                mtdata2_i = item_inp.mtdata2
                trigger_pkt_any = item_out.trigger_pkt_any

                select_i = get_bit(mtdata1_i, 19)
                match_i = get_bit(mtdata1_i, 7)
                store_i = get_bit(mtdata1_i, 1)
                load_i = get_bit(mtdata1_i, 0) & ~get_bit(mtdata1_i, 19)
                execute_i = get_bit(mtdata1_i, 2) & ~get_bit(mtdata1_i, 19)
                m_i = get_bit(mtdata1_i, 6)

                select_o = get_bit(trigger_pkt_any.select, mtsel)
                match_o = get_bit(trigger_pkt_any.match, mtsel)
                store_o = get_bit(trigger_pkt_any.store, mtsel)
                load_o = get_bit(trigger_pkt_any.load, mtsel)
                execute_o = get_bit(trigger_pkt_any.execute, mtsel)
                m_o = get_bit(trigger_pkt_any.m, mtsel)

                mtdata2_o = (trigger_pkt_any.tdata2 >> (mtsel * 32)) & tdata2_mask

                if mtdata2_i != mtdata2_o:
                    log_mismatch_error(self.logger, "mtdata2", mtdata2_i, mtdata2_o)
                    self.passed = False
                if select_i != select_o:
                    log_mismatch_error(self.logger, "select", select_i, select_o)
                    self.passed = False
                if match_i != match_o:
                    log_mismatch_error(self.logger, "match", match_i, match_o)
                    self.passed = False
                if store_i != store_o:
                    log_mismatch_error(self.logger, "store", store_i, store_o)
                    self.passed = False
                if load_i != load_o:
                    log_mismatch_error(self.logger, "load", load_i, load_o)
                    self.passed = False
                if execute_i != execute_o:
                    log_mismatch_error(self.logger, "execute", execute_i, execute_o)
                    self.passed = False
                if m_i != m_o:
                    log_mismatch_error(self.logger, "m", m_i, m_o)
                    self.passed = False

            elif test == "csr_access":
                i0 = item_inp.csrw_instr
                i1 = item_inp.csrr_instr

                wr_addr = (i0 >> 20) & ((1 << 13) - 1)
                rd_addr = (i1 >> 20) & ((1 << 13) - 1)

                if wr_addr != rd_addr:
                    err_msg = f"Write to reg[{hex(wr_addr)}] but read from reg[{hex(rd_addr)}]"
                    self.logger.error(err_msg)
                    self.passed = False

                csr = rd_addr
                data_in = item_inp.exu_i0_result_x
                data_out = item_out.dec_csr_rddata_d

                for c in csr_list:
                    if c == csr:
                        data_in = c.out(data_in)
                        break

                if data_in != data_out:
                    log_mismatch_error(self.logger, f"reg_val[{hex(csr)}]", data_in, data_out)
                    self.passed = False

            elif test == "debug_ic_cache":
                ifu_ic_debug_rd_data_in = item_inp.ifu_ic_debug_rd_data
                ifu_ic_debug_rd_data_out = item_out.ifu_ic_debug_rd_data

                if ifu_ic_debug_rd_data_in != ifu_ic_debug_rd_data_out:
                    log_mismatch_error(
                        self.logger, "read_data", ifu_ic_debug_rd_data_in, ifu_ic_debug_rd_data_out
                    )
                    self.passed = False

            elif test == "debug_csrs_access":
                csr = item_inp.csr_addr
                reg_val_i = item_inp.exu_i0_result_x
                reg_val_o = item_out.dec_csr_rddata_d

                dbg_csrs = [csrs.DICAD0, csrs.DICAD0H, csrs.DICAWICS, csrs.DPC, csrs.DCSR]
                for c in dbg_csrs:
                    if c == csr:
                        reg_val_i = c.out(reg_val_i)
                        break
                if reg_val_i != reg_val_o:
                    log_mismatch_error(self.logger, f"reg_val[{hex(csr)}]", reg_val_i, reg_val_o)
                    self.passed = False

            elif test == "meicidpl":
                reg_val_i = item_inp.exu_i0_result_x
                reg_val_o = item_out.dec_csr_rddata_d
                reg_val_i = csrs.MEICIDPL.out(reg_val_i)
                if reg_val_i != reg_val_o:
                    log_mismatch_error(self.logger, f"reg_val[{hex(csr)}]", reg_val_i, reg_val_o)
                    self.passed = False

            elif test == "recovery_gpr_access":
                if getattr(self, "unmatched_read", None) is None:
                    self.unmatched_read = {}
                if getattr(self, "unmatched_write", None) is None:
                    self.unmatched_write = {}
                if item_inp.gpr_addr not in self.unmatched_read:
                    if item_inp.gpr_addr not in self.unmatched_write:
                        self.unmatched_write[item_inp.gpr_addr] = []
                    self.unmatched_write[item_inp.gpr_addr].append(item_inp.gpr_data)
                else:
                    if item_inp.gpr_data != self.unmatched_read[item_inp.gpr_addr][0]:
                        log_mismatch_error(
                            self.logger,
                            f"gp_reg_val[{hex(item_inp.gpr_addr)}]",
                            item_inp.gpr_data,
                            self.unmatched_read[item_inp.gpr_addr][0]
                        )
                        self.passed = False
                    self.unmatched_read[item_inp.gpr_addr] = self.unmatched_read[item_inp.gpr_addr][1:]
                    if len(self.unmatched_read[item_inp.gpr_addr]) == 0:
                        del self.unmatched_read[item_inp.gpr_addr]
                if item_out.gpr_addr not in self.unmatched_write:
                    if item_out.gpr_addr not in self.unmatched_read:
                        self.unmatched_read[item_out.gpr_addr] = []
                    self.unmatched_read[item_out.gpr_addr].append(item_out.gpr_data)
                else:
                    if item_out.gpr_data != self.unmatched_write[item_out.gpr_addr][0]:
                        log_mismatch_error(
                            self.logger,
                            f"gp_reg_val[{hex(item_out.gpr_addr)}]",
                            item_out.gpr_data,
                            self.unmatched_write[item_out.gpr_addr][0]
                        )
                        self.passed = False
                    self.unmatched_write[item_out.gpr_addr] = self.unmatched_write[item_out.gpr_addr][1:]
                    if len(self.unmatched_write[item_out.gpr_addr]) == 0:
                        del self.unmatched_write[item_out.gpr_addr]

    def final_phase(self):
        if not self.passed:
            self.logger.critical("{} reports a failure".format(type(self)))
            assert False


class CsrRecoveryScoreboard(uvm_component):
    """
    A scoreboard for CSR recovery interface
    """

    def __init__(self, name, parent):
        super().__init__(name, parent)
        self.passed = False
        self.csrs_wr_state = dict()
        self.csrs_rd_f_state = dict()
        self.csrs_rd_b_state = dict()

    def build_phase(self):
        self.fifo_inp = uvm_tlm_analysis_fifo("fifo_inp", self)
        self.fifo_out = uvm_tlm_analysis_fifo("fifo_out", self)
        self.port_inp = uvm_get_port("port_inp", self)
        self.port_out = uvm_get_port("port_out", self)

    def connect_phase(self):
        self.port_inp.connect(self.fifo_inp.get_export)
        self.port_out.connect(self.fifo_out.get_export)

    def check_phase(self):  # noqa: C901

        # CSR writes
        while True:
            got_inp, item_inp = self.port_inp.try_get()
            if not got_inp:
                break

            if item_inp.csr_oper == "wr_front":
                self.csrs_wr_state[item_inp.csr_addr] = item_inp.csr_data
            elif item_inp.csr_oper == "wr_back":
                self.csrs_wr_state[item_inp.csr_addr] = item_inp.csr_data
            else:
                assert False, item_inp.oper

        # CSR reads
        while True:
            got_out, item_out = self.port_out.try_get()
            if not got_out:
                break

            if item_out.csr_oper == "rd_front":
                self.csrs_rd_f_state[item_out.csr_addr] = item_out.csr_data
            elif item_out.csr_oper == "rd_back":
                if item_out.csr_addr != 0: # 0 is not a valid CSR. But it is an artifact of bus monitor operation
                    self.csrs_rd_b_state[item_out.csr_addr] = item_out.csr_data
            else:
                assert False, item_inp.oper

        # DEBUG
        keys = sorted(list(self.csrs_wr_state.keys()))
        for k, v in [(k, self.csrs_wr_state[k]) for k in keys]:
            self.logger.debug(f"W : 0x{k:03X}: 0x{v:08X}")

        keys = sorted(list(self.csrs_rd_f_state.keys()))
        for k, v in [(k, self.csrs_rd_f_state[k]) for k in keys]:
            self.logger.debug(f"Rf: 0x{k:03X}: 0x{v:08X}")

        keys = sorted(list(self.csrs_rd_b_state.keys()))
        for k, v in [(k, self.csrs_rd_b_state[k]) for k in keys]:
            self.logger.debug(f"Rb: 0x{k:03X}: 0x{v:08X}")

        # Compare states
        self.passed = True

        keys = set(self.csrs_rd_f_state.keys()) | set(self.csrs_rd_b_state.keys())
        keys = sorted(list(keys))
        for k in keys:
            vf = self.csrs_rd_f_state.get(k, None)
            vb = self.csrs_rd_b_state.get(k, None)

            vf_str = f"0x{vf:08X}" if vf is not None else "none"
            vb_str = f"0x{vb:08X}" if vb is not None else "none"

            if vf != vb:
                self.logger.error(f"CSR mismatch! 0x{k:03X}, frontdoor:{vf_str}, backdoor:{vb_str}")
                self.passed = False

    def final_phase(self):
        if not self.passed:
            self.logger.critical("{} reports a failure".format(type(self)))
            assert False

# ==============================================================================


class DecSequence(uvm_sequence):

    def __init__(self, name, ops=None):
        super().__init__(name)

    async def body(self):
        count = ConfigDB().get(None, "", "TEST_ITERATIONS")
        test = ConfigDB().get(None, "", "TEST")

        for _ in range(count):
            item = DecInputItem()
            item.randomize(test)

            await self.start_item(item)
            await self.finish_item(item)


class DecTmrGprRecoverySequence(uvm_sequence):
    def __init__(self, name, mode):
        super().__init__(name)
        assert mode in ["retrieve", "restore"], mode
        self.mode = mode

    async def body(self):
        count = 2 # 2 iterations
        for _ in range(count):
            gpr_wr = list(range(1, 32))
            random.shuffle(gpr_wr)

            gpr_data = {addr: random.randrange(1 << 32) for addr in gpr_wr}
            for addr in gpr_wr:
                item = DecInputItem(
                    gpr_addr = addr,
                    gpr_data = gpr_data[addr],
                    gpr_oper = "wr_front" if self.mode == "retrieve" else "wr_back",
                )
                await self.start_item(item)
                await self.finish_item(item)

            # Read CSRs back but in different order
            gpr_rd = list(range(1, 32))
            random.shuffle(gpr_rd)

            for addr in gpr_rd:
                item = DecInputItem(
                    gpr_addr = addr,
                    gpr_oper = "rd_back" if self.mode == "retrieve" else "rd_front",
                )
                await self.start_item(item)
                await self.finish_item(item)


class DecTmrCsrRecoverySequence(uvm_sequence):
    """
    TMR CSR recovery interface test sequence. In "retrieve" mode writes CSRs
    normally, in "restore" mode writes them through backdoor. After write,
    it reads CSR content both through front and backdoor interfaces.
    """
    def __init__(self, name, mode):
        super().__init__(name)
        assert mode in ["retrieve", "restore"], mode
        self.mode = mode

    async def body(self):
        count = 2 # 2 iterations
        for _ in range(count):

            # Get shuffled CSR list and write them
            csrs_wr = list(DecInputItem.CSRS)
            random.shuffle(csrs_wr)

            csr_data = {addr: random.randrange(1 << 32) for addr in csrs_wr}

            for addr in csrs_wr:
                item = DecInputItem(
                    csr_addr = addr,
                    csr_data = csr_data[addr],
                    csr_oper = "wr_front" if self.mode == "retrieve" else "wr_back",
                )
                await self.start_item(item)
                await self.finish_item(item)

            # Read the CSRs back through backdoor
            csrs_rd = list(DecInputItem.CSRS)
            random.shuffle(csrs_rd)

            for addr in csrs_rd:
                item = DecInputItem(
                    csr_addr = addr,
                    csr_oper = "rd_back",
                )
                await self.start_item(item)
                await self.finish_item(item)

            # Read the CSRs back through frontdoor
            csrs_rd = list(DecInputItem.CSRS)
            random.shuffle(csrs_rd)

            for addr in csrs_rd:
                item = DecInputItem(
                    csr_addr = addr,
                    csr_oper = "rd_front",
                )
                await self.start_item(item)
                await self.finish_item(item)

# ==============================================================================


class BaseEnv(uvm_env):
    """
    Base PyUVM test environment
    """

    def build_phase(self):
        # Config
        ConfigDB().set(None, "*", "TEST_CLK_PERIOD", 1)
        ConfigDB().set(None, "*", "TEST_ITERATIONS", 5000)

        # Sequencers
        self.dec_seqr = uvm_sequencer("dec_seqr", self)

        # Driver
        self.dec_drv = DecDriver("dec_drv", self, dut=cocotb.top)

        # Monitors
        self.inp_mon = DecInputMonitor("inp_mon", self, dut=cocotb.top)
        self.out_mon = DecOutputMonitor("out_mon", self, dut=cocotb.top)

        # Scoreboard
        test = ConfigDB().get(self.get_parent(), "", "TEST")
        if test == "recovery_csr_access":
            self.scoreboard = CsrRecoveryScoreboard("scoreboard", self)
        else:
            self.scoreboard = DecScoreboard("scoreboard", self)

    def connect_phase(self):
        self.dec_drv.seq_item_port.connect(self.dec_seqr.seq_item_export)

        self.inp_mon.ap.connect(self.scoreboard.fifo_inp.analysis_export)
        self.out_mon.ap.connect(self.scoreboard.fifo_out.analysis_export)


# ==============================================================================


class BaseTest(uvm_test):
    """
    Base test for the module
    """

    def __init__(self, name, parent, env_class=BaseEnv):
        super().__init__(name, parent)
        self.env_class = env_class

        # Synchronize pyuvm logging level with cocotb logging level. Unclear
        # why it does not happen automatically.
        level = logging.getLevelName(os.environ.get("COCOTB_LOG_LEVEL", "INFO"))
        uvm_report_object.set_default_logging_level(level)

    def build_phase(self):
        self.env = self.env_class("env", self)

    def start_clock(self, name):
        period = ConfigDB().get(None, "", "TEST_CLK_PERIOD")
        sig = getattr(cocotb.top, name)
        clock = Clock(sig, period, units="ns")
        cocotb.start_soon(clock.start(start_high=False))

    async def enter_debug_mode(self):
        cocotb.top.dbg_halt_req.value = 1
        await ClockCycles(cocotb.top.clk, 2)
        cocotb.top.dbg_halt_req.value = 0
        if not cocotb.top.o_debug_mode_status.value:
            await RisingEdge(cocotb.top.o_debug_mode_status)

    async def do_reset(self):
        cocotb.top.rst_l.value = 0
        await ClockCycles(cocotb.top.clk, 2)
        await FallingEdge(cocotb.top.clk)
        cocotb.top.rst_l.value = 1

    async def run_phase(self):
        test = ConfigDB().get(self, "", "TEST")
        self.raise_objection()

        # Start clocks
        self.start_clock("clk")
        self.start_clock("active_clk")
        self.start_clock("free_clk")
        self.start_clock("free_l2clk")

        # Enable run after reset
        cocotb.top.mpc_reset_run_req.value = 1
        # Drive status indicators of non-included modules
        cocotb.top.lsu_idle_any.value = 1
        cocotb.top.ifu_miss_state_idle.value = 1

        cocotb.top.lsu_fastint_stall_any.value = 0
        cocotb.top.rst_vec.value = 0
        cocotb.top.nmi_int.value = 0
        cocotb.top.nmi_vec.value = 0
        cocotb.top.i_cpu_halt_req.value = 0
        cocotb.top.i_cpu_run_req.value = 0
        cocotb.top.core_id.value = 0
        cocotb.top.mpc_debug_halt_req.value = 0
        cocotb.top.mpc_debug_run_req.value = 0
        cocotb.top.exu_pmu_i0_br_misp.value = 0
        cocotb.top.exu_pmu_i0_br_ataken.value = 0
        cocotb.top.exu_pmu_i0_pc4.value = 0
        cocotb.top.lsu_nonblock_load_valid_m.value = 0
        cocotb.top.lsu_nonblock_load_tag_m.value = 0
        cocotb.top.lsu_nonblock_load_inv_r.value = 0
        cocotb.top.lsu_nonblock_load_inv_tag_r.value = 0
        cocotb.top.lsu_nonblock_load_data_valid.value = 0
        cocotb.top.lsu_nonblock_load_data_error.value = 0
        cocotb.top.lsu_nonblock_load_data_tag.value = 0
        cocotb.top.lsu_nonblock_load_data.value = 0
        cocotb.top.lsu_pmu_bus_trxn.value = 0
        cocotb.top.lsu_pmu_bus_misaligned.value = 0
        cocotb.top.lsu_pmu_bus_error.value = 0
        cocotb.top.lsu_pmu_bus_busy.value = 0
        cocotb.top.lsu_pmu_misaligned_m.value = 0
        cocotb.top.lsu_pmu_load_external_m.value = 0
        cocotb.top.lsu_pmu_store_external_m.value = 0
        cocotb.top.dma_pmu_dccm_read.value = 0
        cocotb.top.dma_pmu_dccm_write.value = 0
        cocotb.top.dma_pmu_any_read.value = 0
        cocotb.top.dma_pmu_any_write.value = 0
        cocotb.top.lsu_fir_addr.value = 0
        cocotb.top.lsu_fir_error.value = 0
        cocotb.top.ifu_pmu_instr_aligned.value = 0
        cocotb.top.ifu_pmu_fetch_stall.value = 0
        cocotb.top.ifu_pmu_ic_miss.value = 0
        cocotb.top.ifu_pmu_ic_hit.value = 0
        cocotb.top.ifu_pmu_bus_error.value = 0
        cocotb.top.ifu_pmu_bus_busy.value = 0
        cocotb.top.ifu_pmu_bus_trxn.value = 0
        cocotb.top.ifu_ic_error_start.value = 0
        cocotb.top.ifu_iccm_rd_ecc_single_err.value = 0
        cocotb.top.lsu_trigger_match_m.value = 0
        cocotb.top.dbg_cmd_valid.value = 0
        cocotb.top.dbg_cmd_write.value = 0
        cocotb.top.dbg_cmd_type.value = 0
        cocotb.top.dbg_cmd_addr.value = 0
        cocotb.top.dbg_cmd_wrdata.value = 0
        cocotb.top.ifu_i0_icaf.value = 0
        cocotb.top.ifu_i0_icaf_type.value = 0
        cocotb.top.ifu_i0_icaf_second.value = 0
        cocotb.top.ifu_i0_dbecc.value = 0
        cocotb.top.ifu_i0_bp_index.value = 0
        cocotb.top.ifu_i0_bp_fghr.value = 0
        cocotb.top.ifu_i0_bp_btag.value = 0
        cocotb.top.ifu_i0_fa_index.value = 0
        cocotb.top.lsu_single_ecc_error_incr.value = 0
        cocotb.top.lsu_imprecise_error_load_any.value = 0
        cocotb.top.lsu_imprecise_error_store_any.value = 0
        cocotb.top.lsu_imprecise_error_addr_any.value = 0
        cocotb.top.exu_div_result.value = 0
        cocotb.top.exu_div_wren.value = 0
        cocotb.top.exu_csr_rs1_x.value = 0
        cocotb.top.lsu_result_m.value = 0
        cocotb.top.lsu_result_corr_r.value = 0
        cocotb.top.lsu_load_stall_any.value = 0
        cocotb.top.lsu_store_stall_any.value = 0
        cocotb.top.dma_dccm_stall_any.value = 0
        cocotb.top.dma_iccm_stall_any.value = 0
        cocotb.top.iccm_dma_sb_error.value = 0
        cocotb.top.exu_flush_final.value = 0
        cocotb.top.exu_npc_r.value = 0
        cocotb.top.exu_i0_result_x.value = 0
        cocotb.top.ifu_i0_valid.value = 0
        cocotb.top.ifu_i0_instr.value = 0
        cocotb.top.ifu_i0_pc.value = 0
        cocotb.top.ifu_i0_pc4.value = 0
        cocotb.top.exu_i0_pc_x.value = 0
        cocotb.top.mexintpend.value = 0
        cocotb.top.timer_int.value = 0
        cocotb.top.soft_int.value = 0
        cocotb.top.pic_claimid.value = 0
        cocotb.top.pic_pl.value = 0
        cocotb.top.mhwakeup.value = 0
        cocotb.top.ifu_ic_debug_rd_data.value = 0
        cocotb.top.ifu_ic_debug_rd_data_valid.value = 0
        cocotb.top.dbg_halt_req.value = 0
        cocotb.top.dbg_resume_req.value = 0
        cocotb.top.exu_i0_br_hist_r.value = 0
        cocotb.top.exu_i0_br_error_r.value = 0
        cocotb.top.exu_i0_br_start_error_r.value = 0
        cocotb.top.exu_i0_br_valid_r.value = 0
        cocotb.top.exu_i0_br_mp_r.value = 0
        cocotb.top.exu_i0_br_middle_r.value = 0
        cocotb.top.exu_i0_br_way_r.value = 0
        cocotb.top.ifu_i0_cinst.value = 0
        cocotb.top.recovery_gpr_en.value = 0
        cocotb.top.recovery_gpr_wen.value = 0
        cocotb.top.recovery_gpr_wraddr.value = 0
        cocotb.top.recovery_gpr_wrdata.value = 0
        cocotb.top.recovery_gpr_rdaddr.value = 0
        cocotb.top.recovery_gpr_rddata.value = 0
        cocotb.top.recovery_csr_en.value = 0
        cocotb.top.recovery_csr_wen.value = 0
        cocotb.top.recovery_csr_wraddr.value = 0
        cocotb.top.recovery_csr_wrdata.value = 0
        cocotb.top.recovery_csr_rdaddr.value = 0

        # Issue reset
        await self.do_reset()

        # Wait some cycles
        await ClockCycles(cocotb.top.clk, 2)

        if test == "debug_csrs_access":
            await self.enter_debug_mode()

        # Run the actual test
        await self.run()

        # Wait some cycles
        await ClockCycles(cocotb.top.clk, 10)

        self.drop_objection()

    async def run(self):
        raise NotImplementedError()
