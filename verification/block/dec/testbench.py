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
from cocotb.triggers import ClockCycles, FallingEdge, RisingEdge
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


def log_mismatch_error(logger, name, expected, got):
    logger.error(f"{name} {hex(expected)} != {hex(got)} (should be {hex(expected)})")


csr_list = [getattr(csrs, mod) for mod in dir(csrs) if isinstance(getattr(csrs, mod), csrs.CSR)]
CSR_OPCODE = 0b1110011


class Funct3(IntEnum):
    CSRRW = 0b001
    CSRRS = 0b010
    CSRRC = 0b011
    CSRRWI = 0b101
    CSRRSI = 0b110
    CSRRCI = 0b111


def csr_access_inst(csr, rs1, funct3, rd, opcode):
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
        return csr_access_inst(self.csr, 0, self.funct3, 0, CSR_OPCODE)


@dataclass
class WriteCSRInst:
    csr: int = 0
    funct3: Funct3 = Funct3.CSRRW

    def encode(self):
        return csr_access_inst(self.csr, 0, self.funct3, 0, CSR_OPCODE)


def randint(width=32):
    return random.randint(0, 2 ** (width) - 1)


class DecInputItem(uvm_sequence_item):
    """
    Trigger Logic input data
    """

    def __init__(
        self,
        pic_claimid=0,
        dec_csr_wrdata_r=0,
        ifu_ic_debug_rd_data=0,
        csrw_instr=0,
        csrr_instr=0,
        csr_addr=0,
        mtdata1=0,
        mtdata2=0,
        mtsel=0,
    ):
        super().__init__("DecInputItem")
        self.dec_csr_wrdata_r = dec_csr_wrdata_r
        self.csr_addr = csr_addr
        self.csrw_instr = csrw_instr
        self.csrr_instr = csrr_instr
        self.pic_claimid = pic_claimid
        self.ifu_ic_debug_rd_data = ifu_ic_debug_rd_data
        self.mtdata1 = mtdata1
        self.mtdata2 = mtdata2
        self.mtsel = mtsel

    def randomize(self, test):
        if test == "mtdata":
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
            self.csr_addr = random.choice(
                [
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
                ]
            )
            self.dec_csr_wrdata_r = randint()
            self.csrw_instr = WriteCSRInst(self.csr_addr).encode()
            self.csrr_instr = ReadCSRInst(self.csr_addr).encode()
        elif test == "debug_ic_cache":
            self.ifu_ic_debug_rd_data = randint(71)


class DecOutputItem(uvm_sequence_item):
    """
    Trigger Logic output data
    """

    def __init__(
        self,
        csrr_instr=0,
        dec_csr_wrdata_r=0,
        dec_csr_rddata_d=0,
        trigger_pkt_any=0,
        ifu_ic_debug_rd_data=0,
    ):
        super().__init__("DecOutputItem")
        self.csrr_instr = csrr_instr
        self.dec_csr_wrdata_r = dec_csr_wrdata_r
        self.dec_csr_rddata_d = dec_csr_rddata_d
        self.trigger_pkt_any = trigger_pkt_any
        self.ifu_ic_debug_rd_data = ifu_ic_debug_rd_data


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

    async def run_phase(self):
        while True:
            it = await self.seq_item_port.get_next_item()
            if isinstance(it, DecInputItem):
                test = ConfigDB().get(self, "", "TEST")
                if test == "mtdata":
                    await self.write_csr(WriteCSRInst(csrs.MTSEL).encode(), it.mtsel)
                    await self.write_csr(WriteCSRInst(csrs.MTDATA1).encode(), it.mtdata1)
                    await self.write_csr(WriteCSRInst(csrs.MTDATA2).encode(), it.mtdata2)
                    for _ in range(4):
                        await RisingEdge(self.dut.clk)
                elif test in ["csr_access"]:
                    # Write CSR
                    await self.write_csr(it.csrw_instr, it.dec_csr_wrdata_r)
                    for _ in range(2):
                        await RisingEdge(self.dut.clk)
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
            if test == "mtdata":
                await RisingEdge(self.dut.ifu_i0_valid)
                for _ in range(2):
                    await RisingEdge(self.dut.clk)
                mtsel = int(self.dut.exu_i0_result_x.value)
                await RisingEdge(self.dut.ifu_i0_valid)
                for _ in range(2):
                    await RisingEdge(self.dut.clk)
                mtdata1 = int(self.dut.exu_i0_result_x.value)
                await RisingEdge(self.dut.ifu_i0_valid)
                for _ in range(2):
                    await RisingEdge(self.dut.clk)
                mtdata2 = int(self.dut.exu_i0_result_x.value)
                self.ap.write(DecInputItem(mtdata1=mtdata1, mtdata2=mtdata2, mtsel=mtsel))
            elif test in ["csr_access"]:
                # Wait for CSR write
                await RisingEdge(self.dut.ifu_i0_valid)
                csrw_instr = int(self.dut.ifu_i0_instr.value)
                for _ in range(2):
                    await RisingEdge(self.dut.clk)
                dec_csr_wrdata_r = int(self.dut.exu_i0_result_x.value)
                # Wait for CSR read
                await RisingEdge(self.dut.ifu_i0_valid)
                csrr_instr = int(self.dut.ifu_i0_instr.value)
                self.ap.write(
                    DecInputItem(
                        csrw_instr=csrw_instr,
                        csrr_instr=csrr_instr,
                        dec_csr_wrdata_r=dec_csr_wrdata_r,
                    )
                )
            elif test == "debug_ic_cache":
                # Wait for CSR write
                await RisingEdge(self.dut.ifu_ic_debug_rd_data_valid)
                ic_debug_rd_data = int(self.dut.ifu_ic_debug_rd_data.value)
                self.ap.write(DecInputItem(ifu_ic_debug_rd_data=ic_debug_rd_data))
                # Wait for CSR reads
                for _ in range(4):
                    await RisingEdge(self.dut.clk)


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
            if test == "mtdata":
                # Wait for CSR writes
                for _ in range(3):
                    await RisingEdge(self.dut.ifu_i0_valid)
                # Wait for the outputs
                for _ in range(4):
                    await RisingEdge(self.dut.clk)
                trigger_pkt_any = int(self.dut.trigger_pkt_any.value)
                self.ap.write(DecOutputItem(trigger_pkt_any=trigger_pkt_any))
            elif test in ["csr_access"]:
                # Wait for CSR write
                await RisingEdge(self.dut.ifu_i0_valid)
                for _ in range(2):
                    await RisingEdge(self.dut.clk)
                dec_csr_wrdata_r = int(self.dut.dec_csr_wrdata_r.value)
                # Wait for CSR read
                await RisingEdge(self.dut.ifu_i0_valid)
                csrr_instr = int(self.dut.ifu_i0_instr.value)
                await RisingEdge(self.dut.clk)
                dec_csr_rddata_d = int(self.dut.dec_csr_rddata_d.value)
                self.ap.write(
                    DecOutputItem(
                        csrr_instr=csrr_instr,
                        dec_csr_wrdata_r=dec_csr_wrdata_r,
                        dec_csr_rddata_d=dec_csr_rddata_d,
                    )
                )
            elif test == "debug_ic_cache":
                await RisingEdge(self.dut.ifu_ic_debug_rd_data_valid)
                for _ in range(3):
                    await RisingEdge(self.dut.clk)
                dicad0 = int(self.dut.dec_csr_rddata_d.value)
                for _ in range(2):
                    await RisingEdge(self.dut.clk)
                dicad0h = int(self.dut.dec_csr_rddata_d.value)
                for _ in range(2):
                    await RisingEdge(self.dut.clk)
                dicad1 = int(self.dut.dec_csr_rddata_d.value)
                ifu_ic_debug_rd_data = dicad0 | (dicad0h << 32) | (dicad1 << 64)
                self.ap.write(DecOutputItem(ifu_ic_debug_rd_data=ifu_ic_debug_rd_data))


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
                break

            if self.passed is None:
                self.passed = True

            test = ConfigDB().get(self, "", "TEST")
            if test == "mtdata":
                pkt_any_mask = 0x3FFFFFFFFF
                tdata2_mask = 0xFFFFFFFF
                flags_mask = 0x3F
                flags_shift = 32

                mtsel = item_inp.mtsel
                pkt_any_shift = mtsel * 38

                mtdata1_i = item_inp.mtdata1
                mtdata2_i = item_inp.mtdata2
                trigger_pkt_any = ((item_out.trigger_pkt_any) >> pkt_any_shift) & pkt_any_mask

                select_i = get_bit(mtdata1_i, 19)
                match_i = get_bit(mtdata1_i, 7)
                store_i = get_bit(mtdata1_i, 1)
                load_i = get_bit(mtdata1_i, 0) & ~get_bit(mtdata1_i, 19)
                execute_i = get_bit(mtdata1_i, 2) & ~get_bit(mtdata1_i, 19)
                m_i = get_bit(mtdata1_i, 6)

                flags_o = (trigger_pkt_any >> flags_shift) & flags_mask

                select_o = get_bit(flags_o, 5)
                match_o = get_bit(flags_o, 4)
                store_o = get_bit(flags_o, 3)
                load_o = get_bit(flags_o, 2)
                execute_o = get_bit(flags_o, 1)
                m_o = get_bit(flags_o, 0)

                mtdata2_o = trigger_pkt_any & tdata2_mask

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
                data_w0 = item_inp.dec_csr_wrdata_r
                data_w1 = item_inp.dec_csr_wrdata_r

                if data_w0 != data_w1:
                    self.logger.error(
                        "Sampled from 'dec_csr_wrdata_r': {} != {} (should be {})".format(
                            hex(data_w0), hex(data_w1), hex(data_w0)
                        )
                    )
                    self.passed = False

                data_in = data_w0
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

    async def do_reset(self):
        cocotb.top.rst_l.value = 0
        await ClockCycles(cocotb.top.clk, 2)
        await FallingEdge(cocotb.top.clk)
        cocotb.top.rst_l.value = 1

    async def run_phase(self):
        self.raise_objection()

        # Start clocks
        self.start_clock("clk")
        self.start_clock("active_clk")
        self.start_clock("free_clk")
        self.start_clock("free_l2clk")

        # Enable run after reset
        cocotb.top.mpc_reset_run_req.value = 1

        # Issue reset
        await self.do_reset()

        # Wait some cycles
        await ClockCycles(cocotb.top.clk, 2)

        # Run the actual test
        await self.run()

        # Wait some cycles
        await ClockCycles(cocotb.top.clk, 10)

        self.drop_objection()

    async def run(self):
        raise NotImplementedError()
