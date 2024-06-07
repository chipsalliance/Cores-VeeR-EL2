# Copyright (c) 2023 Antmicro
# SPDX-License-Identifier: Apache-2.0

import math
import os
import random
import struct

import pyuvm
from cocotb.clock import Clock
from cocotb.triggers import (
    ClockCycles,
    Event,
    FallingEdge,
    First,
    Lock,
    RisingEdge,
    Timer,
)
from pyuvm import *

# ==============================================================================


class AluInputItem(uvm_sequence_item):
    """
    ALU input data
    """

    def __init__(self, op, a, b, csr=0, pc=0):
        super().__init__("AluInputItem")
        self.op = op
        self.a = a
        self.b = b
        self.csr = csr
        self.pc = pc


class AluOutputItem(uvm_sequence_item):
    """
    ALU output data
    """

    def __init__(self, out):
        super().__init__("AluOutputItem")
        self.out = out


# ==============================================================================


class AluDriver(uvm_driver):
    """
    ALU input driver
    """

    def __init__(self, *args, **kwargs):
        self.dut = kwargs["dut"]
        del kwargs["dut"]
        super().__init__(*args, **kwargs)

    async def run_phase(self):
        while True:
            it = await self.seq_item_port.get_next_item()

            if isinstance(it, AluInputItem):
                # Wait for rising edge
                await RisingEdge(self.dut.clk)
                self.dut.valid_in.value = 1

                # Zbb
                self.dut.ap_clz.value = it.op in ["clz"]
                self.dut.ap_ctz.value = it.op in ["ctz"]
                self.dut.ap_cpop.value = it.op in ["cpop"]
                self.dut.ap_sext_b.value = it.op in ["sext_b"]
                self.dut.ap_sext_h.value = it.op in ["sext_h"]
                self.dut.ap_rol.value = it.op in ["rol"]
                self.dut.ap_ror.value = it.op in ["ror"]

                # Zbs
                self.dut.ap_bset.value = it.op in ["bset"]
                self.dut.ap_bclr.value = it.op in ["bclr"]
                self.dut.ap_binv.value = it.op in ["binv"]
                self.dut.ap_bext.value = it.op in ["bext"]

                # Zbp
                self.dut.ap_pack.value = it.op in ["pack"]
                self.dut.ap_packh.value = it.op in ["packh"]

                # Zba
                self.dut.ap_sh1add.value = it.op in ["sh1add"]
                self.dut.ap_sh2add.value = it.op in ["sh2add"]
                self.dut.ap_sh3add.value = it.op in ["sh3add"]
                # ap_zba has to be set to 1 to use sh??add instructions
                self.dut.ap_zba.value = it.op in ["sh1add", "sh2add", "sh3add"]

                # Arith
                self.dut.ap_add.value = it.op in ["add"]
                self.dut.ap_sub.value = it.op in ["sub"]
                self.dut.ap_land.value = it.op in ["and"]
                self.dut.ap_lor.value = it.op in ["or"]
                self.dut.ap_lxor.value = it.op in ["xor"]

                # Operands
                self.dut.a_in.value = it.a
                self.dut.b_in.value = it.b
                self.dut.csr_rddata_in.value = it.csr
                self.dut.pc_in.value = it.pc

                # Deassert valid after one cycle
                await RisingEdge(self.dut.clk)
                self.dut.valid_in.value = 0

            else:
                raise RuntimeError("Unknown item '{}'".format(type(it)))

            self.seq_item_port.item_done()


class AluInputMonitor(uvm_component):
    """
    Monitor for ALU inputs
    """

    def __init__(self, *args, **kwargs):
        self.dut = kwargs["dut"]
        del kwargs["dut"]
        super().__init__(*args, **kwargs)

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    async def run_phase(self):
        while True:
            # Act on rising edges
            await RisingEdge(self.dut.clk)

            # We got a valid input
            if self.dut.valid_in.value:
                # Sample control signals and operands
                a = int(self.dut.a_in.value)
                b = int(self.dut.b_in.value)

                # Decode operation
                op = None
                if int(self.dut.ap_add.value):
                    op = "add"
                elif int(self.dut.ap_sub.value):
                    op = "sub"
                elif int(self.dut.ap_land.value):
                    op = "and"
                elif int(self.dut.ap_lor.value):
                    op = "or"
                elif int(self.dut.ap_lxor.value):
                    op = "xor"
                elif int(self.dut.ap_clz.value):
                    op = "clz"
                elif int(self.dut.ap_ctz.value):
                    op = "ctz"
                elif int(self.dut.ap_cpop.value):
                    op = "cpop"
                elif int(self.dut.ap_sext_b.value):
                    op = "sext_b"
                elif int(self.dut.ap_sext_h.value):
                    op = "sext_h"
                elif int(self.dut.ap_rol.value):
                    op = "rol"
                elif int(self.dut.ap_ror.value):
                    op = "ror"
                elif int(self.dut.ap_bset.value):
                    op = "bset"
                elif int(self.dut.ap_bclr.value):
                    op = "bclr"
                elif int(self.dut.ap_binv.value):
                    op = "binv"
                elif int(self.dut.ap_bext.value):
                    op = "bext"
                elif int(self.dut.ap_pack.value):
                    op = "pack"
                elif int(self.dut.ap_packh.value):
                    op = "packh"
                elif int(self.dut.ap_sh1add.value):
                    op = "sh1add"
                elif int(self.dut.ap_sh2add.value):
                    op = "sh2add"
                elif int(self.dut.ap_sh3add.value):
                    op = "sh3add"

                # Write item
                self.ap.write(
                    AluInputItem(
                        op=op,
                        a=a,
                        b=b,
                    )
                )


class AluOutputMonitor(uvm_component):
    """
    Monitor for ALU outputs
    """

    def __init__(self, *args, **kwargs):
        self.dut = kwargs["dut"]
        del kwargs["dut"]
        super().__init__(*args, **kwargs)

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    async def run_phase(self):
        while True:
            # Act on rising edges
            await RisingEdge(self.dut.clk)

            # We got a valid input
            if self.dut.valid_in.value:
                # Wait 1 cycle
                await RisingEdge(self.dut.clk)

                # Sample result & write the item
                result = int(self.dut.result_ff.value)
                self.ap.write(AluOutputItem(out=result))


# ==============================================================================


class AluScoreboard(uvm_component):
    """
    Generic ALU scoreboard
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

    def check_phase(self):
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

            # Predict result
            result = None

            INT_MASK = 0xFFFFFFFF
            if item_inp.op == "add":
                result = (item_inp.a + item_inp.b) & INT_MASK
            elif item_inp.op == "sub":
                result = (item_inp.a - item_inp.b) & INT_MASK
            elif item_inp.op == "and":
                result = item_inp.a & item_inp.b
            elif item_inp.op == "or":
                result = item_inp.a | item_inp.b
            elif item_inp.op == "xor":
                result = item_inp.a ^ item_inp.b
            elif item_inp.op == "clz":
                result = next((i for i in range(32) if ((item_inp.a << i) & INT_MASK) >> 31), 32)
            elif item_inp.op == "ctz":
                result = next((i for i in range(32) if (item_inp.a >> i) & 1), 32)
            elif item_inp.op == "cpop":
                result = item_inp.a.bit_count()
            elif item_inp.op == "sext_b":
                last_byte = item_inp.a & 0xFF
                sign = (item_inp.a & 0x00000080) >> 7
                result = (0xFFFFFF00 * sign) | last_byte
            elif item_inp.op == "sext_h":
                last_2_bytes = item_inp.a & 0xFFFF
                sign = (item_inp.a & 0x00008000) >> 15
                result = (0xFFFF0000 * sign) | last_2_bytes
            elif item_inp.op == "rol":
                shamt = item_inp.b & 31
                result = (item_inp.a << shamt) & INT_MASK | (item_inp.a >> ((32 - shamt) & 31))
            elif item_inp.op == "ror":
                shamt = item_inp.b & 31
                result = (item_inp.a >> shamt) | (item_inp.a << ((32 - shamt) & 31)) & INT_MASK
            elif item_inp.op == "bset":
                result = item_inp.a | (1 << (item_inp.b & 31))
            elif item_inp.op == "bclr":
                result = item_inp.a & ~(1 << (item_inp.b & 31))
            elif item_inp.op == "binv":
                result = item_inp.a ^ (1 << (item_inp.b & 31))
            elif item_inp.op == "bext":
                result = 1 & (item_inp.a >> (item_inp.b & 31))
            elif item_inp.op == "pack":
                result = (((item_inp.a << 16) & INT_MASK) >> 16) | (item_inp.b << 16) & INT_MASK
            elif item_inp.op == "packh":
                result = (item_inp.a & 0xFF) | ((item_inp.b & 0xFF) << 8)
            elif item_inp.op in ["sh1add", "sh2add", "sh3add"]:
                shift = int(item_inp.op[2])
                result = ((item_inp.a << shift) + item_inp.b) & INT_MASK
            else:
                self.logger.error("Unknown ALU operation '{}'".format(item_inp.op))
                self.passed = False

            self.logger.debug(
                "{} {} {} == {}".format(
                    item_inp.a,
                    item_inp.op,
                    item_inp.b,
                    item_out.out,
                )
            )

            # Check result
            assert result is not None
            if item_out.out != result:
                self.logger.error(
                    "{} {} {} != {} (should be {})".format(
                        item_inp.a, item_inp.op, item_inp.b, item_out.out, result
                    )
                )
                self.passed = False

    def final_phase(self):
        if not self.passed:
            self.logger.critical("{} reports a failure".format(type(self)))
            assert False


# ==============================================================================


class BaseSequence(uvm_sequence):
    """
    Base sequence of randomized 32-bit A and B operands along with operators
    picked randomly from the allowed set
    """

    def __init__(self, name, ops=None):
        super().__init__(name)

        if ops is None:
            self.ops = ["add", "sub"]
        else:
            self.ops = ops

    async def body(self):
        count = ConfigDB().get(None, "", "TEST_ITERATIONS")

        for i in range(count):
            a = random.randrange(-(1 << 31), 1 << 31)
            b = random.randrange(-(1 << 31), 1 << 31)
            op = random.choice(self.ops)

            item = AluInputItem(op, a, b)

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
        ConfigDB().set(None, "*", "TEST_ITERATIONS", 50)

        # Sequencers
        self.alu_seqr = uvm_sequencer("alu_seqr", self)

        # Driver
        self.alu_drv = AluDriver("alu_drv", self, dut=cocotb.top)

        # Monitors
        self.inp_mon = AluInputMonitor("inp_mon", self, dut=cocotb.top)
        self.out_mon = AluOutputMonitor("out_mon", self, dut=cocotb.top)

        # Scoreboard
        self.scoreboard = AluScoreboard("scoreboard", self)

    def connect_phase(self):
        self.alu_drv.seq_item_port.connect(self.alu_seqr.seq_item_export)

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

        # Syncrhonize pyuvm logging level with cocotb logging level. Unclear
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

        # Issue reset
        await self.do_reset()

        # Set common signals
        cocotb.top.enable.value = 1

        # Wait some cycles
        await ClockCycles(cocotb.top.clk, 2)

        # Run the actual test
        await self.run()

        # Wait some cycles
        await ClockCycles(cocotb.top.clk, 10)

        self.drop_objection()

    async def run(self):
        raise NotImplementedError()
