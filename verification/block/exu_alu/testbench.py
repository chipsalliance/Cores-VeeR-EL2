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
                self.dut.ap_clz.value = 0
                self.dut.ap_ctz.value = 0
                self.dut.ap_cpop.value = 0
                self.dut.ap_sext_b.value = 0
                self.dut.ap_sext_h.value = 0
                self.dut.ap_min.value = 0
                self.dut.ap_max.value = 0
                self.dut.ap_rol.value = 0
                self.dut.ap_ror.value = 0
                self.dut.ap_grev.value = 0
                self.dut.ap_gorc.value = 0
                self.dut.ap_zbb.value = 0

                # Zbs
                self.dut.ap_bset.value = 0
                self.dut.ap_bclr.value = 0
                self.dut.ap_binv.value = 0
                self.dut.ap_bext.value = 0

                # Zbp
                self.dut.ap_pack.value = 0
                self.dut.ap_packu.value = 0
                self.dut.ap_packh.value = 0

                # Zba
                self.dut.ap_sh1add.value = 0
                self.dut.ap_sh2add.value = 0
                self.dut.ap_sh3add.value = 0
                self.dut.ap_zba.value = 0

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
                ap_add = int(self.dut.ap_add.value)
                ap_sub = int(self.dut.ap_sub.value)
                ap_and = int(self.dut.ap_land.value)
                ap_or = int(self.dut.ap_lor.value)
                ap_xor = int(self.dut.ap_lxor.value)

                vec = (ap_add, ap_sub, ap_and, ap_or, ap_xor)
                op = None

                if vec == (1, 0, 0, 0, 0):
                    op = "add"
                if vec == (0, 1, 0, 0, 0):
                    op = "sub"
                if vec == (0, 0, 1, 0, 0):
                    op = "and"
                if vec == (0, 0, 0, 1, 0):
                    op = "or"
                if vec == (0, 0, 0, 0, 1):
                    op = "xor"

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

            if item_inp.op == "add":
                result = (item_inp.a + item_inp.b) & 0xFFFFFFFF
            elif item_inp.op == "sub":
                result = (item_inp.a - item_inp.b) & 0xFFFFFFFF
            elif item_inp.op == "and":
                result = item_inp.a & item_inp.b
            elif item_inp.op == "or":
                result = item_inp.a | item_inp.b
            elif item_inp.op == "xor":
                result = item_inp.a ^ item_inp.b
            else:
                self.logger.error("Unknown ALU operation '{}'".format(item_in.op))
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
            if item_inp.op in ["add", "sub", "and", "or", "xor"]:
                if item_out.out != result:
                    self.logger.error(
                        "{} {} {} != {} (should be {})".format(
                            item_inp.a, item_inp.op, item_inp.b, item_out.out, result
                        )
                    )
                    self.passed = False
            else:
                assert False

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
            a = random.randrange(1, 1 << 32)
            b = random.randrange(1, 1 << 32)
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
