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


class MulInputItem(uvm_sequence_item):
    """
    Multipiler input data
    """

    def __init__(self, op, a, b, low=0):
        super().__init__("MulInputItem")
        self.op = op
        self.a = a
        self.b = b
        self.low = low


class MulOutputItem(uvm_sequence_item):
    """
    Multiplier output data
    """

    def __init__(self, out):
        super().__init__("MulOutputItem")
        self.out = out


# ==============================================================================


class MulDriver(uvm_driver):
    """
    Multiplier input driver
    """

    def __init__(self, *args, **kwargs):
        self.dut = kwargs["dut"]
        del kwargs["dut"]
        super().__init__(*args, **kwargs)

    async def run_phase(self):
        while True:
            it = await self.seq_item_port.get_next_item()

            if isinstance(it, MulInputItem):
                # Wait for rising edge
                await RisingEdge(self.dut.clk)
                self.dut.mul_p_valid.value = 1

                # Operands
                self.dut.rs1_in.value = abs(it.a)
                self.dut.rs2_in.value = abs(it.b)
                self.dut.mul_p_rs1_sign.value = 0  # For now assume positive
                self.dut.mul_p_rs2_sign.value = 0

                # Control
                self.dut.mul_p_low.value = it.low

                # Deassert valid after one cycle
                await RisingEdge(self.dut.clk)
                self.dut.mul_p_valid.value = 0

            else:
                raise RuntimeError("Unknown item '{}'".format(type(it)))

            self.seq_item_port.item_done()


class MulInputMonitor(uvm_component):
    """
    Monitor for Multiplier inputs
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
            if self.dut.mul_p_valid.value:
                # Sample control signals and operands
                a = int(self.dut.rs1_in.value)
                b = int(self.dut.rs2_in.value)
                low = int(self.dut.mul_p_low.value)

                # Decode operation
                op = None

                # Write item
                self.ap.write(
                    MulInputItem(
                        op=op,
                        a=a,
                        b=b,
                        low=low,
                    )
                )


class MulOutputMonitor(uvm_component):
    """
    Monitor for multiplier outputs
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
            if self.dut.mul_p_valid.value:
                # Wait 1 cycle
                await RisingEdge(self.dut.clk)

                # Sample result & write the item
                result = int(self.dut.result_x.value)
                self.ap.write(MulOutputItem(out=result))


# ==============================================================================


class MulScoreboard(uvm_component):
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

            # Predict the result
            res = item_inp.a * item_inp.b
            if not item_inp.low:
                res >>= 32
            res &= 0xFFFFFFFF

            self.logger.debug(
                "{} * {} ({}) == {}".format(
                    item_inp.a,
                    item_inp.b,
                    "lo" if item_inp.low else "hi",
                    item_out.out,
                )
            )

            if item_out.out != res:
                self.logger.error(
                    "{} * {} ({}) != {} (should be {})".format(
                        item_inp.a, item_inp.b, "lo" if item_inp.low else "hi", item_out.out, res
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
            self.ops = ["mul"]
        else:
            self.ops = ops

    async def body(self):
        count = ConfigDB().get(None, "", "TEST_ITERATIONS")

        for i in range(count):
            a = random.randrange(1, 1 << 32)
            b = random.randrange(1, 1 << 32)
            op = random.choice(self.ops)

            if op == "mul":
                low = random.choice([0, 1])

            item = MulInputItem(op, a, b, low=low)

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
        self.mul_seqr = uvm_sequencer("mul_seqr", self)

        # Driver
        self.mul_drv = MulDriver("mul_drv", self, dut=cocotb.top)

        # Monitors
        self.inp_mon = MulInputMonitor("inp_mon", self, dut=cocotb.top)
        self.out_mon = MulOutputMonitor("out_mon", self, dut=cocotb.top)

        # Scoreboard
        self.scoreboard = MulScoreboard("scoreboard", self)

    def connect_phase(self):
        self.mul_drv.seq_item_port.connect(self.mul_seqr.seq_item_export)

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

        # Wait some cycles
        await ClockCycles(cocotb.top.clk, 2)

        # Run the actual test
        await self.run()

        # Wait some cycles
        await ClockCycles(cocotb.top.clk, 10)

        self.drop_objection()

    async def run(self):
        raise NotImplementedError()
