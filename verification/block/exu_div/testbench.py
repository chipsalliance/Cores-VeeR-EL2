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


class DivInputItem(uvm_sequence_item):
    """
    Divider input data
    """

    def __init__(self, op, num, den, unsign=1):
        super().__init__("DivInputItem")
        self.op = op
        self.num = num
        self.den = den
        self.unsign = unsign


class DivOutputItem(uvm_sequence_item):
    """
    Divider output data
    """

    def __init__(self, out):
        super().__init__("DivOutputItem")
        self.out = out


# ==============================================================================


class DivDriver(uvm_driver):
    """
    Divider module driver
    """

    def __init__(self, *args, **kwargs):
        self.dut = kwargs["dut"]
        del kwargs["dut"]
        super().__init__(*args, **kwargs)

    async def run_phase(self):
        while True:
            it = await self.seq_item_port.get_next_item()

            if isinstance(it, DivInputItem):
                # Wait for rising edge
                await RisingEdge(self.dut.clk)
                self.dut.dp_valid.value = 1
                self.dut.dp_unsign.value = it.unsign
                self.dut.dp_rem.value = it.op == "rem"
                self.dut.dividend.value = it.num
                self.dut.divisor.value = it.den

                # Deassert valid, wait for finish
                for i in range(100):
                    await RisingEdge(self.dut.clk)
                    self.dut.dp_valid.value = 0

                    if self.dut.finish_dly.value:
                        break
                else:
                    raise RuntimeError("Timeout")

            else:
                raise RuntimeError("Unknown item '{}'".format(type(it)))

            self.seq_item_port.item_done()


class DivInputMonitor(uvm_component):
    """
    Monitor for divider inputs
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
            if self.dut.dp_valid.value:
                # Sample control signals and operands
                num = int(self.dut.dividend.value)
                den = int(self.dut.divisor.value)
                unsign = int(self.dut.dp_unsign.value)

                # Decode operation
                op = "rem" if self.dut.dp_rem.value else "div"

                # Write item
                self.ap.write(DivInputItem(op=op, num=num, den=den, unsign=unsign))


class DivOutputMonitor(uvm_component):
    """
    Monitor for divider outputs
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

            # We got a valid output
            if self.dut.finish_dly.value:
                # Sample result & write the item
                result = int(self.dut.out.value)
                self.ap.write(DivOutputItem(out=result))


# ==============================================================================


class DivScoreboard(uvm_component):
    """
    Divider scoreboard
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
            div = item_inp.num // item_inp.den
            rem = item_inp.num - (div * item_inp.den)

            self.logger.debug(
                "{} {} {} == {}".format(
                    item_inp.num,
                    item_inp.op,
                    item_inp.den,
                    item_out.out,
                )
            )

            # Check
            if (item_inp.op == "div" and item_out.out != div) or (
                item_inp.op == "rem" and item_out.out != rem
            ):
                result = div if item_inp.op == "div" else rem

                self.logger.error(
                    "{} {} {} != {} ({})".format(
                        item_inp.num, item_inp.op, item_inp.den, result, item_out.out
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
            self.ops = ["div", "rem"]
        else:
            self.ops = ops

    async def body(self):
        count = ConfigDB().get(None, "", "TEST_ITERATIONS")

        for i in range(count):
            num = random.randrange(1, 1 << 32)
            den = random.randrange(1, 1 << 16)  # Make dividends from smaller range
            op = random.choice(self.ops)

            item = DivInputItem(op, num, den)

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
        self.div_seqr = uvm_sequencer("div_seqr", self)

        # Driver
        self.div_drv = DivDriver("div_drv", self, dut=cocotb.top)

        # Monitors
        self.inp_mon = DivInputMonitor("inp_mon", self, dut=cocotb.top)
        self.out_mon = DivOutputMonitor("out_mon", self, dut=cocotb.top)

        # Scoreboard
        self.scoreboard = DivScoreboard("scoreboard", self)

    def connect_phase(self):
        self.div_drv.seq_item_port.connect(self.div_seqr.seq_item_export)

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
