# Copyright (c) 2023 Antmicro
# SPDX-License-Identifier: Apache-2.0

import math
import os
import random
import struct
import copy

import pyuvm
from cocotb.binary import BinaryValue
from cocotb.types import Array, Range
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


class TlInputItem(uvm_sequence_item):
    """
    Trigger Logic output data
    """

    def __init__(self, data=0, tdata=None, match=0):
        super().__init__("TlOutputItem")

        self.match = match
        self.data = data
        self.tdata = [None] * 4
        if tdata is not None:
            for i in range(4):
                self.tdata[i] = tdata[i]

    def randomize(self):
        data = ""
        for i in range(31):  # Sic. Last bit of PC is always 0
            data += random.choice(["0", "1"])
        data += "0"

        self.data = int(data, 2)

        self.match = 0
        for i in range(4):
            matching = random.choice([False, True])
            trigger = self.random_trigger(data, matching)
            self.match |= trigger["match"] << i
            self.tdata[i] = trigger["tdata"]

    def random_trigger(self, data, matching):
        """
        Creates a trigger packet for data vector.

        It can be precised if the packet will be matching or not.
        """

        # Select determines if we match against the PC or opcode,
        # TL in TLU does the first thing
        match = ""
        tdata = ""

        # Generate the matched part
        length = 0
        if matching:
            length = random.randrange(32 + 1)
            if length > 0:
                tdata += data[:length]
        else:
            length = random.randrange(1, 32)
            for i in range(length):
                tdata += random.choice(["0", "1"])

            # Assure a mismatch
            i = random.randrange(length)
            b = "1" if data[i] == "0" else "0"
            tdata = tdata[:i] + b + tdata[i + 1 :]

        # Generate the mask
        length = 32 - length
        if length == 0:
            match = "0"  # Do full match
        else:
            match = "1"
            tdata += "0" + "1" * (length - 1)

        return {"match": int(match, 2), "tdata": int(tdata, 2)}


class TlOutputItem(uvm_sequence_item):
    """
    Trigger Logic output data
    """

    def __init__(self, matches):
        super().__init__("TlOutputItem")

        self.matches = matches


# ==============================================================================


class TlDriver(uvm_driver):
    """
    Trigger Logic driver
    """

    def __init__(self, *args, **kwargs):
        self.dut = kwargs["dut"]
        del kwargs["dut"]
        super().__init__(*args, **kwargs)

    async def run_phase(self):
        period = ConfigDB().get(None, "", "TEST_CLK_PERIOD")

        while True:
            it = await self.seq_item_port.get_next_item()

            if isinstance(it, TlInputItem):
                self.dut.dec_i0_pc_d.value = it.data >> 1

                for i in range(4):
                    self.dut.tdata[i].value = it.tdata[i]

                self.dut.match.value = it.match

                self.dut.select.value = 0b0000
                self.dut.store.value = 0b1111
                self.dut.load.value = 0b1111
                self.dut.execute.value = 0b1111
                self.dut.m.value = 0b1111

                # Wait for monitors to read the values
                await Timer(period, "ns")
            else:
                raise RuntimeError("Unknown item '{}'".format(type(it)))

            self.seq_item_port.item_done()


class TlInputMonitor(uvm_component):
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
        period = ConfigDB().get(None, "", "TEST_CLK_PERIOD")

        while True:
            # Wait for the driver to set the input signals
            await Timer(period, "ns")

            data = int(self.dut.dec_i0_pc_d.value)
            tdata = [None] * 4

            for i in range(4):
                tdata[i] = int(self.dut.tdata[i].value)

            match = int(self.dut.match.value)

            self.ap.write(TlInputItem(data, tdata, match))


class TlOutputMonitor(uvm_component):
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
        period = ConfigDB().get(None, "", "TEST_CLK_PERIOD")

        while True:
            # Wait for the driver to set the input signals
            await Timer(period, "ns")

            matches = int(self.dut.dec_i0_trigger_match_d.value)

            self.ap.write(TlOutputItem(matches))


# ==============================================================================


class TlScoreboard(uvm_component):
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

            # Change outputs to str and reproduce what TL does
            res = 0
            match = item_inp.match
            data = f"{item_inp.data:031b}"
            for i in range(4):
                tdata = f"{item_inp.tdata[i] >> 1:031b}"
                if match & (1 << i):
                    length = tdata.rindex("0")
                    res |= (tdata[:length] == data[:length]) << i
                else:
                    res |= (tdata == data) << i

            if item_out.matches != res:
                self.logger.error(f"Expected {res:04b} got {item_out.matches:04b}")
                self.passed = False

    def final_phase(self):
        if not self.passed:
            self.logger.critical("{} reports a failure".format(type(self)))
            assert False


# ==============================================================================


class TlSequence(uvm_sequence):
    """
    Base sequence of randomized 32-bit A and B operands along with operators
    picked randomly from the allowed set
    """

    def __init__(self, name, ops=None):
        super().__init__(name)

    async def body(self):
        count = ConfigDB().get(None, "", "TEST_ITERATIONS")

        for i in range(count):
            item = TlInputItem()
            item.randomize()

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
        self.tl_seqr = uvm_sequencer("tl_seqr", self)

        # Driver
        self.tl_drv = TlDriver("tl_drv", self, dut=cocotb.top)

        # Monitors
        self.inp_mon = TlInputMonitor("inp_mon", self, dut=cocotb.top)
        self.out_mon = TlOutputMonitor("out_mon", self, dut=cocotb.top)

        # Scoreboard
        self.scoreboard = TlScoreboard("scoreboard", self)

    def connect_phase(self):
        self.tl_drv.seq_item_port.connect(self.tl_seqr.seq_item_export)

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
