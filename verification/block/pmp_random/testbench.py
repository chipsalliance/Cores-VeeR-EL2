# Copyright (c) 2023 Antmicro
# SPDX-License-Identifier: Apache-2.0

import copy
import math
import os
import random
import struct

import pyuvm
from cocotb.binary import BinaryValue
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
from cocotb.types import Array, Range
from pyuvm import *

# ==============================================================================

NONE = 0x0
READ = 0x1
WRITE = 0x2
EXEC = 0x4

# ==============================================================================


class InputItem(uvm_sequence_item):
    """
    PMP input item
    """

    RANGE = 16

    def __init__(self, cfg=0, entry=0, pmp_addr=0, chan_addr=0, chan_type=0, chan=0, chan_err=0):
        super().__init__("InputItem")

        self.cfg = cfg
        self.entry = entry
        self.pmp_addr = pmp_addr
        self.chan = chan
        self.chan_addr = chan_addr
        self.chan_type = chan_type
        self.chan_err = chan_err

    def randomize(self):
        """
        Randomize cfg and addresses
        """
        self.cfg = random.randint(0, 0xFF)
        self.entry = random.randint(0, 63)
        self.pmp_addr = random.randint(0, 0xFFFFFFFF)
        self.chan = random.randint(0, 2)
        self.chan_addr = random.randint(0, 0xFFFFFFFF)
        self.chan_type = random.randint(0, 3)


# ==============================================================================


class PMPWriteDriver(uvm_driver):
    """
    PMP CSR write port driver driver
    """

    def __init__(self, *args, **kwargs):
        self.dut = kwargs["dut"]
        del kwargs["dut"]
        super().__init__(*args, **kwargs)

    async def run_phase(self):

        while True:
            it = await self.seq_item_port.get_next_item()

            if isinstance(it, InputItem):
                await RisingEdge(self.dut.clk)
                self.dut.pmp_pmpcfg[it.entry].value = it.cfg
                self.dut.pmp_pmpaddr[it.entry].value = it.pmp_addr
                self.dut.pmp_chan_addr[it.chan].value = it.chan_addr
                self.dut.pmp_chan_type[it.chan].value = it.chan_type

            else:
                raise RuntimeError("Unknown item '{}'".format(type(it)))

            self.seq_item_port.item_done()


# ==============================================================================


class WriteMonitor(uvm_component):
    """
    Monitor for CSR write inputs
    """

    def __init__(self, *args, **kwargs):
        self.dut = kwargs["dut"]
        del kwargs["dut"]
        super().__init__(*args, **kwargs)

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    async def run_phase(self):

        while True:
            await RisingEdge(self.dut.clk)
            cfg = self.dut.pmp_pmpcfg.value
            pmp_addr = self.dut.pmp_pmpaddr.value
            chan_addr = self.dut.pmp_chan_addr.value
            chan_type = self.dut.pmp_chan_type
            item = InputItem(cfg=cfg, pmp_addr=pmp_addr, chan_addr=chan_addr, chan_type=chan_type)
            self.ap.write(item)


class ReadMonitor(uvm_component):
    """
    Monitor for CSR read inputs
    """

    def __init__(self, *args, **kwargs):
        self.dut = kwargs["dut"]
        del kwargs["dut"]
        super().__init__(*args, **kwargs)

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    async def run_phase(self):

        while True:
            await RisingEdge(self.dut.clk)
            chan_err = self.dut.pmp_chan_err
            item = InputItem(chan_err=chan_err)
            self.ap.write(item)


# ==============================================================================


class Scoreboard(uvm_component):
    """
    PMP dec ctl scoreboard
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
        self.passed = None

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

            # we should never hit PMP error in this test
            if int(item_inp.chan_err) != 0:
                self.logger.error("Got PMP Error")
                self.passed = False

    def final_phase(self):
        if not self.passed:
            self.logger.critical("{} reports a failure".format(type(self)))
            assert False


# ==============================================================================


class BaseEnv(uvm_env):
    """
    Base PyUVM test environment
    """

    def build_phase(self):
        # Config
        ConfigDB().set(None, "*", "TEST_CLK_PERIOD", 1)
        ConfigDB().set(None, "*", "TEST_ITERATIONS", 200)

        # Sequencers
        self.pmp_wr_seqr = uvm_sequencer("pmp_wr_seqr", self)

        # Drivers
        self.pmp_wr_drv = PMPWriteDriver("pmp_wr_drv", self, dut=cocotb.top)

        # Monitors
        self.wr_mon = WriteMonitor("wr_mon", self, dut=cocotb.top)
        self.rd_mon = ReadMonitor("rd_mon", self, dut=cocotb.top)

        # Scoreboard
        self.scoreboard = Scoreboard("scoreboard", self)

    def connect_phase(self):
        self.pmp_wr_drv.seq_item_port.connect(self.pmp_wr_seqr.seq_item_export)

        self.wr_mon.ap.connect(self.scoreboard.fifo_inp.analysis_export)
        self.rd_mon.ap.connect(self.scoreboard.fifo_out.analysis_export)


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
