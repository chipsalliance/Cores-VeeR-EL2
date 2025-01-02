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


class InputItem(uvm_sequence_item):
    """
    PMP input item
    """

    def __init__(self, dec_csr_wraddr_r=0, dec_csr_wrdata_r=0):
        super().__init__("InputItem")

        self.dec_csr_wraddr_r = dec_csr_wraddr_r
        self.dec_csr_wrdata_r = dec_csr_wrdata_r

    def randomize(self):

        # CSR
        dec_csr_wrdata_r = ""

        for _ in range(31):
            dec_csr_wrdata_r += random.choice(["0", "1"])

        self.dec_csr_wrdata_r = int(dec_csr_wrdata_r, 2)


class OutputItem(uvm_sequence_item):

    def __init__(self):
        super().__init__("OutputItem")


# ==============================================================================
PMPADDR0 = 0x3B0
PMPADDR16 = 0x3C0
PMPADDR32 = 0x3D0
PMPADDR48 = 0x3E0


class Driver(uvm_driver):
    """
    PMP dec driver
    """

    def __init__(self, *args, **kwargs):
        self.dut = kwargs["dut"]
        del kwargs["dut"]
        super().__init__(*args, **kwargs)

    async def run_phase(self):

        while True:
            it = await self.seq_item_port.get_next_item()

            if isinstance(it, InputItem):
                # write PMPADDR0
                self.dut.dec_csr_wen_r_mod.value = 0
                await RisingEdge(self.dut.clk)
                self.dut.dec_csr_wen_r_mod.value = 1
                self.dut.dec_csr_wraddr_r.value = PMPADDR0
                self.dut.dec_csr_wrdata_r.value = it.dec_csr_wrdata_r
                await RisingEdge(self.dut.clk)
                # write PMPADDR16
                self.dut.dec_csr_wen_r_mod.value = 0
                await RisingEdge(self.dut.clk)
                self.dut.dec_csr_wen_r_mod.value = 1
                self.dut.dec_csr_wraddr_r.value = PMPADDR16
                self.dut.dec_csr_wrdata_r.value = it.dec_csr_wrdata_r
                await RisingEdge(self.dut.clk)
                # write PMPADDR32
                self.dut.dec_csr_wen_r_mod.value = 0
                await RisingEdge(self.dut.clk)
                self.dut.dec_csr_wen_r_mod.value = 1
                self.dut.dec_csr_wraddr_r.value = PMPADDR32
                self.dut.dec_csr_wrdata_r.value = it.dec_csr_wrdata_r
                await RisingEdge(self.dut.clk)
                # write PMPADDR48
                self.dut.dec_csr_wen_r_mod.value = 0
                await RisingEdge(self.dut.clk)
                self.dut.dec_csr_wen_r_mod.value = 1
                self.dut.dec_csr_wraddr_r.value = PMPADDR48
                self.dut.dec_csr_wrdata_r.value = it.dec_csr_wrdata_r
                await RisingEdge(self.dut.clk)
                # give two more cycles so that output monitor can catch the data on the outputs
                await RisingEdge(self.dut.clk)
                await RisingEdge(self.dut.clk)
            else:
                raise RuntimeError("Unknown item '{}'".format(type(it)))

            self.seq_item_port.item_done()


class InputMonitor(uvm_component):
    """
    Monitor for inputs
    """

    def __init__(self, *args, **kwargs):
        self.dut = kwargs["dut"]
        del kwargs["dut"]
        super().__init__(*args, **kwargs)

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    async def run_phase(self):

        while True:
            await RisingEdge(self.dut.dec_csr_wen_r_mod)
            await RisingEdge(self.dut.dec_csr_wen_r_mod)
            for _ in range(4):
                await RisingEdge(self.dut.clk)


class OutputMonitor(uvm_component):
    """
    Monitor for outputs
    """

    def __init__(self, *args, **kwargs):
        self.dut = kwargs["dut"]
        del kwargs["dut"]
        super().__init__(*args, **kwargs)

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    async def run_phase(self):

        while True:
            for _ in range(2):
                await RisingEdge(self.dut.clk)

            self.ap.write(OutputItem())


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
        self.passed = True

    def final_phase(self):
        if not self.passed:
            self.logger.critical("{} reports a failure".format(type(self)))
            assert False


# ==============================================================================


class Sequence(uvm_sequence):

    def __init__(self, name, ops=None):
        super().__init__(name)

    async def body(self):
        count = ConfigDB().get(None, "", "TEST_ITERATIONS")

        for i in range(count):
            item = InputItem()
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
        ConfigDB().set(None, "*", "TEST_ITERATIONS", 1)

        # Sequencers
        self.pmp_seqr = uvm_sequencer("pmp_seqr", self)

        # Driver
        self.pmp_drv = Driver("pmp_drv", self, dut=cocotb.top)

        # Monitors
        self.inp_mon = InputMonitor("inp_mon", self, dut=cocotb.top)
        self.out_mon = OutputMonitor("out_mon", self, dut=cocotb.top)

        # Scoreboard
        self.scoreboard = Scoreboard("scoreboard", self)

    def connect_phase(self):
        self.pmp_drv.seq_item_port.connect(self.pmp_seqr.seq_item_export)

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
