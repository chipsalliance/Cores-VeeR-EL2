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

PMPCFG = 0x3A0
PMPADDR0 = 0x3B0
PMPADDR16 = 0x3C0
PMPADDR32 = 0x3D0
PMPADDR48 = 0x3E0

# ==============================================================================


class InputItem(uvm_sequence_item):
    """
    PMP input item
    """

    RANGE = 16

    def __init__(self, addr=0, data=0):
        super().__init__("InputItem")

        self.addr = addr
        self.data = data

    def randomize(self):
        """
        Randomize data and address offset
        """
        self.addr += random.randint(0, self.RANGE - 1)
        self.data = random.randint(0, 0xFFFFFFFF)


# ==============================================================================


class CsrWriteDriver(uvm_driver):
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

                # Write
                await RisingEdge(self.dut.clk)
                self.dut.dec_csr_wen_r.value = 1
                self.dut.dec_csr_wraddr_r.value = it.addr
                self.dut.dec_csr_wrdata_r.value = it.data
                await RisingEdge(self.dut.clk)
                self.dut.dec_csr_wen_r.value = 0

            else:
                raise RuntimeError("Unknown item '{}'".format(type(it)))

            self.seq_item_port.item_done()


class CsrReadDriver(uvm_driver):
    """
    PMP CSR read port driver driver
    """

    def __init__(self, *args, **kwargs):
        self.dut = kwargs["dut"]
        del kwargs["dut"]
        super().__init__(*args, **kwargs)

    async def run_phase(self):

        while True:
            it = await self.seq_item_port.get_next_item()

            if isinstance(it, InputItem):

                # Read
                await RisingEdge(self.dut.clk)
                self.dut.dec_csr_rdaddr_d.value = it.addr

                await RisingEdge(self.dut.clk)
                self.dut.dec_csr_rdaddr_d.value = 0

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

            # A write to a CSR
            await RisingEdge(self.dut.clk)
            if self.dut.dec_csr_wen_r.value:
                addr = int(self.dut.dec_csr_wraddr_r)
                data = int(self.dut.dec_csr_wrdata_r)

                item = InputItem(addr, data)
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

            # A read from a CSR
            await RisingEdge(self.dut.clk)
            addr = int(self.dut.dec_csr_rdaddr_d) & 0x3F0
            if addr in [PMPCFG, PMPADDR0, PMPADDR16, PMPADDR32, PMPADDR48]:
                addr = int(self.dut.dec_csr_rdaddr_d)
                data = int(self.dut.dec_csr_rddata_d)

                item = InputItem(addr, data)
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

            # Compare addresses and data
            if item_inp.addr != item_out.addr or item_inp.data != item_out.data:
                istr = f"{item_inp.addr:04X}:{item_inp.data:08X}"
                ostr = f"{item_out.addr:04X}:{item_out.data:08X}"
                self.logger.error(f"Mismatch {istr} vs. {ostr}")
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
        ConfigDB().set(None, "*", "TEST_ITERATIONS", 5000)

        # Sequencers
        self.pmp_wr_seqr = uvm_sequencer("pmp_wr_seqr", self)
        self.pmp_rd_seqr = uvm_sequencer("pmp_rd_seqr", self)

        # Drivers
        self.pmp_wr_drv = CsrWriteDriver("pmp_wr_drv", self, dut=cocotb.top)
        self.pmp_rd_drv = CsrReadDriver("pmp_rd_drv", self, dut=cocotb.top)

        # Monitors
        self.wr_mon = WriteMonitor("wr_mon", self, dut=cocotb.top)
        self.rd_mon = ReadMonitor("rd_mon", self, dut=cocotb.top)

        # Scoreboard
        self.scoreboard = Scoreboard("scoreboard", self)

    def connect_phase(self):
        self.pmp_wr_drv.seq_item_port.connect(self.pmp_wr_seqr.seq_item_export)
        self.pmp_rd_drv.seq_item_port.connect(self.pmp_rd_seqr.seq_item_export)

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
        self.start_clock("csr_wr_clk")
        self.start_clock("free_l2clk")

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
