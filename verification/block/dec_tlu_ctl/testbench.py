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


class TlInputItem(uvm_sequence_item):
    """
    Trigger Logic output data
    """

    def __init__(self, pic_claimid=0, dec_csr_wrdata_r=0):
        super().__init__("TlOutputItem")

        self.pic_claimid = pic_claimid
        self.dec_csr_wrdata_r = dec_csr_wrdata_r

    def randomize(self):

        pic_claimid = ""
        # CSR
        dec_csr_wrdata_r = ""
        for _ in range(8):
            pic_claimid += random.choice(["0", "1"])

        for _ in range(22):
            dec_csr_wrdata_r += random.choice(["0", "1"])

        self.pic_claimid = int(pic_claimid, 2)
        self.dec_csr_wrdata_r = int(dec_csr_wrdata_r, 2) << 10


class TlOutputItem(uvm_sequence_item):
    """
    Trigger Logic output data
    """

    def __init__(self, dec_tlu_meihap):
        super().__init__("TlOutputItem")
        self.dec_tlu_meihap = dec_tlu_meihap


# ==============================================================================
MEICPCT = 0xBCA
MEIVT = 0xBC8


class TlDriver(uvm_driver):
    """
    Trigger Logic driver
    """

    def __init__(self, *args, **kwargs):
        self.dut = kwargs["dut"]
        del kwargs["dut"]
        super().__init__(*args, **kwargs)

    async def run_phase(self):

        while True:
            it = await self.seq_item_port.get_next_item()

            if isinstance(it, TlInputItem):
                # write MEIVT
                self.dut.dec_csr_wen_r.value = 0
                await RisingEdge(self.dut.clk)
                self.dut.dec_csr_wen_r.value = 1
                self.dut.dec_csr_wraddr_r.value = MEIVT
                self.dut.dec_csr_wrdata_r.value = it.dec_csr_wrdata_r
                await RisingEdge(self.dut.clk)
                self.dut.dec_csr_wen_r.value = 0
                # write pic_claimid
                await RisingEdge(self.dut.clk)
                self.dut.pic_claimid.value = it.pic_claimid
                self.dut.dec_csr_wen_r.value = 1
                self.dut.dec_csr_wraddr_r.value = MEICPCT
                await RisingEdge(self.dut.clk)
                self.dut.dec_csr_wen_r.value = 0
                # give two more cycles so that output monitor can catch the data on the outputs
                await RisingEdge(self.dut.clk)
                await RisingEdge(self.dut.clk)
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

        while True:
            # Wait for the driver to set the input signals
            await RisingEdge(self.dut.dec_csr_wen_r)
            await RisingEdge(self.dut.dec_csr_wen_r)
            # for _ in range(4):
            #    await RisingEdge(self.dut.clk)

            pic_claimid = int(self.dut.pic_claimid.value)
            meivt = int(self.dut.dec_csr_wrdata_r.value)

            self.ap.write(TlInputItem(pic_claimid, meivt))


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

        while True:
            # Wait for the driver to set the input signals and the data goes through
            await RisingEdge(self.dut.dec_csr_wen_r)
            await RisingEdge(self.dut.dec_csr_wen_r)
            for _ in range(2):
                await RisingEdge(self.dut.clk)

            dec_tlu_meihap = int(self.dut.dec_tlu_meihap.value) << 2
            self.ap.write(TlOutputItem(dec_tlu_meihap))


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

            sent_pic_claimid = item_inp.pic_claimid
            sent_meivt = item_inp.dec_csr_wrdata_r >> 12
            recv_pic_claimid = (item_out.dec_tlu_meihap >> 2) & 0xFF
            recv_meivt = item_out.dec_tlu_meihap >> 12

            if sent_pic_claimid != recv_pic_claimid:
                self.logger.error(
                    "pic_claimid {} != {} (should be {})".format(
                        sent_pic_claimid, recv_pic_claimid, sent_pic_claimid
                    )
                )
                self.passed = False

            if sent_meivt != recv_meivt:
                self.logger.error(
                    "meivt {} != {} (should be {})".format(sent_meivt, recv_meivt, sent_meivt)
                )
                self.passed = False

    def final_phase(self):
        if not self.passed:
            self.logger.critical("{} reports a failure".format(type(self)))
            assert False


# ==============================================================================


class TlSequence(uvm_sequence):

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
    Ba5e test for the module
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
