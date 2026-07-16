#
# Copyright (c) 2026 Antmicro
# SPDX-License-Identifier: Apache-2.0

import os

from cocotb.binary import BinaryValue
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, FallingEdge, RisingEdge
from pyuvm import *

# ==============================================================================

# FIXME: Sync with makefile somehow
MuBiFalse = 0b01
MuBiTrue  = 0b10

# ==============================================================================


class DriverItem(uvm_sequence_item):
    def __init__(self, signals=None):
        super().__init__("DriverItem")
        self.signals = dict() if signals is None else signals

    def __str__(self):
        return str(self.signals)


class BusDriver(uvm_driver):

    def __init__(self, *args, **kwargs):
        self.uut = kwargs["uut"]
        del kwargs["uut"]
        super().__init__(*args, **kwargs)

    async def run_phase(self):
        clock = self.uut.clk_i

        while True:
            it = await self.seq_item_port.get_next_item()

            await RisingEdge(clock)
            for k, v in it.signals.items():
                assert hasattr(self.uut, k), k
                s = getattr(self.uut, k)
                s.value = v

            self.seq_item_port.item_done()

# ==============================================================================


class MonitorItem(uvm_sequence_item):
    def __init__(self, signals):
        super().__init__("MonitorItem")
        self.signals = signals

    def __str__(self):
        return str(self.signals)


class BusMonitor(uvm_component):

    def __init__(self, *args, **kwargs):
        self.uut     = kwargs["uut"]
        self.signals = kwargs["signals"]

        del kwargs["uut"]
        del kwargs["signals"]

        super().__init__(*args, **kwargs)
    
    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    async def run_phase(self):
        clock = self.uut.clk_i

        while True:
            await RisingEdge(clock)

            signals = dict()
            for k in self.signals:
                assert hasattr(self.uut, k), k
                s = getattr(self.uut, k)
                signals[k] = s.value
            
            self.ap.write(MonitorItem(signals))

# ==============================================================================

class BaseScoreboard(uvm_component):

    def build_phase(self):
        self.passed = False
        self.fifo = uvm_tlm_analysis_fifo("fifo", self)
        self.port = uvm_get_port("port", self)

    def connect_phase(self):
        self.port.connect(self.fifo.get_export)

    def check_phase(self):
        raise NotImplementedError()

    def final_phase(self):
        if not self.passed:
            self.logger.critical("{} reports a failure".format(type(self)))
            assert False

# ==============================================================================

class BaseEnv(uvm_env):
    """
    Base PyUVM test environment
    """

    def __init__(self, name, parent, scb_class):
        super().__init__(name, parent)
        self.scb_class = scb_class

    def build_phase(self):

        ConfigDB().set(None, "*", "TEST_CLK_PERIOD", 1)
        ConfigDB().set(None, "*", "TEST_ITERATIONS", 100)

        # Sequencers
        self.bus_seqr = uvm_sequencer("bus_seqr", self)
        # Driver
        self.bus_drv = BusDriver("bus_drv", self, uut = cocotb.top)
        # Monitors
        self.bus_mon = BusMonitor("bus_mon", self, uut = cocotb.top, signals = [
            "in_a", "in_b", "in_c",
            "en_a", "en_b", "en_c",
            "out",
            "fault_a", "fault_b", "fault_c",
        ])

        # Scoreboard(s)
        self.scoreboard = None
        if self.scb_class is not None:
            self.scoreboard = self.scb_class("scoreboard", self)

        ConfigDB().set(None, "*", "SEQR", self.bus_seqr)

    def connect_phase(self):
        self.bus_drv.seq_item_port.connect(self.bus_seqr.seq_item_export)
        if self.scoreboard:
            self.bus_mon.ap.connect(self.scoreboard.fifo.analysis_export)

# ==============================================================================


class BaseTest(uvm_test):
    """
    Base PyUVM test for the module
    """

    def __init__(self, name, parent, seq_class, scb_class=None):
        super().__init__(name, parent)
        self.seq_class = seq_class
        self.scb_class = scb_class

        # Synchronize pyuvm logging level with cocotb logging level. Unclear
        # why it does not happen automatically.
        level = logging.getLevelName(os.environ.get("COCOTB_LOG_LEVEL", "INFO"))
        uvm_report_object.set_default_logging_level(level)

    def build_phase(self):
        self.env = BaseEnv("env", self, self.scb_class)

    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = self.seq_class.create("stimulus")

    def start_clock(self, name):
        period = ConfigDB().get(None, "", "TEST_CLK_PERIOD")
        sig = getattr(cocotb.top, name)
        clock = Clock(sig, period, units="ns")
        cocotb.start_soon(clock.start(start_high=False))

    async def run_phase(self):
        self.raise_objection()

        # Initialize signals
        cocotb.top.in_a.value = 0
        cocotb.top.in_b.value = 0
        cocotb.top.in_c.value = 0

        cocotb.top.en_a.value = MuBiFalse
        cocotb.top.en_b.value = MuBiFalse
        cocotb.top.en_c.value = MuBiFalse

        # Start clock
        self.start_clock("clk_i")
        await ClockCycles(cocotb.top.clk_i, 2)

        # Run the sequece
        await self.seq.start()
        await ClockCycles(cocotb.top.clk_i, 2)
        self.drop_objection()

    async def run(self):
        raise NotImplementedError()
