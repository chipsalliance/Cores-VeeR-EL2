#
# Copyright (c) 2026 Antmicro
# SPDX-License-Identifier: Apache-2.0

import os
from collections.abc import Iterable

from cocotb.binary import BinaryValue
from cocotb.clock import Clock
from cocotb.handle import NonHierarchyIndexableObject
from cocotb.triggers import ClockCycles, FallingEdge, ReadOnly, RisingEdge
from pyuvm import *

# ==============================================================================


# FIXME: Sync with makefile somehow
MuBiFalse = 0b01
MuBiTrue = 0b10

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
        clock = self.uut.clk

        while True:
            it = await self.seq_item_port.get_next_item()

            await RisingEdge(clock)
            for k, v in it.signals.items():
                assert hasattr(self.uut, k), k
                s = getattr(self.uut, k)
                if len(s._sub_handles) > 0:
                    for sig, val in zip(s, v):
                        sig.value = val
                else:
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
        self.uut = kwargs["uut"]
        self.signals = kwargs["signals"]

        del kwargs["uut"]
        del kwargs["signals"]

        super().__init__(*args, **kwargs)

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    async def run_phase(self):
        clock = self.uut.clk

        while True:
            # Sample data on falling edge as the monitor samples both async.
            # reset (driven on rising edge) and signals affected by it.
            await FallingEdge(clock)
            await ReadOnly()

            signals = dict()
            for k in self.signals:
                assert hasattr(self.uut, k), k
                s = getattr(self.uut, k)
                signals[k] = s.value

            self.ap.write(MonitorItem(signals))


# ==============================================================================


class BaseScoreboard(uvm_component):

    def build_phase(self):
        self.passed = None
        self.fifo = uvm_tlm_analysis_fifo("fifo", self)
        self.port = uvm_get_port("port", self)

    def connect_phase(self):
        self.port.connect(self.fifo.get_export)

    def check_phase(self):
        rst_state = [0, 0, 0]
        core_active_i = [MuBiFalse, MuBiFalse, MuBiFalse]
        core_active_o = [MuBiFalse, MuBiFalse, MuBiFalse]

        while self.port.can_get():
            _, it = self.port.try_get()
            self.logger.debug(str(it))

            # Initialize the pass flag
            if self.passed is None:
                self.passed = True

            # Shift reset state
            rst_state = [it.signals["rst_l"]] + rst_state[:-1]

            # Reset output
            if not rst_state[0]:
                core_active_o = [MuBiFalse, MuBiFalse, MuBiFalse]

            # Latch output
            if rst_state == [1, 1, 0]:
                core_active_o = it.signals["core_active_o"]
                if core_active_o != core_active_i:
                    self.logger.error(
                        f"Output vs. input error, {core_active_o} vs. {core_active_i}"
                    )
                    self.passed = False

            # Compare core_active state
            if core_active_o != it.signals["core_active_o"]:
                self.logger.error("Latched state changed while it shouldn't")
                self.passed = False

            # Store current core_active_i state for the next cycle
            core_active_i = it.signals["core_active_i"]

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
        self.bus_drv = BusDriver("bus_drv", self, uut=cocotb.top)
        # Monitors
        self.bus_mon = BusMonitor(
            "bus_mon",
            self,
            uut=cocotb.top,
            signals=[
                "rst_l",
                "core_active_i",
                "core_active_o",
            ],
        )

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

    def __init__(self, name, parent, seq_class, scb_class=BaseScoreboard):
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
        cocotb.top.scan_mode.value = 0
        cocotb.top.rst_l.value = 0

        cocotb.top.core_active_i[0].value = MuBiFalse
        cocotb.top.core_active_i[1].value = MuBiFalse
        cocotb.top.core_active_i[2].value = MuBiFalse

        # Start clock
        self.start_clock("clk")
        await ClockCycles(cocotb.top.clk, 2)

        # Run the sequece
        await self.seq.start()
        await ClockCycles(cocotb.top.clk, 2)
        self.drop_objection()

    async def run(self):
        raise NotImplementedError()
