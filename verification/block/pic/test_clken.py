# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

from copy import deepcopy

import cocotb
import pyuvm
from cocotb.result import SimTimeoutError
from cocotb.triggers import Edge, Lock, RisingEdge, Timer, with_timeout
from pyuvm import *
from testbench import BaseEnv, BaseTest, collect_signals

# =============================================================================


class ClockEnableItem(uvm_sequence_item):
    def __init__(self, clk_en, io_clk_en):
        super().__init__("ClockEnableItem")
        self.clk_en = clk_en
        self.io_clk_en = io_clk_en


class ClockStateItem(uvm_sequence_item):
    def __init__(self, state):
        super().__init__("ClockStateItem")
        self.state = deepcopy(state)


# =============================================================================


class ClkenDriver(uvm_driver):
    """
    A driver for clock gating override signals
    """

    SIGNALS = [
        "clk_override",
        "io_clk_override",
    ]

    def __init__(self, *args, **kwargs):
        uut = kwargs["uut"]
        del kwargs["uut"]

        super().__init__(*args, **kwargs)

        collect_signals(self.SIGNALS, uut, self)

    async def run_phase(self):
        while True:
            it = await self.seq_item_port.get_next_item()

            if isinstance(it, ClockEnableItem):
                self.clk_override.value = it.clk_en
                self.io_clk_override.value = it.io_clk_en
            else:
                raise RuntimeError("Unknown item '{}'".format(type(it)))

            self.seq_item_port.item_done()


class ClkenMonitor(uvm_component):
    """
    A monitor for clock gating override signals
    """

    SIGNALS = [
        "clk",
        "clk_override",
        "io_clk_override",
    ]

    def __init__(self, *args, **kwargs):
        uut = kwargs["uut"]
        del kwargs["uut"]

        super().__init__(*args, **kwargs)

        collect_signals(self.SIGNALS, uut, self)

        self.prev_clk_override = 0
        self.prev_io_clk_override = 0

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    async def run_phase(self):
        while True:
            # Sample control signals
            await RisingEdge(self.clk)
            clk_override = int(self.clk_override.value)
            io_clk_override = int(self.io_clk_override.value)

            if (
                self.prev_clk_override != clk_override
                or self.prev_io_clk_override != io_clk_override
            ):
                self.ap.write(ClockEnableItem(clk_override, io_clk_override))

                self.prev_clk_override = clk_override
                self.prev_io_clk_override = io_clk_override


# =============================================================================


class ClockMonitor(uvm_component):
    """
    A monitor for clock signal activity.

    The monitor spawns one task per clock signal. Each task waits either for a
    signal transition or a fixed time equal to twice the expected clock period
    (its actually important that the time is greater than half-period) If,
    during the waiting time, the task detects any signal transition
    (1->0, 0->1), then it marks the signal as an active clock. Otherwise, the
    signal is marked as inactive.

    The main task of the monitor periodically samples the state vector reported
    by monitoring tasks and sends a message through its analysis port. This is
    scheduled to happen periodically every 5 * the expected clock period. The
    scheduling is chosen arbitrarily.
    """

    SIGNALS = [
        "pic_raddr_c1_clk",
        "pic_data_c1_clk",
        "pic_pri_c1_clk",
        "pic_int_c1_clk",
        "gw_config_c1_clk",
    ]

    def __init__(self, *args, **kwargs):
        uut = kwargs["uut"]
        del kwargs["uut"]

        super().__init__(*args, **kwargs)

        collect_signals(self.SIGNALS, uut, self)

        self.lock = Lock()
        self.state = {sig: False for sig in self.SIGNALS}

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    async def run_phase(self):
        period = ConfigDB().get(None, "", "TEST_CLK_PERIOD")

        # Start monitoring tasks
        for name in self.SIGNALS:
            cocotb.start_soon(self.monitor_clock(name))

        # Periodically sample clock state and send messages
        while True:
            # Wait
            await Timer(period * 5, "ns")

            # Sample state and send item
            async with self.lock:
                self.ap.write(ClockStateItem(self.state))

    async def monitor_clock(self, name):
        period = ConfigDB().get(None, "", "TEST_CLK_PERIOD")
        signal = getattr(self, name)

        # Monitor the clock signal
        while True:
            # Wait for clock edges with timeout
            try:
                await with_timeout(Edge(signal), 2.0 * period, "ns")
                toggling = True
            except SimTimeoutError:
                toggling = False

            # Update the state
            async with self.lock:
                self.state[name] = toggling


# =============================================================================


class Scoreboard(uvm_component):
    """
    Clock activity scoreboard.
    """

    CLOCKS = [
        "pic_raddr_c1_clk",
        "pic_data_c1_clk",
        "pic_pri_c1_clk",
        "pic_int_c1_clk",
    ]

    IO_CLOCKS = [
        # FIXME: "IO" clock gates are instanced along with gateway modules
        # inside a generate block. It appears that cocotb does not have access
        # to them.
    ]

    def __init__(self, name, parent):
        super().__init__(name, parent)

        self.passed = None

    def build_phase(self):
        self.fifo = uvm_tlm_analysis_fifo("fifo", self)
        self.port = uvm_get_port("port", self)

    def connect_phase(self):
        self.port.connect(self.fifo.get_export)

    def check_phase(self):
        while self.port.can_get():
            # Get an item
            got_item, item = self.port.try_get()
            assert got_item

            # Got a change in clock override control
            if isinstance(item, ClockEnableItem):
                # Initially pass
                if self.passed is None:
                    self.passed = True

                # Reject next clock state item
                got_it, it = self.port.try_get()
                assert got_it and isinstance(it, ClockStateItem)

                # Get next clock state item and process it
                got_it, it = self.port.try_get()
                assert got_it and isinstance(it, ClockStateItem)

                # Check clocks
                for clk in self.CLOCKS:
                    if it.state[clk] != item.clk_en:
                        self.passed = False
                        self.logger.error(
                            "Clock '{}' is {}toggling".format(
                                clk,
                                "not " if item.clk_en else "",
                            )
                        )

                for clk in self.IO_CLOCKS:
                    if it.state[clk] != item.io_clk_en:
                        self.passed = False
                        self.logger.error(
                            "IO clock '{}' is {}toggling".format(
                                clk,
                                "not " if item.io_clk_en else "",
                            )
                        )

    def final_phase(self):
        if not self.passed:
            self.logger.critical("{} reports a failure".format(type(self)))
            assert False


# =============================================================================


class TestSequence(uvm_sequence):
    """
    A sequence which instructs a driver to enable/disable clock gating override
    """

    async def body(self):
        period = ConfigDB().get(None, "", "TEST_CLK_PERIOD")

        # Disable overrides
        item = ClockEnableItem(0, 0)
        await self.start_item(item)
        await self.finish_item(item)

        # Wait
        await Timer(20 * period, "ns")

        # Enable clock override
        item = ClockEnableItem(1, 0)
        await self.start_item(item)
        await self.finish_item(item)

        # Wait
        await Timer(20 * period, "ns")

        # Disable overrides
        item = ClockEnableItem(0, 0)
        await self.start_item(item)
        await self.finish_item(item)

        # Wait
        await Timer(20 * period, "ns")

        # Enable clock override
        item = ClockEnableItem(0, 1)
        await self.start_item(item)
        await self.finish_item(item)

        # Wait
        await Timer(20 * period, "ns")

        # Disable overrides
        item = ClockEnableItem(0, 0)
        await self.start_item(item)
        await self.finish_item(item)

        # Wait
        await Timer(20 * period, "ns")


# =============================================================================


class TestEnv(BaseEnv):
    """
    Test environment
    """

    def build_phase(self):
        super().build_phase()

        # Sequencers
        self.clken_seqr = uvm_sequencer("clken_seqr", self)

        # Clock enable driver and monitor
        self.clken_drv = ClkenDriver("clken_drv", self, uut=cocotb.top)
        self.clken_mon = ClkenMonitor("clken_mon", self, uut=cocotb.top)

        # Clock monitor
        self.clk_mon = ClockMonitor("clk_mon", self, uut=cocotb.top)

        # Add scoreboard
        self.scoreboard = Scoreboard("scoreboard", self)

    def connect_phase(self):
        super().connect_phase()
        self.clken_drv.seq_item_port.connect(self.clken_seqr.seq_item_export)
        self.clken_mon.ap.connect(self.scoreboard.fifo.analysis_export)
        self.clk_mon.ap.connect(self.scoreboard.fifo.analysis_export)


@pyuvm.test()
class TestClockEnable(BaseTest):
    """
    A test that checks forcing clock gates open
    """

    def __init__(self, name, parent):
        super().__init__(name, parent, TestEnv)

    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = TestSequence.create("stimulus")

    async def run(self):
        await self.seq.start(self.env.clken_seqr)
