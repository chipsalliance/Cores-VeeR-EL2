#
# Copyright (c) 2026 Antmicro
# SPDX-License-Identifier: Apache-2.0

import os
from copy import deepcopy

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, RisingEdge
from cocotb.utils import get_sim_time
from pyuvm import *

# ==============================================================================

# FIXME: Sync with makefile somehow
MuBiFalse = 0b01
MuBiTrue = 0b10

# ==============================================================================


class ClockDomain:
    def __init__(self, clk_name, rst_name):
        self.clk = getattr(cocotb.top, clk_name)
        self.rst = getattr(cocotb.top, rst_name)


# ==============================================================================


class BusItem(uvm_sequence_item):
    def __init__(self, name="BusItem"):
        super().__init__(name)
        self.timestamp = 0
        self.signals = dict()

    def __str__(self):
        return (
            f"BusItem(timestamp={self.timestamp}, "
            + ", ".join([f"{k}:{str(v)}" for k, v in self.signals.items()])
            + ")"
        )


class BusDriver(uvm_driver):
    def __init__(self, *args, **kwargs):
        self.clock_domain = kwargs["clock_domain"]
        del kwargs["clock_domain"]
        super().__init__(*args, **kwargs)

    async def run_phase(self):
        while True:
            it = await self.seq_item_port.get_next_item()
            assert isinstance(it, BusItem)

            # Drive the bus state
            await RisingEdge(self.clock_domain.clk)
            for k, v in it.signals.items():
                sig = getattr(cocotb.top, k)
                sig.value = v

            self.seq_item_port.item_done()


class BusMonitor(uvm_monitor):
    def __init__(self, *args, **kwargs):
        self.signals = kwargs["signals"]
        self.clock_domain = kwargs["clock_domain"]

        del kwargs["signals"]
        del kwargs["clock_domain"]

        super().__init__(*args, **kwargs)

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    async def sample(self):
        sample = dict()
        for name in self.signals:
            sig = getattr(cocotb.top, name)
            sample[name] = sig.value

        return sample

    async def run_phase(self):
        prev_state = None

        while True:
            await RisingEdge(self.clock_domain.clk)

            curr_state = await self.sample()

            if curr_state != prev_state:
                item = BusItem()
                item.timestamp = get_sim_time(units="ps")
                item.signals = deepcopy(curr_state)
                self.logger.debug(f"Bus state: {str(item)}")

                self.ap.write(item)
                prev_state = curr_state


# ==============================================================================


class FaultItem(uvm_sequence_item):
    def __init__(self, name="FaultItem"):
        super().__init__(name)
        self.timestamp = 0
        self.fault = [False, False, False]

    def __str__(self):
        return (
            f"FaultItem(timestamp={self.timestamp}, "
            + ",".join([str(int(f)) for f in self.fault])
            + ")"
        )


class FaultMonitor(uvm_monitor):
    """
    Monitors the module's fault indicator outputs
    """

    def __init__(self, *args, **kwargs):
        self.signals = kwargs["signals"]
        self.clock_domain = kwargs["clock_domain"]

        del kwargs["signals"]
        del kwargs["clock_domain"]

        super().__init__(*args, **kwargs)

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    async def run_phase(self):
        prev_fault = None

        while True:
            await RisingEdge(self.clock_domain.clk)

            curr_fault = [sig.value == MuBiTrue for sig in self.signals]

            if curr_fault != prev_fault:
                item = FaultItem()
                item.timestamp = get_sim_time(units="ps")
                item.fault = curr_fault
                self.logger.debug(f"Fault state: {str(item)}")

                self.ap.write(item)
                prev_fault = curr_fault


# ==============================================================================


class BaseTest(uvm_test):
    """
    Base PyUVM test for the module
    """

    def __init__(self, name, parent, clk_name, rst_name, scb_class=None, env_class=None):
        super().__init__(name, parent)
        self.scb_class = scb_class
        self.env_class = env_class

        self.clock_domain = ClockDomain(clk_name, rst_name)

        # Synchronize pyuvm logging level with cocotb logging level. Unclear
        # why it does not happen automatically.
        level = logging.getLevelName(os.environ.get("COCOTB_LOG_LEVEL", "INFO"))
        uvm_report_object.set_default_logging_level(level)

    def build_phase(self):
        assert self.env_class is not None
        self.env = self.env_class("env", self, self.scb_class)

    def start_clock(self):
        period = ConfigDB().get(None, "", "TEST_CLK_PERIOD")
        clock = Clock(self.clock_domain.clk, period, units="ns")
        cocotb.start_soon(clock.start(start_high=False))

    async def reset(self):

        # Wait, assert reset
        await ClockCycles(self.clock_domain.clk, 3)
        self.clock_domain.rst.value = 0

        # Initialize signals
        await self.initial()

        await ClockCycles(self.clock_domain.clk, 2)
        self.clock_domain.rst.value = 1
        await ClockCycles(self.clock_domain.clk, 3)

    async def run_phase(self):
        self.raise_objection()

        # Initialize signals
        self.clock_domain.rst.value = 1
        await self.initial()

        # Start clock
        self.start_clock()
        # Reset
        await self.reset()

        # Run the test
        await self.run()
        await ClockCycles(self.clock_domain.clk, 2)
        self.drop_objection()

    async def initial(self):
        raise NotImplementedError()

    async def run(self):
        raise NotImplementedError()
