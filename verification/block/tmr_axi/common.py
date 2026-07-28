#
# Copyright (c) 2026 Antmicro
# SPDX-License-Identifier: Apache-2.0

import os

import cocotb
from cocotb.clock import Clock
from cocotb.handle import ModifiableObject
from cocotb.triggers import ClockCycles, RisingEdge
from cocotb.utils import get_sim_time
from pyuvm import *

# ==============================================================================

# FIXME: Sync with makefile somehow
MuBiFalse = 0b01
MuBiTrue = 0b10

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


# ==============================================================================


class FaultMonitor(uvm_monitor):
    """
    Monitors the module's fault indicator outputs
    """

    def __init__(self, *args, **kwargs):
        self.signals = kwargs["signals"]
        del kwargs["signals"]
        super().__init__(*args, **kwargs)

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    async def run_phase(self):
        prev_fault = None

        while True:
            await RisingEdge(cocotb.top.clk_i)

            curr_fault = [sig.value == MuBiTrue for sig in self.signals]

            if prev_fault is None:
                prev_fault = curr_fault

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

    def __init__(self, name, parent, scb_class=None, env_class=None):
        super().__init__(name, parent)
        self.scb_class = scb_class
        self.env_class = env_class

        # Synchronize pyuvm logging level with cocotb logging level. Unclear
        # why it does not happen automatically.
        level = logging.getLevelName(os.environ.get("COCOTB_LOG_LEVEL", "INFO"))
        uvm_report_object.set_default_logging_level(level)

    def build_phase(self):
        assert self.env_class is not None
        self.env = self.env_class("env", self, self.scb_class)

    def start_clock(self, name):
        period = ConfigDB().get(None, "", "TEST_CLK_PERIOD")
        sig = getattr(cocotb.top, name)
        clock = Clock(sig, period, units="ns")
        cocotb.start_soon(clock.start(start_high=False))

    async def reset(self):

        # Wait, assert reset
        await ClockCycles(cocotb.top.clk_i, 3)
        cocotb.top.rst_ni.value = 0

        # It seems that cocotbext-axi does not drive AXI signals to a known
        # state on reset. This is important here as TMR continuiusly compares
        # their state. Clear them manually
        for name in dir(cocotb.top):
            obj = getattr(cocotb.top, name)
            if not isinstance(obj, ModifiableObject):
                continue

            if name.startswith("s_axi_") and name.endswith("_i"):
                obj.value = 0
            if name.startswith("m_axi_") and name.endswith("_i"):
                obj.value = 0

            if name.endswith("fault_i"):
                obj.value = MuBiFalse
            if name.endswith("fault_clr_i"):
                obj.value = MuBiFalse

        await ClockCycles(cocotb.top.clk_i, 2)
        cocotb.top.rst_ni.value = 1
        await ClockCycles(cocotb.top.clk_i, 3)

    async def run_phase(self):
        self.raise_objection()

        # Initialize signals
        cocotb.top.rst_ni.value = 1

        # Start clock
        self.start_clock("clk_i")
        await ClockCycles(cocotb.top.clk_i, 2)

        # Reset
        await self.reset()

        # Run the test
        await self.run()
        await ClockCycles(cocotb.top.clk_i, 2)
        self.drop_objection()

    async def run(self):
        raise NotImplementedError()
