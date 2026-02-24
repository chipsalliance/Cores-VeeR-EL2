# Copyright (c) 2024 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0
import logging
import os

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, FallingEdge, RisingEdge
from pyuvm import ConfigDB, uvm_env, uvm_report_object, uvm_test


class BaseEnv(uvm_env):
    """
    Base PyUVM test environment
    """

    def build_phase(self):
        # Config
        ConfigDB().set(None, "*", "TEST_CLK_PERIOD", 1)
        ConfigDB().set(None, "*", "LOCKSTEP_DELAY", 3)
        ConfigDB().set(None, "*", "MUBI_WIDTH", 4)
        ConfigDB().set(None, "*", "MUBI_TRUE", 0x6)
        ConfigDB().set(None, "*", "MUBI_FALSE", 0x9)

    def connect_phase(self):
        pass


# ==============================================================================


class BaseTest(uvm_test):
    """
    Base test for the module
    """

    def __init__(self, name, parent, env_class=BaseEnv):
        super().__init__(name, parent)
        self.env_class = env_class
        self.dut = cocotb.top
        self.clk = self.dut.clk

        # Synchronize pyuvm logging level with cocotb logging level. Unclear
        # why it does not happen automatically.
        level = logging.getLevelName(os.environ.get("COCOTB_LOG_LEVEL", "INFO"))
        uvm_report_object.set_default_logging_level(level)

    def build_phase(self):
        self.env = self.env_class("env", self)

    def start_clock(self, name):
        period = ConfigDB().get(None, "", "TEST_CLK_PERIOD")
        sig = getattr(self.dut, name)
        clock = Clock(sig, period, units="ns")
        cocotb.start_soon(clock.start(start_high=False))

    async def do_reset(self):
        self.dut.rst_l.value = 0
        self.dut.dbg_rst_l.value = 0
        await ClockCycles(self.dut.clk, 2)
        await FallingEdge(self.dut.clk)
        self.dut.rst_l.value = 1
        self.dut.dbg_rst_l.value = 1

        # Initialize inputs
        # Enable corruption detection by default
        self.dut.disable_corruption_detection_i.value = self.mubi_false
        self.dut.lockstep_err_injection_en_i.value = self.mubi_false

    async def run_phase(self):
        self.raise_objection()

        self.mubi_false = ConfigDB().get(None, "", "MUBI_FALSE")
        self.mubi_true = ConfigDB().get(None, "", "MUBI_TRUE")
        self.mubi_max = (2 ** ConfigDB().get(None, "", "MUBI_WIDTH")) - 1

        # Start clocks
        self.start_clock("clk")

        # Issue reset
        await self.do_reset()
        await RisingEdge(self.clk)

        # Run the actual test
        await self.run()

        # Wait some cycles
        await ClockCycles(self.clk, 10)

        self.drop_objection()

    async def run(self):
        raise NotImplementedError()
