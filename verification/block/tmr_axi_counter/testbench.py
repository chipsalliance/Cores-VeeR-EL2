#
# Copyright (c) 2026 Antmicro
# SPDX-License-Identifier: Apache-2.0

import os

from axi_agent import *
from axi_bus import *
from cocotb.triggers import ClockCycles
from cocotbext.axi.axi_ram import AxiRam
from pyuvm import *

import common

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

        # AXI slave bus
        s_axi = SAxiBus.from_prefix(cocotb.top, "s_axi")
        # AXI master bus
        m_axi = MAxiBus.from_prefix(cocotb.top, "m_axi")

        # AXI master agent
        self.m_axi_agent = AxiAgent(
            "M_AXI",
            self,
            type=AxiAgentType.MASTER,
            bfm_args={
                "bus": s_axi,
                "clock": cocotb.top.clk_i,
                "reset": cocotb.top.rst_ni,
                "reset_active_level": 0,
            },
        )

        ConfigDB().set(None, "*", "AXI_AGENT", self.m_axi_agent)

        # AXI slave "agent"
        self.s_axi_agent = AxiRam(
            bus=m_axi,
            clock=cocotb.top.clk_i,
            reset=cocotb.top.rst_ni,
            reset_active_level=0,
            size=2**32,
        )

        # AXI slave monitor
        self.s_axi_monitor = AxiMonitor(
            "S_AXI",
            self,
            bfm_args={
                "bus": m_axi,
                "clock": cocotb.top.clk_i,
                "reset": cocotb.top.rst_ni,
                "reset_active_level": 0,
            },
        )


# ==============================================================================


class BaseTest(common.BaseTest):
    """
    Base PyUVM test for the module
    """

    def __init__(self, name, parent):
        super().__init__(name, parent, scb_class=None, env_class=BaseEnv)
