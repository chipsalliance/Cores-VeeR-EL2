#
# Copyright (c) 2026 Antmicro
# SPDX-License-Identifier: Apache-2.0

import os

from axi_agent import *
from axi_bus import *
from cocotb.triggers import ClockCycles, FallingEdge, RisingEdge
from cocotb.utils import get_sim_time
from cocotbext.axi.axi_ram import AxiRam
from pyuvm import *

import common
from common import FaultItem, FaultMonitor, MuBiFalse, MuBiTrue

# ==============================================================================


class BaseScoreboard(uvm_component):

    def build_phase(self):
        self.passed = False

        self.a_m_axi_tr_fifo = uvm_tlm_analysis_fifo("a_m_axi_tr_fifo", self)
        self.a_m_axi_tr_port = uvm_get_port("a_m_axi_tr_port", self)

        self.b_m_axi_tr_fifo = uvm_tlm_analysis_fifo("b_m_axi_tr_fifo", self)
        self.b_m_axi_tr_port = uvm_get_port("b_m_axi_tr_port", self)

        self.c_m_axi_tr_fifo = uvm_tlm_analysis_fifo("c_m_axi_tr_fifo", self)
        self.c_m_axi_tr_port = uvm_get_port("c_m_axi_tr_port", self)

        self.s_axi_tr_fifo = uvm_tlm_analysis_fifo("s_axi_tr_fifo", self)
        self.s_axi_tr_port = uvm_get_port("s_axi_tr_port", self)

        self.fault_fifo = uvm_tlm_analysis_fifo("fault_fifo", self)
        self.fault_port = uvm_get_port("fault_port", self)

    def connect_phase(self):
        self.a_m_axi_tr_port.connect(self.a_m_axi_tr_fifo.get_export)
        self.b_m_axi_tr_port.connect(self.b_m_axi_tr_fifo.get_export)
        self.c_m_axi_tr_port.connect(self.c_m_axi_tr_fifo.get_export)
        self.s_axi_tr_port.connect(self.s_axi_tr_fifo.get_export)
        self.fault_port.connect(self.fault_fifo.get_export)

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

        # AXI master buses
        self.m_axi_a = MAxiBus.from_prefix(cocotb.top, "a_m_axi")
        self.m_axi_b = MAxiBus.from_prefix(cocotb.top, "b_m_axi")
        self.m_axi_c = MAxiBus.from_prefix(cocotb.top, "c_m_axi")

        # AXI slave bus
        s_axi = SAxiBus.from_prefix(cocotb.top, "s_axi")

        # AXI mater agent
        self.s_axi_agent = AxiAgent(
            "S_AXI",
            self,
            type=AxiAgentType.MASTER,
            bfm_args={
                "bus": s_axi,
                "clock": cocotb.top.clk_i,
                "reset": cocotb.top.rst_ni,
                "reset_active_level": 0,
            },
        )

        ConfigDB().set(None, "*", "M_AXI_AGENT", self.s_axi_agent)

        # AXI slave "agent"
        self.a_m_axi_agent = AxiRam(
            bus=self.m_axi_a,
            clock=cocotb.top.clk_i,
            reset=cocotb.top.rst_ni,
            reset_active_level=0,
            size=2**32,
        )
        self.b_m_axi_agent = AxiRam(
            bus=self.m_axi_b,
            clock=cocotb.top.clk_i,
            reset=cocotb.top.rst_ni,
            reset_active_level=0,
            size=2**32,
        )
        self.c_m_axi_agent = AxiRam(
            bus=self.m_axi_c,
            clock=cocotb.top.clk_i,
            reset=cocotb.top.rst_ni,
            reset_active_level=0,
            size=2**32,
        )

        # AXI slave monitors
        self.a_m_axi_monitor = AxiMonitor(
            "S_AXI_A",
            self,
            bfm_args={
                "bus": self.m_axi_a,
                "clock": cocotb.top.clk_i,
                "reset": cocotb.top.rst_ni,
                "reset_active_level": 0,
            },
        )
        self.b_m_axi_monitor = AxiMonitor(
            "S_AXI_B",
            self,
            bfm_args={
                "bus": self.m_axi_b,
                "clock": cocotb.top.clk_i,
                "reset": cocotb.top.rst_ni,
                "reset_active_level": 0,
            },
        )
        self.c_m_axi_monitor = AxiMonitor(
            "S_AXI_C",
            self,
            bfm_args={
                "bus": self.m_axi_c,
                "clock": cocotb.top.clk_i,
                "reset": cocotb.top.rst_ni,
                "reset_active_level": 0,
            },
        )

        # Fault status output monitor
        self.fault_monitor = FaultMonitor(
            "fault_monitor",
            self,
            signals=[
                cocotb.top.a_m_axi_fault_o,
                cocotb.top.b_m_axi_fault_o,
                cocotb.top.c_m_axi_fault_o,
            ],
        )

        # Scoreboard(s)
        self.scoreboard = None
        if self.scb_class is not None:
            self.scoreboard = self.scb_class("scoreboard", self)

    def connect_phase(self):
        if self.scoreboard:
            self.s_axi_agent.monitor.tr_ap.connect(self.scoreboard.s_axi_tr_fifo.analysis_export)
            self.a_m_axi_monitor.tr_ap.connect(self.scoreboard.a_m_axi_tr_fifo.analysis_export)
            self.b_m_axi_monitor.tr_ap.connect(self.scoreboard.b_m_axi_tr_fifo.analysis_export)
            self.c_m_axi_monitor.tr_ap.connect(self.scoreboard.c_m_axi_tr_fifo.analysis_export)
            self.fault_monitor.ap.connect(self.scoreboard.fault_fifo.analysis_export)


# ==============================================================================


class BaseTest(common.BaseTest):
    """
    Base PyUVM test for the module
    """

    def __init__(self, name, parent, scb_class=None):
        super().__init__(name, parent, scb_class=scb_class, env_class=BaseEnv)
