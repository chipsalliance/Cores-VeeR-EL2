#
# Copyright (c) 2026 Antmicro
# SPDX-License-Identifier: Apache-2.0

import os

from axi_agent import *
from axi_bus import *
from cocotb.clock import Clock
from cocotb.handle import ModifiableObject
from cocotb.triggers import ClockCycles, FallingEdge, RisingEdge
from cocotb.utils import get_sim_time
from cocotbext.axi.axi_ram import AxiRam
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
        super().__init__(*args, **kwargs)

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    async def run_phase(self):
        prev_fault = None

        while True:
            await RisingEdge(cocotb.top.clk_i)

            curr_fault = [
                cocotb.top.s_axi_a_fault_o.value == MuBiTrue,
                cocotb.top.s_axi_b_fault_o.value == MuBiTrue,
                cocotb.top.s_axi_c_fault_o.value == MuBiTrue,
            ]

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


class BaseScoreboard(uvm_component):

    def build_phase(self):
        self.passed = False

        self.s_axi_a_tr_fifo = uvm_tlm_analysis_fifo("s_axi_a_tr_fifo", self)
        self.s_axi_a_tr_port = uvm_get_port("s_axi_a_tr_port", self)

        self.s_axi_b_tr_fifo = uvm_tlm_analysis_fifo("s_axi_b_tr_fifo", self)
        self.s_axi_b_tr_port = uvm_get_port("s_axi_b_tr_port", self)

        self.s_axi_c_tr_fifo = uvm_tlm_analysis_fifo("s_axi_c_tr_fifo", self)
        self.s_axi_c_tr_port = uvm_get_port("s_axi_c_tr_port", self)

        self.m_axi_tr_fifo = uvm_tlm_analysis_fifo("m_axi_tr_fifo", self)
        self.m_axi_tr_port = uvm_get_port("m_axi_tr_port", self)

        self.fault_fifo = uvm_tlm_analysis_fifo("fault_fifo", self)
        self.fault_port = uvm_get_port("fault_port", self)

    def connect_phase(self):
        self.s_axi_a_tr_port.connect(self.s_axi_a_tr_fifo.get_export)
        self.s_axi_b_tr_port.connect(self.s_axi_b_tr_fifo.get_export)
        self.s_axi_c_tr_port.connect(self.s_axi_c_tr_fifo.get_export)
        self.m_axi_tr_port.connect(self.m_axi_tr_fifo.get_export)
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

        # AXI slave buses
        s_axi_a = SAxiBus.from_prefix(cocotb.top, "s_axi_a")
        s_axi_b = SAxiBus.from_prefix(cocotb.top, "s_axi_b")
        s_axi_c = SAxiBus.from_prefix(cocotb.top, "s_axi_c")

        # AXI master bus
        m_axi = MAxiBus.from_prefix(cocotb.top, "m_axi")

        # AXI master agents
        self.s_axi_a_agent = AxiAgent(
            "AXI_A",
            self,
            type=AxiAgentType.MASTER,
            bfm_args={
                "bus": s_axi_a,
                "clock": cocotb.top.clk_i,
                "reset": cocotb.top.rst_ni,
                "reset_active_level": 0,
            },
        )

        self.s_axi_b_agent = AxiAgent(
            "AXI_B",
            self,
            type=AxiAgentType.MASTER,
            bfm_args={
                "bus": s_axi_b,
                "clock": cocotb.top.clk_i,
                "reset": cocotb.top.rst_ni,
                "reset_active_level": 0,
            },
        )

        self.s_axi_c_agent = AxiAgent(
            "AXI_C",
            self,
            type=AxiAgentType.MASTER,
            bfm_args={
                "bus": s_axi_c,
                "clock": cocotb.top.clk_i,
                "reset": cocotb.top.rst_ni,
                "reset_active_level": 0,
            },
        )

        ConfigDB().set(None, "*", "AXI_AGENT_A", self.s_axi_a_agent)
        ConfigDB().set(None, "*", "AXI_AGENT_B", self.s_axi_b_agent)
        ConfigDB().set(None, "*", "AXI_AGENT_C", self.s_axi_c_agent)

        # AXI slave "agent"
        self.m_axi_agent = AxiRam(
            bus=m_axi,
            clock=cocotb.top.clk_i,
            reset=cocotb.top.rst_ni,
            reset_active_level=0,
            size=2**32,
        )

        # AXI slave monitor
        self.m_axi_monitor = AxiMonitor(
            "M_AXI",
            self,
            bfm_args={
                "bus": m_axi,
                "clock": cocotb.top.clk_i,
                "reset": cocotb.top.rst_ni,
                "reset_active_level": 0,
            },
        )

        # Fault status output monitor
        self.fault_monitor = FaultMonitor("fault_monitor", self)

        # Scoreboard(s)
        self.scoreboard = None
        if self.scb_class is not None:
            self.scoreboard = self.scb_class("scoreboard", self)

    def connect_phase(self):
        if self.scoreboard:
            self.s_axi_a_agent.monitor.tr_ap.connect(
                self.scoreboard.s_axi_a_tr_fifo.analysis_export
            )
            self.s_axi_b_agent.monitor.tr_ap.connect(
                self.scoreboard.s_axi_b_tr_fifo.analysis_export
            )
            self.s_axi_c_agent.monitor.tr_ap.connect(
                self.scoreboard.s_axi_c_tr_fifo.analysis_export
            )
            self.m_axi_monitor.tr_ap.connect(self.scoreboard.m_axi_tr_fifo.analysis_export)
            self.fault_monitor.ap.connect(self.scoreboard.fault_fifo.analysis_export)


# ==============================================================================


class BaseTest(uvm_test):
    """
    Base PyUVM test for the module
    """

    def __init__(self, name, parent, scb_class=None):
        super().__init__(name, parent)
        self.scb_class = scb_class

        # Synchronize pyuvm logging level with cocotb logging level. Unclear
        # why it does not happen automatically.
        level = logging.getLevelName(os.environ.get("COCOTB_LOG_LEVEL", "INFO"))
        uvm_report_object.set_default_logging_level(level)

    def build_phase(self):
        self.env = BaseEnv("env", self, self.scb_class)

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

        cocotb.top.s_axi_a_fault_i.value = MuBiFalse
        cocotb.top.s_axi_b_fault_i.value = MuBiFalse
        cocotb.top.s_axi_c_fault_i.value = MuBiFalse

        cocotb.top.s_axi_a_fault_clr_i.value = MuBiFalse
        cocotb.top.s_axi_b_fault_clr_i.value = MuBiFalse
        cocotb.top.s_axi_c_fault_clr_i.value = MuBiFalse

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
