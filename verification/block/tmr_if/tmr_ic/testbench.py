#
# Copyright (c) 2026 Antmicro
# SPDX-License-Identifier: Apache-2.0

import os

from cocotb.utils import get_sim_time
from pyuvm import *

import common
from common import BusDriver, BusItem, BusMonitor, FaultItem, FaultMonitor, MuBiFalse

# ==============================================================================


class BaseScoreboard(uvm_component):
    """
    Base PyUVM scoreboard
    """

    def build_phase(self):
        self.passed = False

        self.veer_bus_fifo = uvm_tlm_analysis_fifo("veer_bus_fifo", self)
        self.veer_bus_port = uvm_get_port("veer_bus_port", self)

        self.out_bus_fifo = uvm_tlm_analysis_fifo("out_bus_fifo", self)
        self.out_bus_port = uvm_get_port("out_bus_port", self)

        self.fault_fifo = uvm_tlm_analysis_fifo("fault_fifo", self)
        self.fault_port = uvm_get_port("fault_port", self)

    def connect_phase(self):
        self.veer_bus_port.connect(self.veer_bus_fifo.get_export)
        self.out_bus_port.connect(self.out_bus_fifo.get_export)
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
        self.clock_domain = parent.clock_domain

    def build_phase(self):

        bus_signals = [
            "ic_b_sb_wren",
            "ic_b_sb_bit_en_vec",
            "ic_sb_wr_data",
            "ic_rw_addr_bank_q",
            "ic_bank_way_clken_final",
            "ic_bank_way_clken_final_up",
            "ic_tag_clken_final",
            "ic_tag_wren_q",
            "ic_tag_wren_biten_vec",
            "ic_tag_wr_data",
            "ic_rw_addr_q",
        ]

        ConfigDB().set(None, "*", "TEST_CLK_PERIOD", 1)
        ConfigDB().set(None, "*", "TEST_ITERATIONS", 100)

        # VeeR-side bus request driver
        self.veer_bus_driver = BusDriver("veer_bus_driver", self, clock_domain=self.clock_domain)

        # VeeR-side bus sequencer
        self.veer_bus_seqr = uvm_sequencer("veer_bus_seqr", self)

        # VeeR-side bus monitor
        self.veer_bus_monitor = BusMonitor(
            "veer_bus_monitor",
            self,
            clock_domain=self.clock_domain,
            signals=[s + "_veer" for s in bus_signals],
        )

        # TMR complex output side bus monitor
        self.out_bus_monitor = BusMonitor(
            "out_bus_monitor",
            self,
            clock_domain=self.clock_domain,
            signals=bus_signals,
        )

        # Fault status output monitor
        self.fault_monitor = FaultMonitor(
            "fault_monitor",
            self,
            clock_domain=self.clock_domain,
            signals=[
                cocotb.top.ic_fault_q[0],
                cocotb.top.ic_fault_q[1],
                cocotb.top.ic_fault_q[2],
            ],
        )

        # Scoreboard(s)
        self.scoreboard = None
        if self.scb_class is not None:
            self.scoreboard = self.scb_class("scoreboard", self)

    def connect_phase(self):
        self.veer_bus_driver.seq_item_port.connect(self.veer_bus_seqr.seq_item_export)
        if self.scoreboard:
            self.veer_bus_monitor.ap.connect(self.scoreboard.veer_bus_fifo.analysis_export)
            self.out_bus_monitor.ap.connect(self.scoreboard.out_bus_fifo.analysis_export)
            self.fault_monitor.ap.connect(self.scoreboard.fault_fifo.analysis_export)


# ==============================================================================


class BaseTest(common.BaseTest):
    """
    Base PyUVM test for the module
    """

    def __init__(self, name, parent, scb_class=None):
        super().__init__(
            name,
            parent,
            clk_name="clk",
            rst_name="rst_l",
            scb_class=scb_class,
            env_class=BaseEnv,
        )

    async def initial(self):

        # Initialize
        cocotb.top.ic_fault_d[0].value = MuBiFalse
        cocotb.top.ic_fault_d[1].value = MuBiFalse
        cocotb.top.ic_fault_d[2].value = MuBiFalse

        cocotb.top.ic_b_sb_wren_veer.value = [0] * 3
        cocotb.top.ic_b_sb_bit_en_vec_veer.value = [0] * 3
        cocotb.top.ic_sb_wr_data_veer.value = [0] * 3
        cocotb.top.ic_rw_addr_bank_q_veer.value = [0] * 3
        cocotb.top.ic_bank_way_clken_final_veer.value = [0] * 3
        cocotb.top.ic_bank_way_clken_final_up_veer.value = [0] * 3
        cocotb.top.ic_tag_clken_final_veer.value = [0] * 3
        cocotb.top.ic_tag_wren_q_veer.value = [0] * 3
        cocotb.top.ic_tag_wren_biten_vec_veer.value = [0] * 3
        cocotb.top.ic_tag_wr_data_veer.value = [0] * 3
        cocotb.top.ic_rw_addr_q_veer.value = [0] * 3

        cocotb.top.wb_packeddout_pre.value = 0
        cocotb.top.wb_dout_pre_up.value = 0
        cocotb.top.ic_tag_data_raw_packed_pre.value = 0
        cocotb.top.ic_tag_data_raw_pre.value = 0
