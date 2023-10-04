# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

import random

import cocotb
import pyuvm
from axi_r_bfm import AXIReadChannelBFM
from cocotb.queue import QueueEmpty
from cocotb.triggers import RisingEdge
from common import BaseMonitor
from pyuvm import ConfigDB, uvm_agent, uvm_analysis_port, uvm_driver, uvm_sequencer


class AXIReadChannelAgent(uvm_agent):
    def build_phase(self):
        self.seqr = uvm_sequencer("seqr", self)
        ConfigDB().set(None, "*", "axi_r_seqr", self.seqr)
        self.monitor = AXIReadChannelMonitor("axi_r_agent", self)
        self.driver = AXIReadChannelDriver("axi_r_driver", self)

    def connect_phase(self):
        self.driver.seq_item_port.connect(self.seqr.seq_item_export)


class AXIReadChannelDriver(uvm_driver):
    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)
        self.rst_n = cocotb.top.rst_l
        self.clk = cocotb.top.clk

    def start_of_simulation_phase(self):
        self.bfm = AXIReadChannelBFM()

    async def run_phase(self):
        self.bfm.start_bfm()
        while True:
            if self.rst_n.value == 0:
                await RisingEdge(self.rst_n)
                self.logger.info("Agent: AXI Read: Reset Posedge")

            try:
                pending = 1
                axi_notification = self.bfm.rsp_driver_q.get_nowait()
            except QueueEmpty:
                pending = 0

            if pending:
                self.seq_item_port.put_response(axi_notification)

            self.seq_item_port.put_response(3)
            try:
                item = await self.seq_item_port.get_next_item()
                await self.drive(item)
                self.logger.debug(f"Agent: AXI Read: Driven: {item}")
                self.seq_item_port.item_done()
            except QueueEmpty:
                pass

    async def drive(self, item):
        await self.bfm.req_driver_q_put(
            item.axi_arvalid,
            item.axi_arid,
            item.axi_araddr,
            item.axi_arsize,
            item.axi_arprot,
            item.axi_rready,
        )


class AXIReadChannelMonitor(BaseMonitor):
    def __init__(self, name, parent):
        super().__init__(name, parent)

    def build_phase(self):
        super().build_phase()
        self.bfm = AXIReadChannelBFM()
