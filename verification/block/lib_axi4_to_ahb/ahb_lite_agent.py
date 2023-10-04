# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

import cocotb
from ahb_lite_bfm import AHBLiteBFM
from cocotb.queue import QueueEmpty
from cocotb.triggers import RisingEdge
from common import BaseMonitor, get_int
from pyuvm import ConfigDB, uvm_agent, uvm_analysis_port, uvm_driver, uvm_sequencer


class AHBLiteAgent(uvm_agent):
    """
       Seqr <---> Driver
    Monitor <--^
    """

    def build_phase(self):
        self.seqr = uvm_sequencer("seqr", self)
        ConfigDB().set(None, "*", "ahb_seqr", self.seqr)
        self.monitor = AHBLiteMonitor("axi_w_agent", self)
        self.driver = AHBLiteDriver("axi_w_driver", self)

    def connect_phase(self):
        self.driver.seq_item_port.connect(self.seqr.seq_item_export)


class AHBLiteDriver(uvm_driver):
    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)
        self.rst_n = cocotb.top.rst_l
        self.clk = cocotb.top.clk

    def start_of_simulation_phase(self):
        self.bfm = AHBLiteBFM()

    async def run_phase(self):
        self.bfm.start_bfm()
        while True:
            if get_int(self.rst_n) == 0:
                await RisingEdge(self.rst_n)
                self.logger.info("Agent: AHB Lite: Reset Posedge")

            await RisingEdge(self.clk)
            try:
                response = self.bfm.rsp_driver_q.get_nowait()
                self.seq_item_port.put_response(response)
                # Expect two items per one response (hready is asserted for 2 cycles)
                for _ in range(2):
                    item = await self.seq_item_port.get_next_item()
                    await self.drive(item)
                    self.logger.debug(f"Driven: {item}")
                    self.seq_item_port.item_done()
            except QueueEmpty:
                pass

    async def drive(self, item):
        await self.bfm.req_driver_q_put(
            item.ahb_hrdata,
            item.ahb_hready,
            item.ahb_hresp,
        )


class AHBLiteMonitor(BaseMonitor):
    def __init__(self, name, parent):
        super().__init__(name, parent)

    def build_phase(self):
        super().build_phase()
        self.bfm = AHBLiteBFM()
