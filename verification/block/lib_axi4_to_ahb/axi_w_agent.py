# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

import cocotb
from axi_w_bfm import AXIWriteChannelBFM
from axi_w_seq import (
    AXIWriteInactiveSeqItem,
    AXIWriteLastDataSeqItem,
    AXIWriteResponseWriteSeqItem,
    AXIWriteTransactionRequestSeqItem,
)
from cocotb.queue import QueueEmpty
from cocotb.triggers import RisingEdge
from common import BaseMonitor
from pyuvm import ConfigDB, uvm_agent, uvm_driver, uvm_sequencer


class AXIWriteChannelAgent(uvm_agent):
    """
       Seqr <---> Driver
    Monitor <--^
    """

    def build_phase(self):
        self.seqr = uvm_sequencer("seqr", self)
        ConfigDB().set(None, "*", "axi_w_seqr", self.seqr)
        self.monitor = AXIWriteChannelMonitor("axi_w_agent", self)
        self.driver = AXIWriteChannelDriver("axi_w_driver", self)

    def connect_phase(self):
        self.driver.seq_item_port.connect(self.seqr.seq_item_export)


class AXIWriteChannelDriver(uvm_driver):
    def build_phase(self):
        self.rst_n = cocotb.top.rst_l

    def start_of_simulation_phase(self):
        self.bfm = AXIWriteChannelBFM()

    async def run_phase(self):
        self.bfm.start_bfm()
        while True:
            if self.rst_n.value == 0:
                await RisingEdge(self.rst_n)
                self.logger.info("Agent: AXI Write: Reset Posedge")

            try:
                item = await self.seq_item_port.get_next_item()
            except QueueEmpty:
                pass

            if isinstance(item, AXIWriteInactiveSeqItem):
                await self.drive(item)
                self.logger.debug(f"Driven: {item}")
                self.seq_item_port.item_done()

            if isinstance(item, AXIWriteTransactionRequestSeqItem):
                await self.drive(item)
                self.logger.debug(f"Driven: {item}")
                await self.wait_handshake(sig_name="axi_awready")
                self.seq_item_port.item_done()

            if isinstance(item, AXIWriteLastDataSeqItem):
                await self.drive(item)
                self.logger.debug(f"Driven: {item}")
                await self.wait_handshake(sig_name="axi_wready")
                self.seq_item_port.item_done()

            if isinstance(item, AXIWriteResponseWriteSeqItem):
                await self.drive(item)
                await self.wait_handshake(sig_name="axi_bvalid")
                self.logger.debug(f"Driven: {item}")
                self.seq_item_port.item_done()

    async def wait_handshake(self, sig_name=None, TIMEOUT_THRESHOLD=30):
        timeout = 0
        while True:
            timeout += 1
            await RisingEdge(self.bfm.clk)
            sig_handle = getattr(self.bfm.dut, sig_name)
            if sig_handle.value:
                break

            if timeout > TIMEOUT_THRESHOLD:
                raise TimeoutError(f"Transaction Request Handshake Timeout: AXI Write: {sig_name}")

    async def drive(self, item):
        await self.bfm.req_driver_q_put(
            item.axi_awvalid,
            item.axi_awid,
            item.axi_awaddr,
            item.axi_awsize,
            item.axi_awprot,
            item.axi_wvalid,
            item.axi_wdata,
            item.axi_wstrb,
            item.axi_wlast,
            item.axi_bready,
        )


class AXIWriteChannelMonitor(BaseMonitor):
    def __init__(self, name, parent):
        super().__init__(name, parent)

    def build_phase(self):
        super().build_phase()
        self.bfm = AXIWriteChannelBFM()
