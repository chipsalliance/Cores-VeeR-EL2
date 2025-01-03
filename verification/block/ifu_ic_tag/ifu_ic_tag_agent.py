# Copyright (c) 2025 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

import cocotb
from ifu_ic_tag_bfm import IcTagBFM
from cocotb.queue import QueueEmpty, QueueFull
from cocotb.triggers import RisingEdge
from pyuvm import ConfigDB, uvm_agent, uvm_analysis_port, uvm_driver, uvm_sequencer, uvm_monitor

class IcTagAgent(uvm_agent):
    """
       Seqr <---> Driver
    Monitor <--^
    """

    def build_phase(self):
        self.seqr = uvm_sequencer("seqr", self)
        ConfigDB().set(None, "*", "seqr", self.seqr)
        self.monitor = IcTagMonitor("monitor", self)
        self.driver = IcTagDriver("driver", self)

    def connect_phase(self):
        self.driver.seq_item_port.connect(self.seqr.seq_item_export)


class IcTagDriver(uvm_driver):
    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)
        self.rst_n = cocotb.top.rst_l
        self.clk = cocotb.top.clk

    def start_of_simulation_phase(self):
        self.bfm = IcTagBFM()

    async def run_phase(self):
        self.bfm.start_bfm()
        while True:
            item = await self.seq_item_port.get_next_item()
            self.bfm.req_driver_q.put_nowait(item)
            self.logger.debug(f"Driven: {item}")
            await self.bfm.rsp_driver_q.get()
            self.seq_item_port.item_done()

class IcTagMonitor(uvm_monitor):
    def __init__(self, name, parent):
        super().__init__(name, parent)

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)
        self.bfm = IcTagBFM()

    async def monitor_rsp(self):
        while True:
            try:
                datum = await self.bfm.rsp_monitor_q_get()
                self.logger.debug(f"monitor_rsp: {datum}")
                self.ap_rsp.write(datum)
            except:
                QueueEmpty

    async def run_phase(self):
        # pass
        cocotb.start_soon(self.monitor_rsp())
