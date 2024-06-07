# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

import cocotb
from axi_pkg import AXI_W_CHAN_RSP_SIGNALS
from cocotb.queue import QueueEmpty
from cocotb.triggers import RisingEdge
from pyuvm import UVMQueue, utility_classes, uvm_root

from common import get_int, get_signals


class AXIWriteChannelBFM(metaclass=utility_classes.Singleton):
    def __init__(self):
        self.dut = cocotb.top
        self.rst_n = cocotb.top.rst_l
        self.clk = cocotb.top.clk
        self.req_driver_q = UVMQueue(maxsize=1)
        self.req_monitor_q = UVMQueue()
        self.rsp_monitor_q = UVMQueue()

    async def req_driver_q_put(
        self,
        axi_awvalid,
        axi_awid,
        axi_awaddr,
        axi_awsize,
        axi_awprot,
        axi_wvalid,
        axi_wdata,
        axi_wstrb,
        axi_wlast,
        axi_bready,
    ):
        item = (
            axi_awvalid,
            axi_awid,
            axi_awaddr,
            axi_awsize,
            axi_awprot,
            axi_wvalid,
            axi_wdata,
            axi_wstrb,
            axi_wlast,
            axi_bready,
        )
        await self.req_driver_q.put(item)

    async def req_monitor_q_get(self):
        item = await self.req_monitor_q.get()
        return item

    async def rsp_monitor_q_get(self):
        result = await self.rsp_monitor_q.get()
        return result

    async def drive(self):
        while True:
            if self.rst_n.value == 0:
                self.dut.axi_awvalid.value = 0
                self.dut.axi_awid.value = 0
                self.dut.axi_awaddr.value = 0
                self.dut.axi_awsize.value = 0
                self.dut.axi_awprot.value = 0
                self.dut.axi_wvalid.value = 0
                self.dut.axi_wdata.value = 0
                self.dut.axi_wstrb.value = 0
                self.dut.axi_wlast.value = 0
                self.dut.axi_bready.value = 0
                await RisingEdge(self.rst_n)
            await RisingEdge(self.clk)
            try:
                (
                    axi_awvalid,
                    axi_awid,
                    axi_awaddr,
                    axi_awsize,
                    axi_awprot,
                    axi_wvalid,
                    axi_wdata,
                    axi_wstrb,
                    axi_wlast,
                    axi_bready,
                ) = self.req_driver_q.get_nowait()
                self.dut.axi_awvalid.value = axi_awvalid
                self.dut.axi_awid.value = axi_awid
                self.dut.axi_awaddr.value = axi_awaddr
                self.dut.axi_awsize.value = axi_awsize
                self.dut.axi_awprot.value = axi_awprot
                self.dut.axi_wvalid.value = axi_wvalid
                self.dut.axi_wdata.value = axi_wdata
                self.dut.axi_wstrb.value = axi_wstrb
                self.dut.axi_wlast.value = axi_wlast
                self.dut.axi_bready.value = axi_bready
            except QueueEmpty:
                pass

    async def req_monitor_q_bfm(self):
        while True:
            if self.rst_n.value == 0:
                await RisingEdge(self.rst_n)
            await RisingEdge(self.clk)
            send_item = 0
            if get_int(self.dut.axi_awvalid):
                if get_int(self.dut.axi_awready):
                    send_item = 1

            if get_int(self.dut.axi_wvalid):
                if get_int(self.dut.axi_wready):
                    send_item = 1

            if send_item:
                item = (
                    get_int(self.dut.axi_awvalid),
                    get_int(self.dut.axi_awid),
                    get_int(self.dut.axi_awaddr),
                    get_int(self.dut.axi_awsize),
                    get_int(self.dut.axi_awprot),
                    get_int(self.dut.axi_wvalid),
                    get_int(self.dut.axi_wdata),
                    get_int(self.dut.axi_wstrb),
                    get_int(self.dut.axi_wlast),
                    get_int(self.dut.axi_bready),
                )
                await self.req_monitor_q.put(item)

    async def rsp_monitor_q_bfm(self):
        while True:
            if self.rst_n.value == 0:
                await RisingEdge(self.rst_n)
            await RisingEdge(self.clk)
            if get_int(self.dut.axi_bvalid):
                if get_int(self.dut.axi_bready):
                    sigs = get_signals(AXI_W_CHAN_RSP_SIGNALS, self.dut)
                    values = tuple(sig.value for sig in sigs)
                    await self.rsp_monitor_q.put(values)

    def start_bfm(self):
        cocotb.start_soon(self.drive())
        cocotb.start_soon(self.req_monitor_q_bfm())
        cocotb.start_soon(self.rsp_monitor_q_bfm())
