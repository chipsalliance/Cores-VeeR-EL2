# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

import cocotb
from axi_pkg import AXI_NOTIFICATION, AXI_R_CHAN_RSP_SIGNALS
from cocotb.queue import QueueEmpty
from cocotb.triggers import RisingEdge
from common import get_int, get_signals
from pyuvm import UVMQueue, utility_classes, uvm_root


class AXIReadChannelBFM(metaclass=utility_classes.Singleton):
    def __init__(self):
        self.dut = cocotb.top
        self.rst_n = cocotb.top.rst_l
        self.clk = cocotb.top.clk
        self.req_driver_q = UVMQueue(maxsize=1)
        self.rsp_driver_q = UVMQueue(maxsize=1)
        self.req_monitor_q = UVMQueue(maxsize=0)
        self.rsp_monitor_q = UVMQueue(maxsize=0)
        self.TIMEOUT_THRESHOLD = 20

    async def req_driver_q_put(
        self,
        axi_arvalid,
        axi_arid,
        axi_araddr,
        axi_arsize,
        axi_arprot,
        axi_rready,
    ):
        item = (
            axi_arvalid,
            axi_arid,
            axi_araddr,
            axi_arsize,
            axi_arprot,
            axi_rready,
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
                self.dut.axi_arvalid.value = 0
                self.dut.axi_arid.value = 0
                self.dut.axi_araddr.value = 0
                self.dut.axi_arsize.value = 0
                self.dut.axi_arprot.value = 0
                self.dut.axi_rready.value = 0
                await RisingEdge(self.rst_n)
            await RisingEdge(self.clk)
            try:
                (
                    axi_arvalid,
                    axi_arid,
                    axi_araddr,
                    axi_arsize,
                    axi_arprot,
                    axi_rready,
                ) = self.req_driver_q.get_nowait()
                self.dut.axi_arvalid.value = axi_arvalid
                self.dut.axi_arid.value = axi_arid
                self.dut.axi_araddr.value = axi_araddr
                self.dut.axi_arsize.value = axi_arsize
                self.dut.axi_arprot.value = axi_arprot
                self.dut.axi_rready.value = axi_rready
            except QueueEmpty:
                pass

            # Handshake ARVALID <-> ARREADY
            if get_int(self.dut.axi_arvalid):
                timeout = 0
                while get_int(self.dut.axi_arready) == 0:
                    timeout += 1
                    self.rsp_driver_q.put_nowait(AXI_NOTIFICATION.AXI_BUSY)
                    await RisingEdge(self.clk)
                    if timeout > self.TIMEOUT_THRESHOLD:
                        raise TimeoutError("Transaction Request Handshake Timeout: AXI Read")

    async def req_monitor_q_bfm(self):
        while True:
            if self.rst_n.value == 0:
                await RisingEdge(self.rst_n)
            await RisingEdge(self.clk)
            if get_int(self.dut.axi_arvalid):
                if get_int(self.dut.axi_arready):
                    item = (
                        get_int(self.dut.axi_arvalid),
                        get_int(self.dut.axi_arid),
                        get_int(self.dut.axi_araddr),
                        get_int(self.dut.axi_arsize),
                        get_int(self.dut.axi_arprot),
                        get_int(self.dut.axi_rready),
                    )
                    await self.req_monitor_q.put(item)

    async def rsp_monitor_q_bfm(self):
        while True:
            if self.rst_n.value == 0:
                await RisingEdge(self.rst_n)
            await RisingEdge(self.clk)
            if get_int(self.dut.axi_rvalid):
                sigs = get_signals(AXI_R_CHAN_RSP_SIGNALS, self.dut)
                values = tuple(sig.value for sig in sigs)
                await self.rsp_monitor_q.put(values)

    def start_bfm(self):
        cocotb.start_soon(self.drive())
        cocotb.start_soon(self.req_monitor_q_bfm())
        cocotb.start_soon(self.rsp_monitor_q_bfm())
