# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

import cocotb
from ahb_lite_pkg import (
    AHB_LITE_NOTIFICATION,
    AHB_LITE_RESPONSE_CODES,
    AHB_LITE_TRANSFER_TYPE_ENCODING,
    AHB_RSP_SIGNALS,
)
from cocotb.queue import QueueEmpty
from cocotb.triggers import RisingEdge
from pyuvm import UVMQueue, utility_classes

from common import get_int, get_signals


class AHBLiteBFM(metaclass=utility_classes.Singleton):
    def __init__(self):
        self.dut = cocotb.top
        self.rst_n = cocotb.top.rst_l
        self.clk = cocotb.top.clk
        self.req_driver_q = UVMQueue(maxsize=1)
        self.rsp_driver_q = UVMQueue()
        self.req_monitor_q = UVMQueue()
        self.rsp_monitor_q = UVMQueue()

    async def req_driver_q_put(self, ahb_hrdata, ahb_hready, ahb_hresp):
        item = (ahb_hrdata, ahb_hready, ahb_hresp)
        await self.req_driver_q.put(item)

    async def req_monitor_q_get(self):
        item = await self.req_monitor_q.get()
        return item

    async def rsp_monitor_q_get(self):
        result = await self.rsp_monitor_q.get()
        return result

    async def drive(self):
        prev_htrans = AHB_LITE_TRANSFER_TYPE_ENCODING.IDLE
        htrans = AHB_LITE_TRANSFER_TYPE_ENCODING.IDLE

        while True:
            if self.rst_n.value == 0:
                self.dut.ahb_hrdata.value = 0
                self.dut.ahb_hready.value = 0
                self.dut.ahb_hresp.value = 0
                await RisingEdge(self.rst_n)
            await RisingEdge(self.clk)

            prev_htrans = htrans
            if get_int(self.dut.ahb_htrans) == AHB_LITE_TRANSFER_TYPE_ENCODING.IDLE:
                htrans = AHB_LITE_TRANSFER_TYPE_ENCODING.IDLE
                self.dut.ahb_hrdata.value = 0
                self.dut.ahb_hready.value = 0
                self.dut.ahb_hresp.value = AHB_LITE_RESPONSE_CODES.OKAY
            elif get_int(self.dut.ahb_htrans) == AHB_LITE_TRANSFER_TYPE_ENCODING.NONSEQ:
                htrans = AHB_LITE_TRANSFER_TYPE_ENCODING.NONSEQ
                if get_int(self.dut.ahb_hwrite):
                    if htrans != prev_htrans:
                        self.rsp_driver_q.put_nowait(AHB_LITE_NOTIFICATION.AHB_LITE_WRITE)
                else:
                    if htrans != prev_htrans:
                        self.rsp_driver_q.put_nowait(AHB_LITE_NOTIFICATION.AHB_LITE_READ)

            try:
                (ahb_hrdata, ahb_hready, ahb_hresp) = self.req_driver_q.get_nowait()
                self.dut.ahb_hrdata.value = ahb_hrdata
                self.dut.ahb_hready.value = ahb_hready
                self.dut.ahb_hresp.value = ahb_hresp
            except QueueEmpty:
                self.dut.ahb_hrdata.value = 0
                self.dut.ahb_hready.value = 0
                self.dut.ahb_hresp.value = 0

    async def req_monitor_q_bfm(self):
        while True:
            await RisingEdge(self.clk)
            if get_int(self.dut.ahb_hready):
                item = (
                    get_int(self.dut.ahb_hrdata),
                    get_int(self.dut.ahb_hready),
                    get_int(self.dut.ahb_hresp),
                )
                await self.req_monitor_q.put(item)

    async def rsp_monitor_q_bfm(self):
        while True:
            await RisingEdge(self.clk)
            if get_int(self.dut.ahb_hready):
                sigs = get_signals(AHB_RSP_SIGNALS, self.dut)
                values = tuple(sig.value for sig in sigs)
                await self.rsp_monitor_q.put(values)

    def start_bfm(self):
        cocotb.start_soon(self.drive())
        cocotb.start_soon(self.req_monitor_q_bfm())
        cocotb.start_soon(self.rsp_monitor_q_bfm())
