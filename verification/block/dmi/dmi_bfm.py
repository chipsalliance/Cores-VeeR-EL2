#
# Copyright (c) 2023 Antmicro
# SPDX-License-Identifier: Apache-2.0

import pyuvm
from cocotb.triggers import FallingEdge, RisingEdge
from common import Defaults, collect_signals, get_int
from dmi_seq import SetUncoreEnableSeqItem
from pyuvm import *


class MemoryModel:
    def __init__(self):
        self.memory = {}
        self.reset()

    def write(self, addr, data):
        self.memory.update({addr: data})

    def read(self, addr):
        return get_int(self.memory.setdefault(addr, 0))

    def reset(self):
        self.memory = {
            0x01: Defaults.JTAG_ID,
            0x10: Defaults.DTMCS,
            0x11: 0,
        }


class DMITestBfm(metaclass=utility_classes.Singleton):
    """
    A BFM for the DMI core module.
    """

    SIGNALS = [
        # Control inputs
        "core_rst_n",
        "core_clk",
        "jtag_id",
        # DMI inputs
        "uncore_enable",
        "dmi_core_rdata",
        "dmi_uncore_rdata",
        # DMI outputs
        "dmi_hard_reset",
        "rd_data",
        "dmi_core_en",
        "dmi_core_wr_en",
        "dmi_core_addr",
        "dmi_core_wdata",
        "dmi_uncore_en",
        "dmi_uncore_wr_en",
        "dmi_uncore_addr",
        "dmi_uncore_wdata",
    ]

    def __init__(self):
        self.dut = cocotb.top
        self.req_driver_q = UVMQueue(maxsize=1)
        self.req_monitor_q = UVMQueue(maxsize=0)
        self.rsp_monitor_q = UVMQueue(maxsize=0)

        self.predictor = ConfigDB().get(None, "", "JTAG_PREDICTOR")
        self.core_mem = MemoryModel()
        self.uncore_mem = MemoryModel()

        collect_signals(self.SIGNALS, self.dut, self)
        self.rst_n = self.core_rst_n
        self.clk = self.core_clk

    async def req_driver_q_put(self, item):
        await self.req_driver_q.put(item)

    async def rsp_monitor_q_get(self):
        result = await self.rsp_monitor_q.get()
        return result

    async def driver_bfm(self):
        """
        Reads a register
        """

        self.dmi_core_rdata.value = 0
        self.dmi_uncore_rdata.value = 0
        self.uncore_enable.value = 0
        self.jtag_id.value = Defaults.JTAG_ID

        while True:
            await FallingEdge(self.clk)
            try:
                item = self.req_driver_q.get_nowait()

                if isinstance(item, SetUncoreEnableSeqItem):
                    self.uncore_enable.value = item.uncore_enable

            except QueueEmpty:
                pass

    async def rsp_monitor_q_bfm(self):
        DMI_CORE_BOUNDARY = 0x4F

        while True:
            if self.rst_n.value == 0:
                await RisingEdge(self.rst_n)

            await RisingEdge(self.clk)

            if self.dmi_hard_reset.value:
                self.core_mem.reset()
                self.uncore_mem.reset()
                pass

            # DMI Core memory managment
            if self.dmi_core_en.value:
                self.dmi_core_rdata.value = self.core_mem.read(get_int(self.dmi_core_addr))
            if self.dmi_core_wr_en.value:
                self.core_mem.write(get_int(self.dmi_core_addr), get_int(self.dmi_core_wdata))

            # DMI Uncore memory managment
            if self.dmi_uncore_en.value:
                self.dmi_uncore_rdata.value = self.uncore_mem.read(get_int(self.dmi_uncore_addr))
            if self.dmi_uncore_wr_en.value:
                self.uncore_mem.write(get_int(self.dmi_uncore_addr), get_int(self.dmi_uncore_wdata))

            # Pass data to the scoreboard on write/read request
            if self.dmi_uncore_en.value or self.dmi_core_en.value:
                if (self.predictor.wr_addr.integer > DMI_CORE_BOUNDARY) and self.uncore_enable:
                    dmi_type = "uncore"
                    values = [
                        get_int(self.rd_data),
                        get_int(self.dmi_uncore_rdata),
                        get_int(self.dmi_uncore_addr),
                        get_int(self.dmi_uncore_en),
                        get_int(self.predictor.rd_en),
                    ]
                else:
                    dmi_type = "core"
                    values = [
                        get_int(self.rd_data),
                        get_int(self.dmi_core_rdata),
                        get_int(self.dmi_core_addr),
                        get_int(self.dmi_core_en),
                        get_int(self.predictor.rd_en),
                    ]

                self.rsp_monitor_q.put_nowait((values, dmi_type))

    def start_bfm(self):
        cocotb.start_soon(self.driver_bfm())
        cocotb.start_soon(self.rsp_monitor_q_bfm())
