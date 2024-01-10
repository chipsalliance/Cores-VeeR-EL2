# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

import cocotb
import pyuvm
from cocotb.triggers import ClockCycles, FallingEdge, ReadOnly, RisingEdge
from common import *
from jtag_pkg import *
from pyuvm import *

# =============================================================================


class MemoryModel:
    def __init__(self):
        self.memory = {}

    def write(self, addr, data):
        self.memory.update({addr, data})

    def read(self, addr):
        self.memory.setdefault(addr, 0)
        return self.memory.get[addr]

    def reset(self):
        self.memory = {}


class JTAGBfm(metaclass=utility_classes.Singleton):
    """
    A Bus Functional Model for JTAG TAP.
    """

    SIGNALS = [
        # Inputs
        "trst_n",
        "tck",
        "tms",
        "tdi",
        # Outputs
        "tdo",
        "tdoEnable",
    ]

    def __init__(self):
        self.dut = cocotb.top
        self.req_driver_q = UVMQueue(maxsize=1)
        self.req_monitor_q = UVMQueue(maxsize=0)
        self.rsp_monitor_q = UVMQueue(maxsize=0)

        self.predictor = ConfigDB().get(None, "", "JTAG_PREDICTOR")

        collect_signals(self.SIGNALS, self.dut, self)

    async def req_driver_q_put(self, tms, tdi):
        item = (tms, tdi)
        await self.req_driver_q.put(item)

    async def rsp_monitor_q_get(self):
        result = await self.rsp_monitor_q.get()
        return result

    async def reset(self):
        await FallingEdge(self.tck)
        self.trst_n.value = 0
        self.tms.value = 1
        self.tdi.value = 0
        await ClockCycles(self.tck, 10)
        await FallingEdge(self.tck)
        self.trst_n.value = 1
        await FallingEdge(self.tck)

    async def driver_bfm(self):
        sigs = [self.tms, self.tdi]
        for sig in sigs:
            sig.value = 0
        while True:
            await FallingEdge(self.tck)
            try:
                (tms, tdi) = self.req_driver_q.get_nowait()
                self.tms.value = tms
                self.tdi.value = tdi
            except QueueEmpty:
                pass

    async def req_monitor_q_bfm(self):
        while True:
            if self.trst_n.value == 0:
                await RisingEdge(self.trst_n)
            await RisingEdge(self.tck)

            item = (get_int(self.tms), get_int(self.tdi))
            self.req_monitor_q.put_nowait(item)

    async def rsp_monitor_q_bfm(self):
        while True:
            if self.trst_n.value == 0:
                await RisingEdge(self.trst_n)

            await FallingEdge(self.tck)
            await ReadOnly()
            self.predictor.predict_jtag_outputs(edge="neg")

            await RisingEdge(self.tck)
            await ReadOnly()
            self.predictor.predict_jtag_outputs(edge="pos")

            curr_values = [
                get_int(self.tdo),
                get_int(self.tdoEnable),
            ]
            predicted_values = [
                get_int(self.predictor.tdo),
                get_int(self.predictor.tdoEnable),
            ]
            self.rsp_monitor_q.put_nowait((curr_values, predicted_values))

    def start_bfm(self):
        cocotb.start_soon(self.driver_bfm())
        cocotb.start_soon(self.req_monitor_q_bfm())
        cocotb.start_soon(self.rsp_monitor_q_bfm())
