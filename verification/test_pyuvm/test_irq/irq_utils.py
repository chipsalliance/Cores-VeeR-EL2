#
# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: BSD-2-Clause

from cocotb.triggers import FallingEdge
from cocotb.queue import Queue

from pyuvm import *


def get_int(signal):
    try:
        sig = int(signal.value)
    except ValueError:
        sig = 0
    return sig


class IrqBfm(metaclass=utility_classes.Singleton):
    """
        Interrupt Bus Functional Model

        Drive:
            el2_veer_wrapper {
                input logic                      nmi_int
                input logic                      timer_int
                input logic                      soft_int
                input logic [pt.PIC_TOTAL_INT:1] extintsrc_req
            }
        Receive:
            el2_veer_wrapper {
                output logic trace_rv_i_interrupt_ip
            }

    """

    def __init__(self):
        self.dut = cocotb.top
        self.interrupt_driver_queue = Queue(maxsize=1)
        self.interrupt_source_queue = Queue(maxsize=0)
        self.trace_interrupt_queue = Queue(maxsize=0)
        self.interrupts = (self.dut.nmi_int,
                           self.dut.soft_int,
                           self.dut.timer_int,
                           self.dut.extintsrc_req)

    async def send_interrupt_source(self, ints):
        await self.interrupt_driver_queue.put(ints)

    async def get_interrupt_source(self):
        ints = await self.interrupt_source_queue.get()
        return ints

    async def get_trace_interrupt(self):
        ints = await self.trace_interrupt_queue.get()
        return ints

    async def reset(self):
        await FallingEdge(self.dut.clk)
        self.dut.soft_int.value = 0
        self.dut.timer_int.value = 0
        self.dut.nmi_int.value = 0
        self.dut.extintsrc_req.value = 0
        await FallingEdge(self.dut.clk)

    async def interrupt_driver_bfm(self):
        self.dut.soft_int.value = 0
        self.dut.timer_int.value = 0
        self.dut.nmi_int.value = 0
        self.dut.extintsrc_req.value = 0
        while True:
            await FallingEdge(self.dut.clk)
            try:
                ints = self.interrupt_driver_queue.get_nowait()
                self.dut.soft_int.value = ints.soft
                self.dut.timer_int.value = ints.timer
                self.dut.nmi_int.value = ints.nmi
                self.dut.extintsrc_req.value = ints.ext
            except QueueEmpty:
                pass

    async def interrupt_source_bfm(self):
        while True:
            await FallingEdge(self.dut.clk)
            item = (
                get_int(self.dut.soft_int),
                get_int(self.dut.timer_int),
                get_int(self.dut.nmi_int),
                get_int(self.dut.extintsrc_req)
            )
            self.interrupt_source_queue.put_nowait(item)

    async def interrupt_trace_bfm(self):
        while True:
            await FallingEdge(self.dut.clk)
            item = get_int(self.dut.trace_rv_i_interrupt_ip)
            self.trace_interrupt_queue.put_nowait(item)

    def start_bfm(self):
        cocotb.start_soon(self.interrupt_driver_bfm())
        cocotb.start_soon(self.interrupt_source_bfm())
        cocotb.start_soon(self.interrupt_trace_bfm())
