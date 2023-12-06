# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

import random

import pyuvm
from cocotb.triggers import ClockCycles, Combine
from pyuvm import *
from testbench import (
    AXI4LiteReadyItem,
    AXI4LiteResponseItem,
    BaseEnv,
    BaseTest,
    BusReadItem,
)

# =============================================================================


class AHBReadSequence(uvm_sequence):
    def __init__(self, name):
        super().__init__(name)

    async def body(self):
        align = 8

        addr = 0xF0040000 + random.randrange(0, 0x1000)
        addr = (addr // align) * align

        item = BusReadItem(addr)
        await self.start_item(item)
        await self.finish_item(item)


class AXI4LiteReadResponseSequence(uvm_sequence):
    def __init__(self, name):
        super().__init__(name)

    async def body(self):
        # Respond to AR
        item = AXI4LiteResponseItem(["ar"])
        await self.start_item(item)
        await self.finish_item(item)

        # Emulate latency
        await ClockCycles(cocotb.top.clk, 2)

        # Respond on R
        item = AXI4LiteResponseItem(["r"])
        await self.start_item(item)
        await self.finish_item(item)


class AXI4LiteNoReadDataResponseSequence(uvm_sequence):
    def __init__(self, name):
        super().__init__(name)

    async def body(self):
        # Respond to AR but not to R
        item = AXI4LiteResponseItem(["ar"])
        await self.start_item(item)
        await self.finish_item(item)


# =============================================================================


class AXI4LiteReadReadySequence(uvm_sequence):
    def __init__(self, name):
        super().__init__(name)

    async def body(self):
        # Become ready
        item = AXI4LiteReadyItem(["ar"], True)
        await self.start_item(item)
        await self.finish_item(item)


# =============================================================================


async def later(cr, cycles):
    """
    A helper function to start a task after a number of clock cycles
    """
    await ClockCycles(cocotb.top.clk, cycles)
    await cr


class NoBackpressureReadSequence(uvm_sequence):
    async def body(self):
        ahb_seqr = ConfigDB().get(None, "", "AHB_SEQR")
        axi_seqr = ConfigDB().get(None, "", "AXI_SEQR")

        axi_rdy = AXI4LiteReadReadySequence("ready")
        ahb_seq = AHBReadSequence("stimulus")
        axi_seq = AXI4LiteReadResponseSequence("response")

        # Issue an AHB read and do a correct AXI response
        await axi_rdy.start(axi_seqr)

        tasks = [
            cocotb.start_soon(ahb_seq.start(ahb_seqr)),
            cocotb.start_soon(axi_seq.start(axi_seqr)),
        ]
        await Combine(*tasks)


class BackpressureReadSequence(uvm_sequence):
    async def body(self):
        ahb_seqr = ConfigDB().get(None, "", "AHB_SEQR")
        axi_seqr = ConfigDB().get(None, "", "AXI_SEQR")

        ahb_seq = AHBReadSequence("stimulus")
        axi_seq = AXI4LiteReadResponseSequence("response")

        # Issue an AHB read and do a correct AXI response
        tasks = [
            cocotb.start_soon(ahb_seq.start(ahb_seqr)),
            cocotb.start_soon(later(axi_seq.start(axi_seqr), 5)),
        ]
        await Combine(*tasks)


class NoReadDataResponseSequence(uvm_sequence):
    async def body(self):
        ahb_seqr = ConfigDB().get(None, "", "AHB_SEQR")
        axi_seqr = ConfigDB().get(None, "", "AXI_SEQR")

        axi_rdy = AXI4LiteReadReadySequence("ready")
        ahb_seq = AHBReadSequence("stimulus")
        axi_seq = AXI4LiteNoReadDataResponseSequence("response")

        # Issue an AHB read and do a correct AXI response
        await axi_rdy.start(axi_seqr)

        tasks = [
            cocotb.start_soon(ahb_seq.start(ahb_seqr)),
            cocotb.start_soon(axi_seq.start(axi_seqr)),
        ]
        await Combine(*tasks)


# =============================================================================


@pyuvm.test()
class TestReadNoBackpressure(BaseTest):
    """
    Read test with no AXI backpressure
    """

    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = NoBackpressureReadSequence()

    async def run(self):
        count = ConfigDB().get(None, "", "TEST_ITERATIONS")
        gap = ConfigDB().get(None, "", "TEST_BURST_GAP")

        for i in range(count):
            await self.seq.start()
            await ClockCycles(cocotb.top.clk, gap)


@pyuvm.test()
class TestReadBackpressure(BaseTest):
    """
    Read test with AXI backpressure
    """

    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = BackpressureReadSequence()

    async def run(self):
        count = ConfigDB().get(None, "", "TEST_ITERATIONS")
        gap = ConfigDB().get(None, "", "TEST_BURST_GAP")

        for i in range(count):
            await self.seq.start()
            await ClockCycles(cocotb.top.clk, gap)


@pyuvm.test(expect_error=TimeoutError)
class TestReadNoDataResponse(BaseTest):
    """
    Read test with response on AR channel but not on R channel. A timeout should
    occur due to lack of the response.
    """

    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = NoReadDataResponseSequence()

    async def run(self):
        count = ConfigDB().get(None, "", "TEST_ITERATIONS")
        gap = ConfigDB().get(None, "", "TEST_BURST_GAP")

        for i in range(count):
            await self.seq.start()
            await ClockCycles(cocotb.top.clk, gap)
