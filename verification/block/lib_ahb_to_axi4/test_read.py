# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

import random

import pyuvm
from pyuvm import *

from cocotb.triggers import ClockCycles

from testbench import BaseEnv, BaseTest
from testbench import BusWriteItem, BusReadItem

# =============================================================================

class AHBReadSequence(uvm_sequence):
    """
    """

    def __init__(self, name):
        super().__init__(name)

    async def body(self):

        count  = ConfigDB().get(None, "", "TEST_ITERATIONS")
        gap    = ConfigDB().get(None, "", "TEST_BURST_GAP")

        dwidth = 64
        align  = 8

        for i in range(count):
            addr = 0xF0040000 + random.randrange(0, 0x1000)
            addr = (addr // align) * align

            # Issue a single read, the converter module does not support
            # bursts
            item = BusReadItem(addr)

            await self.start_item(item)
            await self.finish_item(item)

            await ClockCycles(cocotb.top.clk, gap)

# =============================================================================

@pyuvm.test()
class TestRead(BaseTest):
    """
    AHB Lite to AXI4 Lite read test
    """

    def __init__(self, name, parent):
        super().__init__(name, parent)

    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = AHBReadSequence("stimulus")

    async def run(self):
        await self.seq.start(self.env.ahb_seqr)
