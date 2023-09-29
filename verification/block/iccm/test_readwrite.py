# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0
import random

import pyuvm
from pyuvm import *
from testbench import BaseTest, MemReadItem, MemWriteItem

# =============================================================================


class ReadWriteSequence(uvm_sequence):
    """
    A sequencer that issues a random sequence of writes followed by a
    randomized sequence of reads containing the same addresses previously
    written to.
    """

    def __init__(self, name):
        super().__init__(name)

    async def body(self):
        count = ConfigDB().get(None, "", "TEST_ITERATIONS")
        burst = ConfigDB().get(None, "", "TEST_BURST_LEN")

        awidth = (
            ConfigDB().get(None, "", "ICCM_BITS") - 1
        )  # Address input declared as [pt.ICCM_BITS-1:1]
        dwidth = 64  # Fixed

        for i in range(count):
            # Randomize unique addresses (aligned to 8)
            addrs = set([random.randrange(0, 1 << awidth) & ~7 for i in range(burst)])

            # Issue writes, randomize data
            for addr in addrs:
                data = random.randrange(0, 1 << dwidth)

                item = MemWriteItem(addr, data)
                await self.start_item(item)
                await self.finish_item(item)

            # Issue random reads for written addresses
            addrs = list(set(addrs))
            random.shuffle(addrs)
            for addr in addrs:
                item = MemReadItem(addr, data)
                await self.start_item(item)
                await self.finish_item(item)


@pyuvm.test()
class TestReadWrite(BaseTest):
    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = ReadWriteSequence("stimulus")

    async def run(self):
        await self.seq.start(self.env.mem_seqr)
