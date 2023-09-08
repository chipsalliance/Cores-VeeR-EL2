# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0
import random

import pyuvm
from pyuvm import *
from testbench import BaseEnv, BaseTest, BusReadItem, BusWriteItem

# =============================================================================


class TestSequence(uvm_sequence):
    """ """

    def __init__(self, name):
        super().__init__(name)

    async def body(self):
        item = BusWriteItem(0xF0040000, 0xDEADBEEF)
        await self.start_item(item)
        await self.finish_item(item)

        # TODO: This is just for testing
        item = BusReadItem(0xF0040000)
        await self.start_item(item)
        await self.finish_item(item)


# =============================================================================


class TestEnv(BaseEnv):
    def build_phase(self):
        super().build_phase()

    def connect_phase(self):
        super().connect_phase()


@pyuvm.test()
class TestDmaWrite(BaseTest):
    """ """

    def __init__(self, name, parent):
        super().__init__(name, parent, TestEnv)

    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = TestSequence.create("stimulus")

    async def run(self):
        await self.seq.start(self.env.axi_seqr)
