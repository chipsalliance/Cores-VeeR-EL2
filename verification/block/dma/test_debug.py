# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

import random
import struct

from cocotb.triggers import ClockCycles

import pyuvm
from pyuvm import *

from testbench import BaseEnv, BaseTest
from testbench import BusReadItem, BusWriteItem
from testbench import MemReadItem, MemWriteItem

# =============================================================================


class TestSequence(uvm_sequence):
    """
    """

    def __init__(self, name):
        super().__init__(name)

    async def body(self):

        iccm_base = ConfigDB().get(None, "", "ICCM_BASE")
        iccm_size = ConfigDB().get(None, "", "ICCM_SIZE")

        dccm_base = ConfigDB().get(None, "", "DCCM_BASE")
        dccm_size = ConfigDB().get(None, "", "DCCM_SIZE")

        pic_base  = ConfigDB().get(None, "", "PIC_BASE")
        pic_size  = ConfigDB().get(None, "", "PIC_SIZE")

        # TEST
        for i in range(10):
            item = BusWriteItem(dccm_base,     0xDEADBEEF)
            await self.start_item(item)
            await self.finish_item(item)

            item = BusWriteItem(dccm_base - 4, 0xCAFEBACA)
            await self.start_item(item)
            await self.finish_item(item)

            item = BusReadItem(dccm_base)
            await self.start_item(item)
            await self.finish_item(item)

            item = BusReadItem(dccm_base + 4)
            await self.start_item(item)
            await self.finish_item(item)

# =============================================================================


class TestEnv(BaseEnv):
    def build_phase(self):
        super().build_phase()

    def connect_phase(self):
        super().connect_phase()

# =============================================================================


@pyuvm.test()
class TestDebug(BaseTest):
    """
    """

    def __init__(self, name, parent):
        super().__init__(name, parent, TestEnv)

    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = TestSequence.create("stimulus")

    async def run(self):
        await self.seq.start(self.env.dbg_seqr)

