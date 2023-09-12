# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

import random
import struct

from cocotb.triggers import ClockCycles

import pyuvm
from pyuvm import *

from testbench import BaseEnv, BaseTest
from testbench import BusReadItem, BusWriteItem
from scoreboards import AccessScoreboard

# =============================================================================


class TestSequenceRange(uvm_sequence):
    """
    A sequencer that generates random bus read/write requests to addresses
    outside the range accepted by the DMA module
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

        align = ConfigDB().get(None, "", "ADDR_ALIGN")

        for j in range(50):

            # Crude address randomizer
            while True:
                addr = random.randrange(0, (1 << 32) - 1)
                addr = (addr // align) * align

                if addr >= iccm_base and addr < iccm_base + iccm_size:
                    continue
                if addr >= dccm_base and addr < dccm_base + dccm_size:
                    continue
                if addr >= pic_base  and addr < pic_base  + pic_size:
                    continue

                break

            # Randomize read/write
            if random.random() >= 0.5:
                item = BusReadItem(addr)
            else:
                data = random.randrange(0, (1 << 32) - 1)
                item = BusWriteItem(addr, data)

            await self.start_item(item)
            await self.finish_item(item)


# =============================================================================


class TestEnv(BaseEnv):
    def build_phase(self):
        super().build_phase()

        # Add scoreboard
        self.scoreboard = AccessScoreboard("scoreboard", self)

    def connect_phase(self):
        super().connect_phase()

        # Connect monitors
        self.dbg_mon.ap.connect(self.scoreboard.fifo.analysis_export)
        self.mem_mon.ap.connect(self.scoreboard.fifo.analysis_export)

# =============================================================================


@pyuvm.test()
class TestAddressOutOfRange(BaseTest):
    """
    Out of range addressing test
    """

    def __init__(self, name, parent):
        super().__init__(name, parent, TestEnv)

    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = TestSequenceRange.create("stimulus")

    async def run(self):
        await self.seq.start(self.env.dbg_seqr)

