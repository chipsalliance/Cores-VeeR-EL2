# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

import random
import struct
from collections import defaultdict

from cocotb.triggers import ClockCycles

import pyuvm
from pyuvm import *

from testbench import BaseEnv, BaseTest
from testbench import BusReadItem, BusWriteItem
from scoreboards import WriteScoreboard

# =============================================================================


class TestSequenceDCCM(uvm_sequence):
    """
    A sequence of random DCCM writes
    """

    def __init__(self, name):
        super().__init__(name)

    async def body(self):

        dccm_base = ConfigDB().get(None, "", "DCCM_BASE")
        dccm_size = ConfigDB().get(None, "", "DCCM_SIZE")

        align = ConfigDB().get(None, "", "ADDR_ALIGN")

        for j in range(4):
            for i in range(6):

                addr = dccm_base + random.randrange(0, dccm_size)
                addr = (addr // align) * align
                data = random.randrange(0, (1 << 32) - 1)

                item = BusWriteItem(addr, data)
                await self.start_item(item)
                await self.finish_item(item)

            await ClockCycles(cocotb.top.clk, 5)


class TestSequenceICCM(uvm_sequence):
    """
    A sequence of random ICCM writes
    """

    def __init__(self, name):
        super().__init__(name)

    async def body(self):

        iccm_base = ConfigDB().get(None, "", "ICCM_BASE")
        iccm_size = ConfigDB().get(None, "", "ICCM_SIZE")

        align = ConfigDB().get(None, "", "ADDR_ALIGN")

        for j in range(4):
            for i in range(6):

                addr = iccm_base + random.randrange(0, iccm_size)
                addr = (addr // align) * align
                data = random.randrange(0, (1 << 32) - 1)

                item = BusWriteItem(addr, data)
                await self.start_item(item)
                await self.finish_item(item)

            await ClockCycles(cocotb.top.clk, 5)


class TestSequenceBoth(uvm_sequence):
    """
    A sequence of random ICCM or DCCM writes
    """

    def __init__(self, name):
        super().__init__(name)

    async def body(self):

        iccm_base = ConfigDB().get(None, "", "ICCM_BASE")
        iccm_size = ConfigDB().get(None, "", "ICCM_SIZE")

        dccm_base = ConfigDB().get(None, "", "DCCM_BASE")
        dccm_size = ConfigDB().get(None, "", "DCCM_SIZE")

        align = ConfigDB().get(None, "", "ADDR_ALIGN")

        for j in range(4):
            for i in range(6):

                mem_base, mem_size = random.choice([
                    (iccm_base, iccm_size),
                    (dccm_base, dccm_size),
                ])

                addr = mem_base + random.randrange(0, mem_size)
                addr = (addr // align) * align
                data = random.randrange(0, (1 << 32) - 1)

                item = BusWriteItem(addr, data)
                await self.start_item(item)
                await self.finish_item(item)

            await ClockCycles(cocotb.top.clk, 5)


# =============================================================================


class TestEnv(BaseEnv):
    def build_phase(self):
        super().build_phase()

        # Add scoreboard
        self.scoreboard = WriteScoreboard("scoreboard", self)

    def connect_phase(self):
        super().connect_phase()

        # Connect monitors
        self.dbg_mon.ap.connect(self.scoreboard.fifo.analysis_export)
        self.mem_mon.ap.connect(self.scoreboard.fifo.analysis_export)

# =============================================================================


@pyuvm.test()
class TestDCCMWrite(BaseTest):
    """
    DCCM write test
    """

    def __init__(self, name, parent):
        super().__init__(name, parent, TestEnv)

    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = TestSequenceDCCM.create("stimulus")

    async def run(self):
        await self.seq.start(self.env.dbg_seqr)


@pyuvm.test()
class TestICCMWrite(BaseTest):
    """
    ICCM write test
    """

    def __init__(self, name, parent):
        super().__init__(name, parent, TestEnv)

    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = TestSequenceICCM.create("stimulus")

    async def run(self):
        await self.seq.start(self.env.dbg_seqr)


@pyuvm.test()
class TestBothWrite(BaseTest):
    """
    Randomized DCCM/ICCM write test
    """

    def __init__(self, name, parent):
        super().__init__(name, parent, TestEnv)

    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = TestSequenceBoth.create("stimulus")

    async def run(self):
        await self.seq.start(self.env.dbg_seqr)
