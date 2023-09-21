# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0


import pyuvm
from cocotb.triggers import ClockCycles
from pyuvm import *
from scoreboards import ReadScoreboard
from sequences import AnyMemReadSequence, MemReadSequence
from testbench import BaseEnv, BaseTest, BusReadItem, BusWriteItem

# =============================================================================


class TestEnv(BaseEnv):
    def build_phase(self):
        super().build_phase()

        # Add scoreboard
        self.scoreboard = ReadScoreboard("scoreboard", self)

    def connect_phase(self):
        super().connect_phase()

        # Connect monitors
        self.dbg_mon.ap.connect(self.scoreboard.fifo.analysis_export)
        self.mem_mon.ap.connect(self.scoreboard.fifo.analysis_export)


# =============================================================================


@pyuvm.test()
class TestDCCMRead(BaseTest):
    """
    DCCM write test
    """

    def __init__(self, name, parent):
        super().__init__(name, parent, TestEnv)

    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = MemReadSequence("stimulus", "DCCM")

    async def run(self):
        await self.seq.start(self.env.dbg_seqr)


@pyuvm.test()
class TestICCMRead(BaseTest):
    """
    ICCM write test
    """

    def __init__(self, name, parent):
        super().__init__(name, parent, TestEnv)

    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = MemReadSequence("stimulus", "ICCM")

    async def run(self):
        await self.seq.start(self.env.dbg_seqr)


@pyuvm.test()
class TestBothRead(BaseTest):
    """
    Randomized DCCM/ICCM write test
    """

    def __init__(self, name, parent):
        super().__init__(name, parent, TestEnv)

    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = AnyMemReadSequence("stimulus")

    async def run(self):
        await self.seq.start(self.env.dbg_seqr)
