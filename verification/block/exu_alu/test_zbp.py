# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0
import random

import pyuvm
from cocotb.triggers import ClockCycles
from pyuvm import *
from testbench import BaseSequence, BaseTest

# =============================================================================


@pyuvm.test()
class TestPack(BaseTest):
    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = BaseSequence("stimulus", ["pack"])

    async def run(self):
        await self.seq.start(self.env.alu_seqr)


@pyuvm.test()
class TestPackh(BaseTest):
    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = BaseSequence("stimulus", ["packh"])

    async def run(self):
        await self.seq.start(self.env.alu_seqr)


@pyuvm.test()
class TestAll(BaseTest):
    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = BaseSequence("stimulus", ["pack", "packh"])

    async def run(self):
        await self.seq.start(self.env.alu_seqr)
