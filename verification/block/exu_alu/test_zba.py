# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0
import random

import pyuvm
from cocotb.triggers import ClockCycles
from pyuvm import *
from testbench import BaseSequence, BaseTest

# =============================================================================


@pyuvm.test()
class TestSh1add(BaseTest):
    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = BaseSequence("stimulus", ["sh1add"])

    async def run(self):
        await self.seq.start(self.env.alu_seqr)


@pyuvm.test()
class TestSh2add(BaseTest):
    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = BaseSequence("stimulus", ["sh2add"])

    async def run(self):
        await self.seq.start(self.env.alu_seqr)


@pyuvm.test()
class TestSh3add(BaseTest):
    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = BaseSequence("stimulus", ["sh3add"])

    async def run(self):
        await self.seq.start(self.env.alu_seqr)


@pyuvm.test()
class TestAll(BaseTest):
    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = BaseSequence("stimulus", ["sh1add", "sh2add", "sh3add"])

    async def run(self):
        await self.seq.start(self.env.alu_seqr)
