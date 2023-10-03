# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0
import random

import pyuvm
from cocotb.triggers import ClockCycles
from pyuvm import *
from testbench import BaseSequence, BaseTest

# =============================================================================


@pyuvm.test()
class TestAnd(BaseTest):
    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = BaseSequence("stimulus", ["and"])

    async def run(self):
        await self.seq.start(self.env.alu_seqr)


@pyuvm.test()
class TestOr(BaseTest):
    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = BaseSequence("stimulus", ["or"])

    async def run(self):
        await self.seq.start(self.env.alu_seqr)


@pyuvm.test()
class TestXor(BaseTest):
    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = BaseSequence("stimulus", ["xor"])

    async def run(self):
        await self.seq.start(self.env.alu_seqr)


@pyuvm.test()
class TestAll(BaseTest):
    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = BaseSequence("stimulus", ["and", "or", "xor"])

    async def run(self):
        await self.seq.start(self.env.alu_seqr)
