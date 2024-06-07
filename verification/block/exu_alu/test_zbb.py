# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0
import random

import pyuvm
from cocotb.triggers import ClockCycles
from pyuvm import *
from testbench import BaseSequence, BaseTest

# =============================================================================


@pyuvm.test()
class TestClz(BaseTest):
    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = BaseSequence("stimulus", ["clz"])

    async def run(self):
        await self.seq.start(self.env.alu_seqr)


@pyuvm.test()
class TestCtz(BaseTest):
    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = BaseSequence("stimulus", ["ctz"])

    async def run(self):
        await self.seq.start(self.env.alu_seqr)


@pyuvm.test()
class TestCpop(BaseTest):
    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = BaseSequence("stimulus", ["cpop"])

    async def run(self):
        await self.seq.start(self.env.alu_seqr)


@pyuvm.test()
class TestSextb(BaseTest):
    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = BaseSequence("stimulus", ["sext_b"])

    async def run(self):
        await self.seq.start(self.env.alu_seqr)


@pyuvm.test()
class TestSexth(BaseTest):
    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = BaseSequence("stimulus", ["sext_h"])

    async def run(self):
        await self.seq.start(self.env.alu_seqr)


@pyuvm.test()
class TestRol(BaseTest):
    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = BaseSequence("stimulus", ["rol"])

    async def run(self):
        await self.seq.start(self.env.alu_seqr)


@pyuvm.test()
class TestRor(BaseTest):
    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = BaseSequence("stimulus", ["ror"])

    async def run(self):
        await self.seq.start(self.env.alu_seqr)


@pyuvm.test()
class TestAll(BaseTest):
    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = BaseSequence(
            "stimulus", ["clz", "ctz", "cpop", "sext_b", "sext_h", "rol", "ror"]
        )

    async def run(self):
        await self.seq.start(self.env.alu_seqr)
