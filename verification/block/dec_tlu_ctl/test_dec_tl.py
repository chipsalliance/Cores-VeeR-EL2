# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0
import random

import pyuvm
from cocotb.triggers import ClockCycles
from pyuvm import *
from testbench import BaseTest, TlSequence

# =============================================================================


@pyuvm.test()
class TestMeihap(BaseTest):
    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        ConfigDB().set(None, "*", "TEST", "meihap")
        self.seq = TlSequence("stimulus")

    async def run(self):
        await self.seq.start(self.env.tl_seqr)


@pyuvm.test()
class TestMtdata(BaseTest):
    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        ConfigDB().set(None, "*", "TEST", "mtdata")
        self.seq = TlSequence("stimulus")

    async def run(self):
        await self.seq.start(self.env.tl_seqr)


@pyuvm.test()
class TestCsrAccess(BaseTest):
    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        ConfigDB().set(None, "*", "TEST", "csrs_access")
        self.seq = TlSequence("stimulus")

    async def run(self):
        await self.seq.start(self.env.tl_seqr)


@pyuvm.test()
class TestDebugCSRs(BaseTest):
    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        ConfigDB().set(None, "*", "TEST", "debug_csrs_access")
        self.seq = TlSequence("stimulus")

    async def run(self):
        await self.seq.start(self.env.tl_seqr)
