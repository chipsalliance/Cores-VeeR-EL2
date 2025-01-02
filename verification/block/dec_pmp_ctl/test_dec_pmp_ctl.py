# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0
import random

import pyuvm
from cocotb.triggers import ClockCycles
from pyuvm import *
from testbench import BaseTest, Sequence

# =============================================================================


@pyuvm.test()
class TestCsrWriteAddress(BaseTest):
    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = Sequence("stimulus")

    async def run(self):
        await self.seq.start(self.env.pmp_seqr)
