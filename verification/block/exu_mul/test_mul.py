# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0
import random

import pyuvm
from cocotb.triggers import ClockCycles
from pyuvm import *
from testbench import BaseSequence, BaseTest

# =============================================================================


@pyuvm.test()
class TestMul(BaseTest):
    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = BaseSequence("stimulus", ["mul"])

    async def run(self):
        await self.seq.start(self.env.mul_seqr)
