# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0
import random

import pyuvm
from cocotb.triggers import ClockCycles
from pyuvm import *
from testbench import BaseTest, IbCtlSequence

# =============================================================================


@pyuvm.test()
class TestIbCtlLogic(BaseTest):
    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = IbCtlSequence("stimulus")

    async def run_phase(self):
        self.raise_objection()

        # Run the actual test
        await self.run()

        self.drop_objection()

    async def run(self):
        await self.seq.start(self.env.seqr)
