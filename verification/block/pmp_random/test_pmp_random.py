# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0
import random

import pyuvm
from cocotb.triggers import ClockCycles
from pyuvm import *
from testbench import BaseTest, InputItem

# =============================================================================


class PMPRandomLegalSequence(uvm_sequence):
    """ """

    def __init__(self, name):
        super().__init__(name)

    def legalize_pmpcfg(self, item):
        """
        Leave only A, X and R fields as any combination of them is legal and
        does not influence PMPADDR access. Setting L would interfere with the
        test.
        """
        mask = 0b00011101
        item.cfg &= (mask << 24) | (mask << 16) | (mask << 8) | mask

    def legalize_pmpaddr(self, item):
        """
        Mask out two MSBs
        """
        item.pmp_addr &= 0x3FFFFFFF

    async def body(self):

        # Run
        count = ConfigDB().get(None, "", "TEST_ITERATIONS")

        for i in range(count):
            item = InputItem()
            item.randomize()
            self.legalize_pmpaddr(item)
            self.legalize_pmpcfg(item)

            await self.start_item(item)
            await self.finish_item(item)


@pyuvm.test()
class TestRandomPMP(BaseTest):
    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        count = ConfigDB().get(None, "", "TEST_ITERATIONS")
        self.seq = [PMPRandomLegalSequence("stimulus") for i in range(count)]

    async def run(self):
        for seq in self.seq:
            await seq.start(self.env.pmp_wr_seqr)
