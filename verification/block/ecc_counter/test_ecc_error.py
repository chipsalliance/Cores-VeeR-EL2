# Copyright (c) 2026 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0
import random

from cocotb.handle import Force, Release
from pyuvm import ConfigDB, test, uvm_sequence
from testbench import (
    BaseTest,
    DriverItem,
)

# =============================================================================


class TestSequence(uvm_sequence):
    def __init__(self, name):
        super().__init__(name)

        self.seqr = ConfigDB().get(None, "", "SEQR")

    async def body(self):
        iter = ConfigDB().get(None, "", "TEST_ITERATIONS")

        for i in range(iter):
            for n, ctrl in [(10, "inc_i"), (5, "dec_i")]:
                for j in range(n):

                    if random.random() < 0.1:
                        upset_bit = random.randint(0, 12)
                    else:
                        upset_bit = None

                    # Assert control
                    it = DriverItem()
                    it.signals[ctrl] = 1

                    # .. and force storage bit
                    if upset_bit is not None:
                        v = random.choice([0, 1])
                        it.signals[f"storage[{upset_bit}]"] = Force(v)

                    await self.seqr.start_item(it)
                    await self.seqr.finish_item(it)

                    # Deassert control
                    it = DriverItem()
                    it.signals[ctrl] = 0

                    # .. and release storage bit
                    if upset_bit is not None:
                        it.signals[f"storage[{upset_bit}]"] = Release()

                    await self.seqr.start_item(it)
                    await self.seqr.finish_item(it)


# ==============================================================================


@test()
class TestEccError(BaseTest):
    def __init__(self, name, parent):
        super().__init__(name, parent, TestSequence)
