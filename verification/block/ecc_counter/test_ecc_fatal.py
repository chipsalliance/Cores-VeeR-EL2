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
        did_fatal = False

        for i in range(iter):
            for n, ctrl in [(10, "inc_i"), (5, "dec_i")]:
                for j in range(n):

                    # Didn't do a fatal injection. Randomize it
                    if not did_fatal:
                        if random.random() < 0.1:
                            upset_bits = random.sample(range(13), 2)
                        else:
                            upset_bits = None

                    # Did a fatal injection. Randomize clearing it
                    else:
                        upset_bits = None
                        did_fatal = False

                        if random.random() < 0.1:
                            for v in [1, 0]:
                                it = DriverItem()
                                it.signals["clr_i"] = v
                                await self.seqr.start_item(it)
                                await self.seqr.finish_item(it)

                    # Assert control
                    it = DriverItem()
                    it.signals[ctrl] = 1

                    # .. and force storage bits
                    if upset_bits is not None:
                        for bit in upset_bits:
                            v = random.choice([0, 1])
                            it.signals[f"storage[{bit}]"] = Force(v)

                    await self.seqr.start_item(it)
                    await self.seqr.finish_item(it)

                    # Deassert control
                    it = DriverItem()
                    it.signals[ctrl] = 0

                    # .. and release storage bits
                    if upset_bits is not None:
                        for bit in upset_bits:
                            it.signals[f"storage[{bit}]"] = Release()

                    await self.seqr.start_item(it)
                    await self.seqr.finish_item(it)

                    if upset_bits is not None:
                        did_fatal = True


# ==============================================================================


@test()
class TestEccFatal(BaseTest):
    def __init__(self, name, parent):
        super().__init__(name, parent, TestSequence)
