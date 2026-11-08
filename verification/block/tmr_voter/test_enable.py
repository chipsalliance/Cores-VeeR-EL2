# Copyright (c) 2026 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0
import random

from pyuvm import ConfigDB, test, uvm_sequence
from testbench import (
    BaseTest,
    DriverItem,
    MuBiFalse,
    MuBiTrue,
)

# =============================================================================


class TestSequence(uvm_sequence):
    """
    Randomly enabled inputs while driving the same data to all of them.
    Occassionaly drives different data to the disabled one(s).
    """

    def __init__(self, name):
        super().__init__(name)

        self.seqr = ConfigDB().get(None, "", "SEQR")

    async def body(self):
        iter = ConfigDB().get(None, "", "TEST_ITERATIONS")
        width = 8  # FIXME: Sync with makefile

        # Drive all inputs, occasionally disable some
        for i in range(iter):
            it = DriverItem()

            # Drive data
            value = random.randrange(0, 1 << width)
            it.signals["in_a"] = value
            it.signals["in_b"] = value
            it.signals["in_c"] = value

            # Randomize enable
            it.signals["en_a"] = MuBiTrue if random.random() < 0.9 else MuBiFalse
            it.signals["en_b"] = MuBiTrue if random.random() < 0.9 else MuBiFalse
            it.signals["en_c"] = MuBiTrue if random.random() < 0.9 else MuBiFalse

            # For each disabled input randomize its value occassionaly
            for sig in ["a", "b", "c"]:
                if it.signals["en_" + sig] == MuBiFalse and random.random() < 0.25:
                    it.signals["in_" + sig] = random.randrange(0, 1 << width)

            # Send the item
            await self.seqr.start_item(it)
            await self.seqr.finish_item(it)


# ==============================================================================


@test()
class TestEnable(BaseTest):
    def __init__(self, name, parent):
        super().__init__(name, parent, TestSequence)
