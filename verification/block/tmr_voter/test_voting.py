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
    With all 3 inputs enabled drives the same data on all of them occasionally
    injecting an error.
    """

    def __init__(self, name):
        super().__init__(name)

        self.seqr = ConfigDB().get(None, "", "SEQR")

    async def body(self):
        iter = ConfigDB().get(None, "", "TEST_ITERATIONS")
        width = 8  # FIXME: Sync with makefile

        # Drive all inputs, occasionally inject 1 error
        for i in range(iter):
            it = DriverItem()

            # Enable all 3 inputs
            it.signals["en_a"] = MuBiTrue
            it.signals["en_b"] = MuBiTrue
            it.signals["en_c"] = MuBiTrue

            # Base data value
            value = random.randrange(0, 1 << width)
            it.signals["in_a"] = value
            it.signals["in_b"] = value
            it.signals["in_c"] = value

            # Make a random fault
            if random.random() < 0.25:

                # Fault count
                n = 2 if random.random() < 0.25 else 1

                # Inject
                which = random.sample(["in_a", "in_b", "in_c"], k=n)
                for sig in which:
                    upset = random.randrange(0, 1 << width)
                    it.signals[sig] = upset

            # Send the item
            await self.seqr.start_item(it)
            await self.seqr.finish_item(it)


# ==============================================================================


@test()
class TestVoting(BaseTest):
    def __init__(self, name, parent):
        super().__init__(name, parent, TestSequence)
