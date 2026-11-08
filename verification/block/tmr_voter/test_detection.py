# Copyright (c) 2026 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0
import random

from pyuvm import ConfigDB, test, uvm_sequence
from testbench import (
    BaseScoreboard,
    BaseTest,
    DriverItem,
    MuBiFalse,
    MuBiTrue,
)

# =============================================================================


class TestSequence(uvm_sequence):
    """
    Enable exactly 2 random inputs. Drive the same value to them. Occassionaly
    do an upsed by driving one of the enable inputs with a different value.
    """

    def __init__(self, name):
        super().__init__(name)

        self.seqr = ConfigDB().get(None, "", "SEQR")

    async def body(self):
        iter = ConfigDB().get(None, "", "TEST_ITERATIONS")
        width = 8  # FIXME: Sync with makefile

        for i in range(iter):
            it = DriverItem()

            # Enable 2 inputs
            signals = ["en_a", "en_b", "en_c"]
            enabled = random.sample(signals, k=2)
            for sig in signals:
                it.signals[sig] = MuBiTrue if sig in enabled else MuBiFalse

            # Base data value
            value = random.randrange(0, 1 << width)
            it.signals["in_a"] = value
            it.signals["in_b"] = value
            it.signals["in_c"] = value

            if random.random() < 0.25:
                upset = random.randrange(0, 1 << width)
                which = random.choice(enabled).replace("en_", "in_")

                it.signals[which] = upset

            # Send the item
            await self.seqr.start_item(it)
            await self.seqr.finish_item(it)


# ==============================================================================


@test()
class TestDetection(BaseTest):
    def __init__(self, name, parent):
        super().__init__(name, parent, TestSequence)
