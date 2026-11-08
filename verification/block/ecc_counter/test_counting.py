# Copyright (c) 2026 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0
import random

from pyuvm import ConfigDB, test, uvm_sequence
from testbench import (
    BaseTest,
    DriverItem,
)

# =============================================================================


class TestSequence(uvm_sequence):
    """
    Randomly pulse counter control signals
    """

    def __init__(self, name):
        super().__init__(name)

        self.seqr = ConfigDB().get(None, "", "SEQR")

    async def body(self):
        iter = ConfigDB().get(None, "", "TEST_ITERATIONS")

        signals = ["inc_i", "dec_i", "clr_i"]
        for i in range(iter):

            # Choose a signal to pulse
            signal = random.choice(signals)

            # Pulse
            it = DriverItem()
            it.signals[signal] = 1

            await self.seqr.start_item(it)
            await self.seqr.finish_item(it)

            it = DriverItem()
            it.signals[signal] = 0

            await self.seqr.start_item(it)
            await self.seqr.finish_item(it)


# ==============================================================================


@test()
class TestCounting(BaseTest):
    def __init__(self, name, parent):
        super().__init__(name, parent, TestSequence)
