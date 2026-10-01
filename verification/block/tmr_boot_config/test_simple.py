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
    def __init__(self, name):
        super().__init__(name)

        self.seqr = ConfigDB().get(None, "", "SEQR")

    async def body(self):
        iter = ConfigDB().get(None, "", "TEST_ITERATIONS")

        # Drive all inputs, occasionally disable some
        for i in range(iter):
            it = DriverItem()

            it.signals["rst_l"] = random.choice([0, 1])
            it.signals["activate_core"] = [random.choice([MuBiTrue, MuBiFalse]) for _ in range(3)]

            # Send the item
            await self.seqr.start_item(it)
            await self.seqr.finish_item(it)


# ==============================================================================


@test()
class TestSimple(BaseTest):
    def __init__(self, name, parent):
        super().__init__(name, parent, TestSequence)
