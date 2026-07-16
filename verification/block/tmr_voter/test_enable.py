# Copyright (c) 2026 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0
import random

from pyuvm import ConfigDB, test, uvm_sequence
from testbench import (
    BaseTest,
    BaseScoreboard,
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
        iter  = ConfigDB().get(None, "", "TEST_ITERATIONS")
        width = 8 # FIXME: Sync with makefile

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


class Scoreboard(BaseScoreboard):
    """
    Checks fault reporting
    """

    def check_phase(self):
        self.passed = True

        while self.port.can_get():
            _, it = self.port.try_get()
            self.logger.debug(str(it))

            en_a = it.signals["en_a"] == MuBiTrue
            en_b = it.signals["en_b"] == MuBiTrue
            en_c = it.signals["en_c"] == MuBiTrue

            fault_a = it.signals["fault_a"]
            fault_b = it.signals["fault_b"]
            fault_c = it.signals["fault_c"]

            # All 3 disabled
            if not en_a and not en_b and not en_c:
                assert fault_a == MuBiFalse
                assert fault_b == MuBiFalse
                assert fault_c == MuBiFalse

            # Two inputs disabled
            elif not en_a and not en_b and en_c:
                assert fault_a == MuBiFalse
                assert fault_b == MuBiFalse
                assert fault_c == MuBiTrue

            elif en_a and not en_b and not en_c:
                assert fault_a == MuBiTrue
                assert fault_b == MuBiFalse
                assert fault_c == MuBiFalse

            elif not en_a and en_b and not en_c:
                assert fault_a == MuBiFalse
                assert fault_b == MuBiTrue
                assert fault_c == MuBiFalse

            # In all other cases no error shall be reported provided that all
            # the enabled inputs match
            else:
                assert fault_a == MuBiFalse
                assert fault_b == MuBiFalse
                assert fault_c == MuBiFalse

                # Output should be equal to any non-disabled input
                ins = []
                if en_a:
                    ins.append(it.signals["in_a"])
                if en_b:
                    ins.append(it.signals["in_b"])
                if en_c:
                    ins.append(it.signals["in_c"])

                val = random.choice(ins)
                assert val == it.signals["out"]

            # Check MuBi
            assert it.signals["fault_a"] in [MuBiTrue, MuBiFalse]
            assert it.signals["fault_b"] in [MuBiTrue, MuBiFalse]
            assert it.signals["fault_c"] in [MuBiTrue, MuBiFalse]


# ==============================================================================


@test()
class TestEnable(BaseTest):
    def __init__(self, name, parent):
        super().__init__(name, parent, TestSequence, Scoreboard)
