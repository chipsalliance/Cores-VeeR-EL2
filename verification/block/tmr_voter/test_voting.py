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
    With all 3 inputs enabled drives the same data on all of them occasionally
    injecting an error.
    """
    def __init__(self, name):
        super().__init__(name)

        self.seqr = ConfigDB().get(None, "", "SEQR")

    async def body(self):
        iter  = ConfigDB().get(None, "", "TEST_ITERATIONS")
        width = 8 # FIXME: Sync with makefile

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

            # Make a single random fault
            if random.random() < 0.25:
                upset = random.randrange(0, 1 << width)
                which = random.choice(["in_a", "in_b", "in_c"])

                it.signals[which] = upset

            # Send the item
            await self.seqr.start_item(it)
            await self.seqr.finish_item(it)


# ==============================================================================


class Scoreboard(BaseScoreboard):
    """
    Checks if majority voting works and that failures are reported
    correctly
    """

    def check_phase(self):
        self.passed = True

        while self.port.can_get():
            _, it = self.port.try_get()
            self.logger.debug(str(it))

            # At least one input is disabled. Skip
            if it.signals["en_a"] != MuBiTrue or \
               it.signals["en_b"] != MuBiTrue or \
               it.signals["en_c"] != MuBiTrue:
               continue

            # Get inputs, do the voting. Assume that all are enabled
            in_a = it.signals["in_a"]
            in_b = it.signals["in_b"]
            in_c = it.signals["in_c"]

            # Predict
            pred_out     = None
            pred_fault_a = MuBiFalse
            pred_fault_b = MuBiFalse
            pred_fault_c = MuBiFalse

            if   in_a != in_b and in_b != in_c and in_c == in_a:
                pred_fault_b = MuBiTrue
                pred_out     = in_a
            elif in_a == in_b and in_b != in_c and in_c != in_a:
                pred_fault_c = MuBiTrue
                pred_out     = in_b
            elif in_a != in_b and in_b == in_c and in_c != in_a:
                pred_fault_a = MuBiTrue
                pred_out     = in_c
            else:
                # Assume that only 1 fault is possible in the test
                # so in the remaining cases there are no faults.
                pred_out = in_a

            # Check MuBi
            assert it.signals["fault_a"] in [MuBiTrue, MuBiFalse]
            assert it.signals["fault_b"] in [MuBiTrue, MuBiFalse]
            assert it.signals["fault_c"] in [MuBiTrue, MuBiFalse]

            # Check
            assert pred_out     == it.signals["out"]
            assert pred_fault_a == it.signals["fault_a"]
            assert pred_fault_b == it.signals["fault_b"]
            assert pred_fault_c == it.signals["fault_c"]

# ==============================================================================


@test()
class TestVoting(BaseTest):
    def __init__(self, name, parent):
        super().__init__(name, parent, TestSequence, Scoreboard)
