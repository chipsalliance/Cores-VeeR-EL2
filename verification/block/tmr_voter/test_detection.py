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
    Enable exactly 2 random inputs. Drive the same value to them. Occassionaly
    do an upsed by driving one of the enable inputs with a different value.
    """
    def __init__(self, name):
        super().__init__(name)

        self.seqr = ConfigDB().get(None, "", "SEQR")

    async def body(self):
        iter  = ConfigDB().get(None, "", "TEST_ITERATIONS")
        width = 8 # FIXME: Sync with makefile

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

            # Make a single random fault
            if random.random() < 0.25:
                upset = random.randrange(0, 1 << width)
                which = random.choice(enabled).replace("en_", "in_")

                it.signals[which] = upset

            # Send the item
            await self.seqr.start_item(it)
            await self.seqr.finish_item(it)


# ==============================================================================


class Scoreboard(BaseScoreboard):
    """
    Check if mismatches are correctly detected between any two enabled inputs
    """

    def check_phase(self):
        self.passed = True

        while self.port.can_get():
            _, it = self.port.try_get()
            self.logger.debug(str(it))

            # Everything disabled, skip
            if it.signals["en_a"] != MuBiTrue and \
               it.signals["en_b"] != MuBiTrue and \
               it.signals["en_c"] != MuBiTrue:
               continue

            in_a = it.signals["in_a"]
            in_b = it.signals["in_b"]
            in_c = it.signals["in_c"]

            en_a = it.signals["en_a"] == MuBiTrue
            en_b = it.signals["en_b"] == MuBiTrue
            en_c = it.signals["en_c"] == MuBiTrue

            # Predict
            pred_out     = None
            pred_fault_a = MuBiFalse
            pred_fault_b = MuBiFalse
            pred_fault_c = MuBiFalse

            # C is disabled
            if en_a and en_b and not en_c:
                pred_out     = in_a     if (in_a == in_b) else None
                pred_fault_a = MuBiTrue if (in_a != in_b) else MuBiFalse
                pred_fault_b = MuBiTrue if (in_a != in_b) else MuBiFalse
                pred_fault_c = MuBiFalse

            # A is disabled
            elif not en_a and en_b and en_c:
                pred_out     = in_b     if (in_b == in_c) else None
                pred_fault_a = MuBiFalse
                pred_fault_b = MuBiTrue if (in_b != in_c) else MuBiFalse
                pred_fault_c = MuBiTrue if (in_b != in_c) else MuBiFalse

            # B is disabled
            elif en_a and not en_b and en_c:
                pred_out     = in_c     if (in_c == in_a) else None
                pred_fault_a = MuBiTrue if (in_c != in_a) else MuBiFalse
                pred_fault_b = MuBiFalse
                pred_fault_c = MuBiTrue if (in_c != in_a) else MuBiFalse

            # Should not happen in this test
            else:
                assert False

            # Check MuBi
            assert it.signals["fault_a"] in [MuBiTrue, MuBiFalse]
            assert it.signals["fault_b"] in [MuBiTrue, MuBiFalse]
            assert it.signals["fault_c"] in [MuBiTrue, MuBiFalse]

            # Check
            if pred_out is not None:
                assert pred_out == it.signals["out"]

            assert pred_fault_a == it.signals["fault_a"]
            assert pred_fault_b == it.signals["fault_b"]
            assert pred_fault_c == it.signals["fault_c"]

# ==============================================================================


@test()
class TestDetection(BaseTest):
    def __init__(self, name, parent):
        super().__init__(name, parent, TestSequence, Scoreboard)
