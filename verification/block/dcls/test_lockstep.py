# Copyright (c) 2024 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

from random import randrange

import pyuvm
from cocotb.triggers import ClockCycles, ReadOnly, RisingEdge
from cocotb.utils import get_sim_time
from pyuvm import ConfigDB
from testbench import BaseTest

# =============================================================================


@pyuvm.test()
class TestReset(BaseTest):
    """
    A basic test that resets the DUT and ensures shadow core gets out of reset
    after the configured delay
    """

    def assert_signals(self, signals):
        time = get_sim_time(units="ns")
        self.logger.info(f"Validating signals at {time}")
        for name, value in signals.items():
            try:
                sig = getattr(self.dut, name)
            except AttributeError:
                print(f"DUT does not contain signal named {name}")
                exit(1)
            self.logger.info(f"Assert that {name}={value}")
            assert sig.value == value

    async def test_reset(self):
        lockstep_delay = ConfigDB().get(None, "", "LOCKSTEP_DELAY")
        signals = {
            "shadow_reset": 0,
            "shadow_dbg_reset": 0,
            "corruption_detected_o": 0,
        }
        # The shadow core should go into the reset regardless of the delay
        for _ in range(lockstep_delay):
            await ReadOnly()
            self.assert_signals(signals)
            await RisingEdge(self.clk)

        # After the delay shadow core should be out of reset without corruption detected
        signals.update({"shadow_reset": 1, "shadow_dbg_reset": 1})
        await ReadOnly()
        self.assert_signals(signals)
        await RisingEdge(self.clk)

    async def run(self):
        await self.test_reset()


@pyuvm.test()
class TestErrorInjection(TestReset):
    """
    A test that ensures the Shadow Core reports a corruption after enabling an error injection.
    """

    async def run(self):
        # Get out of reset
        await self.test_reset()

        # Await few cycles (arbitrary number)
        await ClockCycles(self.clk, 10)

        # Enable error injection
        self.dut.lockstep_err_injection_en_i.value = 1
        await RisingEdge(self.clk)

        # Assert that an error is detected
        signals = {
            "shadow_reset": 1,
            "shadow_dbg_reset": 1,
            "corruption_detected_o": 1,
        }
        self.assert_signals(signals)

        # Disable the Shadow Core
        self.dut.disable_corruption_detection_i.value = 1
        await RisingEdge(self.clk)

        # Assert that an error is not detected
        signals.update({"corruption_detected_o": 0})
        self.assert_signals(signals)
