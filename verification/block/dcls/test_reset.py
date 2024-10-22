# Copyright (c) 2024 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

import cocotb
import pyuvm
from cocotb.triggers import ClockCycles
from testbench import BaseTest

# =============================================================================


@pyuvm.test()
class TestReset(BaseTest):
    """
    A basic test that resets the DUT
    """

    # TODO: Change me once `el2_veer_lockstep` outputs only `panic` signal
    async def run(self):
        # The shadow core should go into the reset regardless of the delay
        state = {
            "corruption_detected": 0,
        }

        for name, value in state.items():
            signal = getattr(cocotb.top, name)
            assert signal.value == value, "{}={}, should be {}".format(name, signal.value, value)
