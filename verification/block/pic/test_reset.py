# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

import cocotb
import pyuvm
from testbench import BaseTest

# =============================================================================


@pyuvm.test()
class TestReset(BaseTest):
    """
    A basic test that resets the DUT
    """

    async def run(self):
        # Check state of DUT signals after reset
        state = {
            "mexintpend": 0,
            "mhwakeup": 0,
            "pl": 0,
            "claimid": 0,
        }

        for name, value in state.items():
            signal = getattr(cocotb.top, name)
            assert signal.value == value, "{}={}, should be {}".format(name, signal.value, value)
