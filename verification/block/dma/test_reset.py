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
            "dma_dbg_cmd_done": 0,
            "dma_dbg_cmd_fail": 0,
            "dma_dccm_req": 0,
            "dma_iccm_req": 0,
            "dma_active": 0,
            "dma_dccm_stall_any": 0,
            "dma_iccm_stall_any": 0,
            "dma_pmu_dccm_read": 0,
            "dma_pmu_dccm_write": 0,
            "dma_pmu_any_read": 0,
            "dma_pmu_any_write": 0,
            "dma_axi_bvalid": 0,
            "dma_axi_rvalid": 0,
        }

        for name, value in state.items():
            signal = getattr(cocotb.top, name)
            assert signal.value == value, "{}={}, should be {}".format(name, signal.value, value)
