# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

from common import BaseSequence
from pyuvm import ConfigDB, test
from testbench import BaseEnv, BaseTest, PMPWriteAddrCSRItem, PMPWriteCfgCSRItem

LOWER_BOUNDARY = 0x00000
UPPER_BOUNDARY = 0x20000

pmp_configurations = [
    {
        # 0 - Entry locked, allow none, TOR, address range 0x00000-0x0FFFF
        "pmpcfg": 0b10001000,
        "pmpaddr": (0x10000 >> 2),
    },
    {
        # 1 - Entry locked, but disabled, address 0x01000
        "pmpcfg": 0b10000000,
        "pmpaddr": (0x01000 >> 2),
    },
    {
        # 2 - Entry locked, allow RWX, TOR, address range 0x01000-0x0FFFF
        "pmpcfg": 0b10001111,
        "pmpaddr": (0x10000 >> 2),
    },
    {
        # 3 - Entry unlocked, address 0x01000
        "pmpcfg": 0b00000000,
        "pmpaddr": (0x01000 >> 2),
    },
    {
        # 4 - Entry locked, allow R, TOR, address range 0x01000-0x1FFFF
        "pmpcfg": 0b10001001,
        "pmpaddr": (0x20000 >> 2),
    },
    {
        # 5 - Entry unlocked, address 0x01000
        "pmpcfg": 0b00000000,
        "pmpaddr": (0x01000 >> 2),
    },
    {
        # 6 - Entry locked, allow W, TOR, address range 0x01000-0x1FFFF
        "pmpcfg": 0b10001010,
        "pmpaddr": (0x20000 >> 2),
    },
    {
        # 7 - Entry unlocked, address 0x01000
        "pmpcfg": 0b00000000,
        "pmpaddr": (0x01000 >> 2),
    },
    {
        # 8 - Entry locked, allow X, TOR, address range 0x01000-0x1FFFF
        "pmpcfg": 0b10001100,
        "pmpaddr": (0x20000 >> 2),
    },
]


# =============================================================================


class TestSequence(BaseSequence):
    def __init__(self, name):
        super().__init__(name)

    async def body(self):
        test_iterations = ConfigDB().get(None, "", "TEST_ITERATIONS")
        pmp_entries = ConfigDB().get(None, "", "PMP_ENTRIES")

        # Ensure to not use more configurations than PMP entries
        assert len(pmp_configurations) <= pmp_entries

        # Configure PMP entries
        for i, cfg in enumerate(pmp_configurations):
            item = PMPWriteAddrCSRItem(index=i, pmpaddr=cfg["pmpaddr"])
            await self.pmp_seqr.start_item(item)
            await self.pmp_seqr.finish_item(item)

        for i, cfg in enumerate(pmp_configurations):
            item = PMPWriteCfgCSRItem(index=i, pmpcfg=cfg["pmpcfg"])
            await self.pmp_seqr.start_item(item)
            await self.pmp_seqr.finish_item(item)

        self.checkRangeBoundary(LOWER_BOUNDARY)
        for _ in range(test_iterations):
            await self.randomAccessInAddrRange(LOWER_BOUNDARY, UPPER_BOUNDARY)
        self.checkRangeBoundary(UPPER_BOUNDARY)


# ==============================================================================


@test()
class TestMultipleConfigs(BaseTest):
    """
    This test provides a sequence that checks behaviour for multiple PMP configurations
    appplying to the same address ranges.
    """

    def __init__(self, name, parent):
        super().__init__(name, parent, BaseEnv)

    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = TestSequence.create("stimulus")

    async def run(self):
        await self.seq.start()
