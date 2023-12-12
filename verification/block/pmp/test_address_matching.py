# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0


from common import BaseSequence
from pyuvm import ConfigDB, test
from testbench import (
    BaseEnv,
    BaseTest,
    PMPWriteAddrCSRItem,
    PMPWriteCfgCSRItem,
    getDecodedEntryCfg,
)

pmp_configurations = [
    {
        # 0 - Entry locked but disabled, address 0x1000
        "pmpcfg": 0b10000000,
        "pmpaddr": (0x1000 >> 2),
    },
    {
        # 1 - Entry locked, allow RWX, TOR, address range 0x1000-0x1FFF
        "pmpcfg": 0b10001111,
        "pmpaddr": (0x2000 >> 2),
    },
    {
        # 2 - Entry locked, allow R, TOR, address range 0x2000-0x3FFF
        "pmpcfg": 0b10001001,
        "pmpaddr": (0x4000 >> 2),
    },
    {
        # 3 - Entry locked, allow X, TOR, address range 0x4000-0xFFFF
        "pmpcfg": 0b10001100,
        "pmpaddr": (0x10000 >> 2),
    },
    {
        # 4 - Entry locked, allow W, TOR, address range 0x10000-0x1FFFF
        "pmpcfg": 0b10001010,
        "pmpaddr": (0x20000 >> 2),
    },
    {
        # 5 - Entry unlocked, allow none, TOR, address range 0x20000-0xFFFFFFFF
        "pmpcfg": 0b00001000,
        "pmpaddr": (0x100000000 >> 2),
    },
    {
        # 6 - Entry locked, allow none, TOR, address range 0xFFFFFFFF-0x10000
        "pmpcfg": 0b10001000,
        "pmpaddr": (0x20000 >> 2),
    },
    {
        # 7 - Entry locked, allow RWX, NA4, address range 0x20000-0x20003
        "pmpcfg": 0b10010111,
        "pmpaddr": (0x20000 >> 2),
    },
    {
        # 8 - Entry locked, allow none, NA4, address range 0x30000-0x30003
        "pmpcfg": 0b10010000,
        "pmpaddr": (0x30000 >> 2),
    },
    {
        # 9 - Entry locked, allow none, NAPOT, address range 0x40000-0x5FFFF
        "pmpcfg": 0b10011000,
        "pmpaddr": (0x57FFF >> 2),
    },
    {
        # 10 - Entry locked, allow RW, NAPOT, address range 0x24000-0x25FFF
        "pmpcfg": 0b10011011,
        "pmpaddr": (0x257FF >> 2),
    },
    {
        # 11 - Entry locked, allow X, NAPOT, address range 0x26000-0x26FFF
        "pmpcfg": 0b10011100,
        "pmpaddr": (0x26BFF >> 2),
    },
    {
        # 12 - Entry locked, allow RW, NAPOT, address range 0x26000-0x26FFF
        "pmpcfg": 0b10011011,
        "pmpaddr": (0x26BFF >> 2),
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

        # Check boundaries and few random addresses of each PMP entry
        for i in range(len(pmp_configurations)):
            start_addr, end_addr = getDecodedEntryCfg(self.pmp_regs, i, range_only=True)

            await self.checkRangeBoundary(start_addr)

            # Access up to 10 random memory cells
            accesses = min((end_addr - start_addr) // 4, 10)
            if start_addr != end_addr:
                for _ in range(accesses):
                    await self.randomAccessInAddrRange(start_addr, end_addr)

            await self.checkRangeBoundary(end_addr)

        # In the end check accesses at random memory locations
        for _ in range(test_iterations):
            await self.randomAccessInAddrRange(0x00000000, 0xFFFFFFFF)


# ==============================================================================


@test()
class TestAddressMatching(BaseTest):
    """
    This test provides a sequence that checks behaviour for different address
    matching schemes like:
    - Disabled entries
    - Top of range with lower boundary than previous entry
    - Top of range with higher boundary than previous entry
    - Unlocked entry that "forbids" access
    - Different permissions restrictions
    - Different configurations with interlacing address ranges
    """

    def __init__(self, name, parent):
        super().__init__(name, parent, BaseEnv)

    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = TestSequence.create("stimulus")

    async def run(self):
        await self.seq.start()
