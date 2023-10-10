# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

from pyuvm import ConfigDB, test, uvm_sequence
from testbench import BaseEnv, BaseTest, PMPCheckItem, PMPWriteCSRItem

# =============================================================================


class TestSequence(uvm_sequence):
    def __init__(self, name):
        super().__init__(name)

        self.pmp_seqr = ConfigDB().get(None, "", "PMP_SEQR")

    async def body(self):
        pmp_entries = ConfigDB().get(None, "", "PMP_ENTRIES")
        pmp_channels = ConfigDB().get(None, "", "PMP_CHANNELS")

        # Configure first 8 entries to all possible XWR configurations
        # Use TOR address matching for simplicity
        # 0b10001000
        # - bit 7 - Locked status (1 is locked)
        # - bits 6-5 - Reserved (always 0)
        # - bits 4-3 - Address Matching configuration (01 is TOR)
        # - bit 2 - Execute permission
        # - bit 1 - Write permission
        # - bit 0 - Read permission
        for i in range(8):
            cfg = 0b10001000 + i
            addr = ((i + 1) * 0x1000) >> 2
            item = PMPWriteCSRItem(index=i, pmpcfg=cfg, pmpaddr=addr)
            await self.pmp_seqr.start_item(item)
            await self.pmp_seqr.finish_item(item)

        # Check all possible access variants on configured entries
        for i in range(pmp_channels):
            # Set type to each of 3 available (R or W or X)
            for j in range(3):
                type = 1 << j
                for k in range(pmp_entries):
                    # Set address somewhere in the 0x1000 wide entry
                    addr = (0x200 + (k * 0x1000)) >> 2
                    channel = i

                    item = PMPCheckItem(channel, addr, type)
                    await self.pmp_seqr.start_item(item)
                    await self.pmp_seqr.finish_item(item)


# ==============================================================================


@test()
class TestXWRAccess(BaseTest):
    """
    This test configures few registers to covers or possible variants of RWX
    access permissions and then checks if they are properly checked.
    """

    def __init__(self, name, parent):
        super().__init__(name, parent, BaseEnv)

    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = TestSequence.create("stimulus")

    async def run(self):
        await self.seq.start()
