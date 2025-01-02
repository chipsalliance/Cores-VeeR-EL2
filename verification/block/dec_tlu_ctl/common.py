from random import randrange

from pyuvm import ConfigDB, uvm_sequence
from testbench import PMPCheckItem


class BaseSequence(uvm_sequence):
    MAX_ADDR = 2**32 - 4

    def __init__(self, name):
        super().__init__(name)

        self.pmp_regs = ConfigDB().get(None, "", "PMP_CSRS")
        self.pmp_seqr = ConfigDB().get(None, "", "PMP_SEQR")
        self.pmp_channels = ConfigDB().get(None, "", "PMP_CHANNELS")

    # Access (R, W, X) memory at a given address on all channels
    async def accessAtAddr(self, addr):
        for t in range(3):
            type = 1 << t
            for c in range(self.pmp_channels):
                item = PMPCheckItem(channel=c, addr=addr, type=type)
                await self.pmp_seqr.start_item(item)
                await self.pmp_seqr.finish_item(item)

    # Try to access memory at random locations in a given address range
    async def randomAccessInAddrRange(self, start_addr, end_addr):
        addr = randrange(start_addr, end_addr, 4)
        await self.accessAtAddr(addr)

    # Access memory at a given address and at adjacent addresses
    async def checkRangeBoundary(self, addr):
        # Ensure access address is always aligned and doesn't extend 32 bits,
        # address is assumed to be inclusive so increment it by 1 initially.
        addr = min(self.MAX_ADDR, (addr + 1) & 0xFFFFFFFC)

        if addr >= 4:
            await self.accessAtAddr(addr - 4)
        await self.accessAtAddr(addr)
        if addr < self.MAX_ADDR:
            await self.accessAtAddr(addr + 4)
