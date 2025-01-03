# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0
import random

import pyuvm
from cocotb.triggers import ClockCycles
from pyuvm import *
from testbench import (
    PMPADDR0,
    PMPADDR16,
    PMPADDR32,
    PMPADDR48,
    PMPCFG,
    BaseTest,
    InputItem,
)

# =============================================================================


class CsrSequence(uvm_sequence):
    """
    A random sequence of PMP CSR items with random addresses and data
    """

    def __init__(self, name):
        super().__init__(name)

        # Generate
        self.items = []
        addrs = set()
        for i in range(5):

            while True:
                item = InputItem(PMPCFG)
                item.randomize()
                if item.addr not in addrs:
                    break
            self.legalize_pmpcfg(item)
            self.items.append(item)
            addrs.add(item.addr)

            for base in [PMPADDR0, PMPADDR16, PMPADDR32, PMPADDR48]:
                while True:
                    item = InputItem(base)
                    item.randomize()
                    if item.addr not in addrs:
                        break
                self.legalize_pmpaddr(item)
                self.items.append(item)
                addrs.add(item.addr)

    def legalize_pmpcfg(self, item):
        """
        Leave only A, X and R fields as any combination of them is leagal and
        does not influence PMPADDR access. Setting L would interfere with the
        test.
        """
        mask = 0b00011101
        item.data &= (mask << 24) | (mask << 16) | (mask << 8) | mask

    def legalize_pmpaddr(self, item):
        """
        Mask out two MSBs
        """
        item.data &= 0x3FFFFFFF

    async def body(self):

        # Run
        for item in self.items:
            await self.start_item(item)
            await self.finish_item(item)


class PmpCfgLockSequence(uvm_sequence):
    """
    A random sequence of PMPCFG accesses that also do entry locking
    """

    def __init__(self, name):
        super().__init__(name)

        # Generate
        self.items = []
        addrs = set()
        for i in range(10):

            while True:
                item = InputItem(PMPCFG)
                item.randomize()
                if item.addr not in addrs:
                    break
            self.legalize_pmpcfg(item)
            self.items.append(item)
            addrs.add(item.addr)

    def legalize_pmpcfg(self, item):
        """
        Leave only L, A, X and R fields as any combination of them is leagal and
        does not influence PMPADDR access.
        """
        mask = 0b10011101
        item.data &= (mask << 24) | (mask << 16) | (mask << 8) | mask

    async def body(self):

        # Run
        for item in self.items:
            await self.start_item(item)
            await self.finish_item(item)


# =============================================================================


@pyuvm.test()
class TestCsrAccess(BaseTest):
    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        count = ConfigDB().get(None, "", "TEST_ITERATIONS")
        self.seq = [CsrSequence("stimulus") for i in range(count)]

    async def run(self):
        for seq in self.seq:
            await seq.start(self.env.pmp_wr_seqr)
            await seq.start(self.env.pmp_rd_seqr)


@pyuvm.test()
class TestPmpCfgLock(BaseTest):
    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        count = ConfigDB().get(None, "", "TEST_ITERATIONS")
        self.seq = [PmpCfgLockSequence("stimulus") for i in range(count)]

    async def run(self):
        for seq in self.seq:

            # Do sequence of PMPCFG lock writes
            await seq.start(self.env.pmp_wr_seqr)
            await seq.start(self.env.pmp_rd_seqr)

            # Reset the module (there's no other way to clear the locks)
            await self.do_reset()
