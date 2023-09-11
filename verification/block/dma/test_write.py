# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

import random
import struct
from collections import defaultdict

from cocotb.triggers import ClockCycles

import pyuvm
from pyuvm import *

from testbench import BaseEnv, BaseTest
from testbench import BusReadItem, BusWriteItem
from testbench import MemReadItem, MemWriteItem

# =============================================================================


class TestSequenceDCCM(uvm_sequence):
    """
    A sequence of random DCCM writes
    """

    def __init__(self, name):
        super().__init__(name)

    async def body(self):

        dccm_base = ConfigDB().get(None, "", "DCCM_BASE")
        dccm_size = ConfigDB().get(None, "", "DCCM_SIZE")

        for j in range(4):
            for i in range(6):

                addr = dccm_base + random.randrange(0, dccm_size)
                data = random.randrange(0, (1 << 64) - 1)

                item = BusWriteItem(addr, struct.pack("<Q", data))
                await self.start_item(item)
                await self.finish_item(item)

            await ClockCycles(cocotb.top.clk, 5)


class TestSequenceICCM(uvm_sequence):
    """
    A sequence of random ICCM writes
    """

    def __init__(self, name):
        super().__init__(name)

    async def body(self):

        iccm_base = ConfigDB().get(None, "", "ICCM_BASE")
        iccm_size = ConfigDB().get(None, "", "ICCM_SIZE")

        for j in range(4):
            for i in range(6):

                addr = iccm_base + random.randrange(0, iccm_size)
                data = random.randrange(0, (1 << 64) - 1)

                item = BusWriteItem(addr, struct.pack("<Q", data))
                await self.start_item(item)
                await self.finish_item(item)

            await ClockCycles(cocotb.top.clk, 5)


class TestSequenceBoth(uvm_sequence):
    """
    A sequence of random ICCM or DCCM writes
    """

    def __init__(self, name):
        super().__init__(name)

    async def body(self):

        iccm_base = ConfigDB().get(None, "", "ICCM_BASE")
        iccm_size = ConfigDB().get(None, "", "ICCM_SIZE")

        dccm_base = ConfigDB().get(None, "", "DCCM_BASE")
        dccm_size = ConfigDB().get(None, "", "DCCM_SIZE")

        for j in range(4):
            for i in range(6):

                mem_base, mem_size = random.choice([
                    (iccm_base, iccm_size),
                    (dccm_base, dccm_size),
                ])

                addr = mem_base + random.randrange(0, mem_size)
                data = random.randrange(0, (1 << 64) - 1)

                item = BusWriteItem(addr, struct.pack("<Q", data))
                await self.start_item(item)
                await self.finish_item(item)

            await ClockCycles(cocotb.top.clk, 5)

# =============================================================================


class Scoreboard(uvm_component):
    """
    A scoreboard that counts writes that happen on AXI and memory sides of the
    DMA module
    """

    def __init__(self, name, parent):
        super().__init__(name, parent)

        self.passed = None

        self.iccm_base = ConfigDB().get(None, "", "ICCM_BASE")
        self.iccm_size = ConfigDB().get(None, "", "ICCM_SIZE")

        self.dccm_base = ConfigDB().get(None, "", "DCCM_BASE")
        self.dccm_size = ConfigDB().get(None, "", "DCCM_SIZE")

    def build_phase(self):
        self.fifo = uvm_tlm_analysis_fifo("fifo", self)
        self.port = uvm_get_port("port", self)

    def connect_phase(self):
        self.port.connect(self.fifo.get_export)

    def is_iccm(self, addr):
        return addr > self.iccm_base and \
               addr < (self.iccm_base + self.iccm_size)

    def is_dccm(self, addr):
        return addr > self.dccm_base and \
               addr < (self.dccm_base + self.dccm_size)

    def check_phase(self):

        iccm_writes = defaultdict(lambda: 0)
        dccm_writes = defaultdict(lambda: 0)

        # Process writes
        while self.port.can_get():

            # Get an item
            got_item, item = self.port.try_get()
            assert got_item

            # Initially pass
            if self.passed is None:
                self.passed = True

            # AXI write. Check and decode its address
            if isinstance(item, BusWriteItem):

                if self.is_iccm(item.addr):
                    addr = item.addr - self.iccm_base
                    data = struct.unpack("<Q", item.data)[0]
                    iccm_writes[(addr, data)] += 1

                elif self.is_dccm(item.addr):
                    addr = item.addr - self.dccm_base
                    data = struct.unpack("<Q", item.data)[0]
                    dccm_writes[(addr, data)] += 1

                else:
                    self.logger.error(
                        "Write to a non-memory address 0x{:08X}".format(
                        item.addr
                    ))
                    self.passed = False

            # Memory write
            elif isinstance(item, MemWriteItem):
                if item.mem == "ICCM":
                    iccm_writes[(item.addr, item.data,)] += 1
                elif item.mem == "DCCM":
                    dccm_writes[(item.addr, item.data,)] += 1
                else:
                    self.logger.error(
                        "Write to an unknown memory region '{}'".format(
                        item.mem
                    ))
                    self.passed = False

        # Check if there is an even number of writes for (each address, data)
        # for each memory region.
        for name, d in [("ICCM", iccm_writes), ("DCCM", dccm_writes)]:
            for key, count in d.items():
                if count & 1:
                    self.logger.error(
                        "{} write count to 0x{:08X} is odd, data {}".format(
                        name,
                        key[0],
                        key[1]
                    ))
                    self.passed = False

    def final_phase(self):
        if not self.passed:
            self.logger.critical("{} reports a failure".format(type(self)))
            assert False

# =============================================================================


class TestEnv(BaseEnv):
    def build_phase(self):
        super().build_phase()

        # Add scoreboard
        self.scoreboard = Scoreboard("scoreboard", self)

    def connect_phase(self):
        super().connect_phase()

        # Connect monitors
        self.axi_mon.ap.connect(self.scoreboard.fifo.analysis_export)
        self.mem_mon.ap.connect(self.scoreboard.fifo.analysis_export)

# =============================================================================


@pyuvm.test()
class TestDCCMWrite(BaseTest):
    """
    DCCM write test
    """

    def __init__(self, name, parent):
        super().__init__(name, parent, TestEnv)

    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = TestSequenceDCCM.create("stimulus")

    async def run(self):
        await self.seq.start(self.env.axi_seqr)


@pyuvm.test()
class TestICCMWrite(BaseTest):
    """
    ICCM write test
    """

    def __init__(self, name, parent):
        super().__init__(name, parent, TestEnv)

    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = TestSequenceICCM.create("stimulus")

    async def run(self):
        await self.seq.start(self.env.axi_seqr)


@pyuvm.test()
class TestBothWrite(BaseTest):
    """
    Randomized DCCM/ICCM write test
    """

    def __init__(self, name, parent):
        super().__init__(name, parent, TestEnv)

    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = TestSequenceBoth.create("stimulus")

    async def run(self):
        await self.seq.start(self.env.axi_seqr)
