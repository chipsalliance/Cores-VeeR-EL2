# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

import random
import struct
from collections import defaultdict

import pyuvm
from cocotb.triggers import ClockCycles
from pyuvm import *
from testbench import (
    BaseEnv,
    BaseTest,
    BusReadItem,
    BusWriteItem,
    MemReadItem,
    MemWriteItem,
)

# =============================================================================


class TestSequence(uvm_sequence):
    """
    A sequence of random ICCM or DCCM reads. ECC failure injection is
    randomized as well.
    """

    def __init__(self, name):
        super().__init__(name)

    async def body(self):
        iccm_base = ConfigDB().get(None, "", "ICCM_BASE")
        iccm_size = ConfigDB().get(None, "", "ICCM_SIZE")

        dccm_base = ConfigDB().get(None, "", "DCCM_BASE")
        dccm_size = ConfigDB().get(None, "", "DCCM_SIZE")

        align = ConfigDB().get(None, "", "ADDR_ALIGN")

        for i in range(50):
            mem_base, mem_size = random.choice(
                [
                    (iccm_base, iccm_size),
                    (dccm_base, dccm_size),
                ]
            )

            addr = mem_base + random.randrange(0, mem_size)
            addr = (addr // align) * align

            item = BusReadItem(addr)
            await self.start_item(item)
            await self.finish_item(item)


# =============================================================================


class Scoreboard(uvm_component):
    """ """

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
        return addr > self.iccm_base and addr < (self.iccm_base + self.iccm_size)

    def is_dccm(self, addr):
        return addr > self.dccm_base and addr < (self.dccm_base + self.dccm_size)

    def check_phase(self):
        reads = defaultdict(lambda: dict())

        # Process writes
        while self.port.can_get():
            # Get an item
            got_item, item = self.port.try_get()
            assert got_item

            # Initially pass
            if self.passed is None:
                self.passed = True

            # AXI read. Check and decode its address
            if isinstance(item, BusReadItem):
                addr = item.addr
                reads[addr]["axi"] = item.resp

            # Memory read
            elif isinstance(item, MemReadItem):
                if item.mem == "ICCM":
                    addr = item.addr + self.iccm_base
                    reads[addr]["mem"] = item.resp
                elif item.mem == "DCCM":
                    addr = item.addr + self.dccm_base
                    reads[addr]["mem"] = item.resp
                else:
                    self.logger.error("Read from an unknown memory region '{}'".format(item.mem))
                    self.passed = False

        # Check reads
        for addr, pair in reads.items():
            if "axi" not in pair:
                self.logger.error("No AXI transfer for access to 0x{:08X}".format(addr))
                self.passed = False

            if "mem" not in pair:
                self.logger.error("No memory transfer for access to 0x{:08X}".format(addr))
                self.passed = False

            if "axi" not in pair or "mem" not in pair:
                continue

            # Check correlation between AXI response and ECC error injection
            if not pair["mem"] and pair["axi"] != 0x0:
                self.logger.error(
                    "AXI transfer error (0b{:03b}) for access to 0x{:08X}".format(pair["axi"], addr)
                )
                self.passed = False

            if pair["mem"] and pair["axi"] != 0x2:
                self.logger.error(
                    "Invalid AXI response (0b{:03b}) for access to 0x{:08X}".format(
                        pair["axi"], addr
                    )
                )
                self.passed = False

    def final_phase(self):
        if not self.passed:
            self.logger.critical("{} reports a failure".format(type(self)))
            assert False


# =============================================================================


class TestEnv(BaseEnv):
    def build_phase(self):
        super().build_phase()

        # Enable ECC error injection
        ConfigDB().set(self.mem_bfm, "", "ECC_ERROR_RATE", 0.5)

        # Add scoreboard
        self.scoreboard = Scoreboard("scoreboard", self)

    def connect_phase(self):
        super().connect_phase()

        # Connect monitors
        self.axi_mon.ap.connect(self.scoreboard.fifo.analysis_export)
        self.mem_mon.ap.connect(self.scoreboard.fifo.analysis_export)


# =============================================================================


@pyuvm.test()
class TestEccError(BaseTest):
    """
    Tests the DMA reaction on ICCM/DCCM ECC error
    """

    def __init__(self, name, parent):
        super().__init__(name, parent, TestEnv)

    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = TestSequence.create("stimulus")

    async def run(self):
        await self.seq.start(self.env.axi_seqr)
