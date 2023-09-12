# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

import random
import struct

from cocotb.triggers import ClockCycles

import pyuvm
from pyuvm import *

from testbench import BaseEnv, BaseTest
from testbench import BusReadItem, BusWriteItem
from testbench import MemReadItem, MemWriteItem

# =============================================================================


class TestSequenceRange(uvm_sequence):
    """
    A sequencer that generates random bus read/write requests to addresses
    outside the range accepted by the DMA module
    """

    def __init__(self, name):
        super().__init__(name)

    async def body(self):

        iccm_base = ConfigDB().get(None, "", "ICCM_BASE")
        iccm_size = ConfigDB().get(None, "", "ICCM_SIZE")

        dccm_base = ConfigDB().get(None, "", "DCCM_BASE")
        dccm_size = ConfigDB().get(None, "", "DCCM_SIZE")

        pic_base  = ConfigDB().get(None, "", "PIC_BASE")
        pic_size  = ConfigDB().get(None, "", "PIC_SIZE")

        align = ConfigDB().get(None, "", "ADDR_ALIGN")

        for j in range(50):

            # Crude address randomizer
            while True:
                addr = random.randrange(0, (1 << 32) - 1)
                addr = (addr // align) * align

                if addr >= iccm_base and addr < iccm_base + iccm_size:
                    continue
                if addr >= dccm_base and addr < dccm_base + dccm_size:
                    continue
                if addr >= pic_base  and addr < pic_base  + pic_size:
                    continue

                break

            # Randomize read/write
            if random.random() >= 0.5:
                item = BusReadItem(addr)
            else:
                data = random.randrange(0, (1 << 64) - 1)
                item = BusWriteItem(addr, struct.pack("<Q", data))

            await self.start_item(item)
            await self.finish_item(item)

# =============================================================================


class Scoreboard(uvm_component):
    """
    Checks if all AXI transfers fail with response 0x3 and that there is no
    activity on the ICCM/DCCM memory bus
    """

    def __init__(self, name, parent):
        super().__init__(name, parent)

        self.passed = None

    def build_phase(self):
        self.fifo = uvm_tlm_analysis_fifo("fifo", self)
        self.port = uvm_get_port("port", self)

    def connect_phase(self):
        self.port.connect(self.fifo.get_export)

    def check_phase(self):

        # Process items
        while self.port.can_get():

            # Get an item
            got_item, item = self.port.try_get()
            assert got_item

            # Initially pass
            if self.passed is None:
                self.passed = True

            # Got a memory bus activity which is incorrect
            if isinstance(item, MemReadItem) or \
               isinstance(item, MemWriteItem):
                self.logger.debug(
                    "Unexpected memory access at 0x{:08X}".format(
                    item.address
                ))
                self.passed = False

            # Got an AXI activity, check the response code
            elif isinstance(item, BusReadItem) or \
                 isinstance(item, BusWriteItem):
                if item.resp != 0x3:
                    self.logger.debug(
                        "Unexpected AXI response (0b{:03b}) for access to 0x{:08X}".format(
                        item.resp,
                        item.address
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
class TestAddressOutOfRange(BaseTest):
    """
    Out of range addressing test
    """

    def __init__(self, name, parent):
        super().__init__(name, parent, TestEnv)

    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = TestSequenceRange.create("stimulus")

    async def run(self):
        await self.seq.start(self.env.axi_seqr)

