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
    DebugReadItem,
    DebugWriteItem,
    MemReadItem,
    MemWriteItem,
)

# =============================================================================


class ReadScoreboard(uvm_component):
    """
    A scoreboard that counts reads that happen on the debug/AXI and memory
    sides of the DMA module
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
        return addr >= self.iccm_base and addr < (self.iccm_base + self.iccm_size)

    def is_dccm(self, addr):
        return addr >= self.dccm_base and addr < (self.dccm_base + self.dccm_size)

    def check_phase(self):
        iccm_reads = defaultdict(lambda: 0)
        dccm_reads = defaultdict(lambda: 0)

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
                # FIXME: Assuming the transaction is 64-bit wide
                data = struct.unpack("<Q", item.data)[0]

                if self.is_iccm(item.addr):
                    addr = item.addr - self.iccm_base
                    iccm_reads[(addr, data)] += 1

                elif self.is_dccm(item.addr):
                    addr = item.addr - self.dccm_base
                    dccm_reads[(addr, data)] += 1

                else:
                    self.logger.error("Read from a non-memory address 0x{:08X}".format(item.addr))
                    self.passed = False

            # Debug read. Check and decode its address
            elif isinstance(item, DebugReadItem):
                data = item.data

                if self.is_iccm(item.addr):
                    addr = item.addr - self.iccm_base
                    iccm_reads[(addr, data)] += 1

                elif self.is_dccm(item.addr):
                    addr = item.addr - self.dccm_base
                    dccm_reads[(addr, data)] += 1

                else:
                    self.logger.error("Read from a non-memory address 0x{:08X}".format(item.addr))
                    self.passed = False

            # Memory read
            elif isinstance(item, MemReadItem):
                # Mask out unused bits
                if item.size == 0:
                    data = item.data & 0xFF
                elif item.size == 1:
                    data = item.data & 0xFFFF
                elif item.size == 2:
                    data = item.data & 0xFFFFFFFF
                elif item.size >= 3:  # FIXME: Unclear
                    data = item.data
                else:
                    self.logger.error("Invalid transaction size {}".format(item.size))
                    self.passed = False

                if item.mem == "ICCM":
                    iccm_reads[
                        (
                            item.addr,
                            data,
                        )
                    ] += 1
                elif item.mem == "DCCM":
                    dccm_reads[
                        (
                            item.addr,
                            data,
                        )
                    ] += 1
                else:
                    self.logger.error("Read from an unknown memory region '{}'".format(item.mem))
                    self.passed = False

        # Check if there is an even number of reads for (each address, data)
        # for each memory region.
        for name, d in [("ICCM", iccm_reads), ("DCCM", dccm_reads)]:
            for key, count in d.items():
                if count & 1:
                    self.logger.error(
                        "{} read count from 0x{:08X} is odd, data {}".format(name, key[0], key[1])
                    )
                    self.passed = False

    def final_phase(self):
        if not self.passed:
            self.logger.critical("{} reports a failure".format(type(self)))
            assert False


# =============================================================================


class WriteScoreboard(uvm_component):
    """
    A scoreboard that counts writes that happen on the debug/AXI and memory
    sides of the DMA module.
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
        return addr >= self.iccm_base and addr < (self.iccm_base + self.iccm_size)

    def is_dccm(self, addr):
        return addr >= self.dccm_base and addr < (self.dccm_base + self.dccm_size)

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
                # FIXME: Assuming the transaction is 64-bit wide
                data = struct.unpack("<Q", item.data)[0]

                if self.is_iccm(item.addr):
                    addr = item.addr - self.iccm_base
                    iccm_writes[(addr, data)] += 1

                elif self.is_dccm(item.addr):
                    addr = item.addr - self.dccm_base
                    dccm_writes[(addr, data)] += 1

                else:
                    self.logger.error("Write to a non-memory address 0x{:08X}".format(item.addr))
                    self.passed = False

            # Debug write. Check and decode its address
            elif isinstance(item, DebugWriteItem):
                if item.fail:
                    self.logger.error("Write to address 0x{:08X} failed".format(item.addr))
                    self.passed = False

                if self.is_iccm(item.addr):
                    addr = item.addr - self.iccm_base
                    data = item.data
                    iccm_writes[(addr, data)] += 1

                elif self.is_dccm(item.addr):
                    addr = item.addr - self.dccm_base
                    data = item.data
                    dccm_writes[(addr, data)] += 1

                else:
                    self.logger.error("Write to a non-memory address 0x{:08X}".format(item.addr))
                    self.passed = False

            # Memory write
            elif isinstance(item, MemWriteItem):
                # Mask out unused bits
                if item.size == 0:
                    data = item.data & 0xFF
                elif item.size == 1:
                    data = item.data & 0xFFFF
                elif item.size == 2:
                    data = item.data & 0xFFFFFFFF
                elif item.size >= 3:  # FIXME: Unclear
                    data = item.data
                else:
                    self.logger.error("Invalid transaction size {}".format(item.size))
                    self.passed = False

                if item.mem == "ICCM":
                    iccm_writes[
                        (
                            item.addr,
                            data,
                        )
                    ] += 1
                elif item.mem == "DCCM":
                    dccm_writes[
                        (
                            item.addr,
                            data,
                        )
                    ] += 1
                else:
                    self.logger.error("Write to an unknown memory region '{}'".format(item.mem))
                    self.passed = False

        # Check if there is an even number of writes for (each address, data)
        # for each memory region.
        for name, d in [("ICCM", iccm_writes), ("DCCM", dccm_writes)]:
            for key, count in d.items():
                if count & 1:
                    self.logger.error(
                        "{} write count to 0x{:08X} is odd, data {}".format(name, key[0], key[1])
                    )
                    self.passed = False

    def final_phase(self):
        if not self.passed:
            self.logger.critical("{} reports a failure".format(type(self)))
            assert False


# =============================================================================


class AccessScoreboard(uvm_component):
    """
    Checks if all Debug/AXI transfers fail with response 0x3 and that there is
    no activity on the ICCM/DCCM memory bus
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
            if isinstance(item, MemReadItem) or isinstance(item, MemWriteItem):
                self.logger.debug("Unexpected memory access at 0x{:08X}".format(item.address))
                self.passed = False

            # Got an AXI activity, check the response code
            elif isinstance(item, BusReadItem) or isinstance(item, BusWriteItem):
                if item.resp != 0x3:
                    self.logger.debug(
                        "Unexpected AXI response (0b{:03b}) for access to 0x{:08X}".format(
                            item.resp, item.address
                        )
                    )
                    self.passed = False

            # Got a debug bus activity, check for failure
            elif isinstance(item, DebugReadItem) or isinstance(item, DebugWriteItem):
                if not item.fail:
                    self.logger.debug(
                        "Unexpected debug bus response (0b{:01b}) for access to 0x{:08X}".format(
                            item.fail, item.address
                        )
                    )
                    self.passed = False

    def final_phase(self):
        if not self.passed:
            self.logger.critical("{} reports a failure".format(type(self)))
            assert False
