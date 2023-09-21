# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

import random
import struct

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


class MemWriteSequence(uvm_sequence):
    """
    A sequence of random memory writes
    """

    def __init__(self, name, mem, dwidth=32):
        super().__init__(name)
        self.mem = mem
        self.dwidth = dwidth

    async def body(self):
        mem_base = ConfigDB().get(None, "", self.mem + "_BASE")
        mem_size = ConfigDB().get(None, "", self.mem + "_SIZE")

        align = ConfigDB().get(None, "", "ADDR_ALIGN")

        count = ConfigDB().get(None, "", "TEST_ITERATIONS")
        burst = ConfigDB().get(None, "", "TEST_BURST_LEN")
        gap = ConfigDB().get(None, "", "TEST_BURST_GAP")

        for j in range(count):
            for i in range(burst):
                addr = mem_base + random.randrange(0, mem_size)
                addr = (addr // align) * align

                # Determine how to pack data to bytes
                if self.dwidth == 32:
                    fmt = "<I"
                elif self.dwidth == 64:
                    fmt = "<Q"
                else:
                    assert False, self.dwidth

                data = random.randrange(0, (1 << self.dwidth) - 1)
                item = BusWriteItem(addr, struct.pack(fmt, data))

                await self.start_item(item)
                await self.finish_item(item)

            await ClockCycles(cocotb.top.clk, gap)


class AnyMemWriteSequence(uvm_sequence):
    """
    A sequence of random ICCM or DCCM writes
    """

    def __init__(self, name, dwidth=32):
        super().__init__(name)
        self.dwidth = dwidth

    async def body(self):
        iccm_base = ConfigDB().get(None, "", "ICCM_BASE")
        iccm_size = ConfigDB().get(None, "", "ICCM_SIZE")

        dccm_base = ConfigDB().get(None, "", "DCCM_BASE")
        dccm_size = ConfigDB().get(None, "", "DCCM_SIZE")

        align = ConfigDB().get(None, "", "ADDR_ALIGN")

        count = ConfigDB().get(None, "", "TEST_ITERATIONS")
        burst = ConfigDB().get(None, "", "TEST_BURST_LEN")
        gap = ConfigDB().get(None, "", "TEST_BURST_GAP")

        for j in range(count):
            for i in range(burst):
                mem_base, mem_size = random.choice(
                    [
                        (iccm_base, iccm_size),
                        (dccm_base, dccm_size),
                    ]
                )

                addr = mem_base + random.randrange(0, mem_size)
                addr = (addr // align) * align

                # Determine how to pack data to bytes
                if self.dwidth == 32:
                    fmt = "<I"
                elif self.dwidth == 64:
                    fmt = "<Q"
                else:
                    assert False, self.dwidth

                data = random.randrange(0, (1 << self.dwidth) - 1)
                item = BusWriteItem(addr, struct.pack(fmt, data))

                await self.start_item(item)
                await self.finish_item(item)

            await ClockCycles(cocotb.top.clk, gap)


# =============================================================================


class MemReadSequence(uvm_sequence):
    """
    A sequence of random memory reads
    """

    def __init__(self, name, mem):
        super().__init__(name)
        self.mem = mem

    async def body(self):
        mem_base = ConfigDB().get(None, "", self.mem + "_BASE")
        mem_size = ConfigDB().get(None, "", self.mem + "_SIZE")

        align = ConfigDB().get(None, "", "ADDR_ALIGN")

        count = ConfigDB().get(None, "", "TEST_ITERATIONS")
        burst = ConfigDB().get(None, "", "TEST_BURST_LEN")
        gap = ConfigDB().get(None, "", "TEST_BURST_GAP")

        for j in range(count):
            for i in range(burst):
                addr = mem_base + random.randrange(0, mem_size)
                addr = (addr // align) * align

                item = BusReadItem(addr)
                await self.start_item(item)
                await self.finish_item(item)

            await ClockCycles(cocotb.top.clk, gap)


class AnyMemReadSequence(uvm_sequence):
    """
    A sequence of random ICCM or DCCM reads
    """

    def __init__(self, name):
        super().__init__(name)

    async def body(self):
        iccm_base = ConfigDB().get(None, "", "ICCM_BASE")
        iccm_size = ConfigDB().get(None, "", "ICCM_SIZE")

        dccm_base = ConfigDB().get(None, "", "DCCM_BASE")
        dccm_size = ConfigDB().get(None, "", "DCCM_SIZE")

        align = ConfigDB().get(None, "", "ADDR_ALIGN")

        count = ConfigDB().get(None, "", "TEST_ITERATIONS")
        burst = ConfigDB().get(None, "", "TEST_BURST_LEN")
        gap = ConfigDB().get(None, "", "TEST_BURST_GAP")

        for j in range(count):
            for i in range(burst):
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

            await ClockCycles(cocotb.top.clk, gap)


# =============================================================================


class InvalidAddressSequence(uvm_sequence):
    """
    A sequence of random bus read/write requests to addresses
    outside the range accepted by the DMA module
    """

    def __init__(self, name, dwidth=32):
        super().__init__(name)
        self.dwidth = dwidth

    async def body(self):
        iccm_base = ConfigDB().get(None, "", "ICCM_BASE")
        iccm_size = ConfigDB().get(None, "", "ICCM_SIZE")

        dccm_base = ConfigDB().get(None, "", "DCCM_BASE")
        dccm_size = ConfigDB().get(None, "", "DCCM_SIZE")

        pic_base = ConfigDB().get(None, "", "PIC_BASE")
        pic_size = ConfigDB().get(None, "", "PIC_SIZE")

        align = ConfigDB().get(None, "", "ADDR_ALIGN")

        count = ConfigDB().get(None, "", "TEST_ITERATIONS")
        burst = ConfigDB().get(None, "", "TEST_BURST_LEN")
        gap = ConfigDB().get(None, "", "TEST_BURST_GAP")

        for j in range(count):
            for i in range(burst):
                # Crude address randomizer
                while True:
                    addr = random.randrange(0, (1 << 32) - 1)
                    addr = (addr // align) * align

                    if addr >= iccm_base and addr < iccm_base + iccm_size:
                        continue
                    if addr >= dccm_base and addr < dccm_base + dccm_size:
                        continue
                    if addr >= pic_base and addr < pic_base + pic_size:
                        continue

                    break

                # Randomize read/write
                if random.random() >= 0.5:
                    item = BusReadItem(addr)
                else:
                    # Determine how to pack data to bytes
                    if self.dwidth == 32:
                        fmt = "<I"
                    elif self.dwidth == 64:
                        fmt = "<Q"
                    else:
                        assert False, self.dwidth

                    data = random.randrange(0, (1 << self.dwidth) - 1)
                    item = BusWriteItem(addr, struct.pack(fmt, data))

                await self.start_item(item)
                await self.finish_item(item)

            await ClockCycles(cocotb.top.clk, gap)
