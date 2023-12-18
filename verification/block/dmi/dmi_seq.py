#
# Copyright (c) 2023 Antmicro
# SPDX-License-Identifier: Apache-2.0

import pyuvm
from cocotb.handle import LogicArray
from jtag_seq import *
from pyuvm import *


class SetUncoreEnableSeqItem(uvm_sequence_item):
    def __init__(self, name, uncore_enable):
        super().__init__(name)
        self.uncore_enable = uncore_enable

    def __str__(self):
        return self.__class__.__name__

    def randomize(self):
        pass


class SetUncoreEnableSequence(BaseSeq):
    def __init__(self, name, value):
        super().__init__(name)
        self.name = name
        self.value = value

    async def body(self):
        item = [SetUncoreEnableSeqItem(self.name, self.value)]
        await self.run_items(item)


class AccessDMIRegSequence(BaseSeq):
    def __init__(self, name, addr, data=0x0, is_write=False):
        super().__init__(name)
        assert isinstance(addr, int)
        assert isinstance(data, int)

        self.addr = LogicArray(addr, range(7))
        self.data = LogicArray(data, range(32))
        self.is_write = 1 if is_write else 0

    async def body(self):
        data_bits_items = []
        addr_bits_items = []

        for i, val in enumerate(reversed(list(self.data))):
            data_bits_items.append(JTAGBaseSeqItem("write_data_bit{}".format(i), 0, val))

        for i, val in enumerate(reversed(list(self.addr))):
            # Last bit must be written simultaneously with leaving SHIFT_DR state
            tms = 1 if (i == (len(list(self.addr)) - 1)) else 0
            addr_bits_items.append(JTAGBaseSeqItem("write_addr_bit{}".format(i), tms, val))

        items = [
            JTAGBaseSeqItem("switch_to_select_dr_scan", 1, 0),
            JTAGBaseSeqItem("switch_to_capture_dr", 0, 0),
            JTAGBaseSeqItem("switch_to_shift_dr", 0, 0),
            JTAGBaseSeqItem("write_rd_en_bit", 0, 1),
            JTAGBaseSeqItem("write_wr_en_bit", 0, self.is_write),
        ]
        items += data_bits_items
        items += addr_bits_items
        items += [
            JTAGBaseSeqItem("switch_to_update_dr", 1, 0),
            JTAGBaseSeqItem("switch_to_idle", 0, 0),
            JTAGBaseSeqItem("idle0", 0, 0),
            JTAGBaseSeqItem("idle1", 0, 0),
        ]
        await self.run_items(items)
