#
# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: BSD-2-Clause

from common import BaseSeq
from pyuvm import *


class JTAGBaseSeqItem(uvm_sequence_item):
    def __init__(self, name, tms=1, tdi=0):
        super().__init__(name)
        self.name = name
        self.tms = tms
        self.tdi = tdi

    def __str__(self):
        return self.__class__.__name__

    def randomize(self):
        pass


class SetIRSequence(BaseSeq):
    def __init__(self, name, instruction):
        super().__init__(name)
        self.instr = instruction

    async def body(self):
        items = [
            JTAGBaseSeqItem("switch_to_select_dr_scan", 1, 0),
            JTAGBaseSeqItem("switch_to_select_ir_scan", 1, 0),
            JTAGBaseSeqItem("switch_to_capture_ir", 0, 0),
            JTAGBaseSeqItem("switch_to_shift_ir", 0, 0),
            JTAGBaseSeqItem("shift_ir_bit_0", 0, (self.instr >> 0) & 0x1),
            JTAGBaseSeqItem("shift_ir_bit_1", 0, (self.instr >> 1) & 0x1),
            JTAGBaseSeqItem("shift_ir_bit_2", 0, (self.instr >> 2) & 0x1),
            JTAGBaseSeqItem("shift_ir_bit_3", 0, (self.instr >> 3) & 0x1),
            JTAGBaseSeqItem("switch_to_exit1_ir", 1, (self.instr >> 4) & 0x1),
            JTAGBaseSeqItem("switch_to_update_ir", 1, 0),
            JTAGBaseSeqItem("switch_to_idle", 0, 0),
            JTAGBaseSeqItem("idle0", 0, 0),
            JTAGBaseSeqItem("idle1", 0, 0),
        ]
        await self.run_items(items)


class ReadIDCODESequence(SetIRSequence):
    def __init__(self, name):
        super().__init__(name, 0b00001)


class CaptureDRSequence(BaseSeq):
    def __init__(self, name):
        super().__init__(name)

    async def body(self):
        shift_dr_items = []
        for i in range(40):
            shift_dr_items.append(JTAGBaseSeqItem("shift_dr_bit{}".format(i), 0, 0))

        items = [
            JTAGBaseSeqItem("switch_to_select_dr_scan", 1, 0),
            JTAGBaseSeqItem("switch_to_capture_dr", 0, 0),
            JTAGBaseSeqItem("switch_to_shift_dr", 0, 0),
        ]
        items += shift_dr_items
        items += [
            JTAGBaseSeqItem("switch_to_exit1_dr", 1, 0),
            JTAGBaseSeqItem("switch_to_update_dr", 1, 0),
            JTAGBaseSeqItem("switch_to_idle", 0, 0),
            JTAGBaseSeqItem("idle0", 0, 0),
            JTAGBaseSeqItem("idle1", 0, 0),
        ]

        await self.run_items(items)
