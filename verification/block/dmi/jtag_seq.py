#
# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: BSD-2-Clause

from pyuvm import *


class BaseSeq(uvm_sequence):
    async def run_items(self, items):
        for item in items:
            repeat = 1

            if hasattr(item, "repeat"):
                repeat = item.repeat

            for _ in range(repeat):
                await self.start_item(item)
                item.randomize()
                await self.finish_item(item)


class JTAGBaseSeqItem(uvm_sequence_item):
    def __init__(self, name, tms=1, tdi=0, repeat=1):
        super().__init__(name)
        self.name = name
        self.tms = tms
        self.tdi = tdi
        self.repeat = repeat

    def __eq__(self, other):
        pass

    def __str__(self):
        return self.__class__.__name__

    def randomize(self):
        pass


class BasicSequence(uvm_sequence):
    async def body(self):
        for i in range(10):
            uvm_root().logger.info("BasicSequence Item")
            item = JTAGBaseSeqItem("test_logic_reset")
            await self.start_item(item)
            await self.finish_item(item)


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
        items = [
            JTAGBaseSeqItem("switch_to_select_dr_scan", 1, 0),
            JTAGBaseSeqItem("switch_to_capture_dr", 0, 0),
            JTAGBaseSeqItem("switch_to_shift_dr", 0, 0),
            JTAGBaseSeqItem("shift_dr_bits", 0, 0, repeat=32),
            JTAGBaseSeqItem("switch_to_exit1_dr", 1, 0),
            JTAGBaseSeqItem("switch_to_update_dr", 1, 0),
            JTAGBaseSeqItem("switch_to_idle", 0, 0),
            JTAGBaseSeqItem("idle0", 0, 0),
            JTAGBaseSeqItem("idle1", 0, 0),
        ]
        await self.run_items(items)
