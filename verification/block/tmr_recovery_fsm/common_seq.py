# Copyright (c) 2026 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0
import copy

from pyuvm import uvm_sequence
from testbench import CPUCtrlStatusItem, ExtFlagsItem, MuBiFalse, MuBiTrue, RegBusItem


class CPUReactiveCtrlSequence(uvm_sequence):
    """
    A sequence which responds to control requests
    """

    def __init__(self, name, seqr, halt_delay=3, run_delay=1):
        self.seqr = seqr
        self.halted = False
        self.halt_delay = halt_delay
        self.run_delay = run_delay
        super().__init__(name)

    async def body(self):
        while True:
            item = CPUCtrlStatusItem()
            item.wait_req = True
            await self.seqr.start_item(item)
            await self.seqr.finish_item(item)
            item = CPUCtrlStatusItem()
            item.sample = True
            await self.seqr.start_item(item)
            await self.seqr.finish_item(item)
            state = await self.seqr.get_response()
            if state.i_cpu_halt_req:
                if not self.halted:
                    for _ in range(self.halt_delay):
                        item = CPUCtrlStatusItem()
                        item.drive_ext = True
                        await self.seqr.start_item(item)
                        await self.seqr.finish_item(item)
                    self.halted = True
                item = CPUCtrlStatusItem()
                item.drive_ext = True
                item.o_cpu_halt_ack = 1
                item.o_cpu_halt_status = 1
                await self.seqr.start_item(item)
                await self.seqr.finish_item(item)
            elif state.i_cpu_run_req:
                if self.halted:
                    item.o_cpu_halt_status = 1
                    for _ in range(self.run_delay):
                        item = CPUCtrlStatusItem()
                        item.drive_ext = True
                        await self.seqr.start_item(item)
                        await self.seqr.finish_item(item)
                    self.halted = False
                item = CPUCtrlStatusItem()
                item.drive_ext = True
                item.o_cpu_halt_status = 0
                item.o_cpu_run_ack = 1
                await self.seqr.start_item(item)
                await self.seqr.finish_item(item)


class ExternalFlagSequence(uvm_sequence):
    """
    A sequence which drives external flag and responds to clear request
    """

    def __init__(self, name, seqr, clear_delay=0):
        self.seqr = seqr
        self.clear_delay = clear_delay
        super().__init__(name)

    async def body(self):
        item = ExtFlagsItem()
        item.ext = MuBiTrue
        item.drive_ext = True
        await self.seqr.start_item(item)
        await self.seqr.finish_item(item)
        _ = await self.seqr.get_response()
        item = ExtFlagsItem()
        item.wait_for_clr = True
        await self.seqr.start_item(item)
        await self.seqr.finish_item(item)
        _ = await self.seqr.get_response()
        for _ in range(self.clear_delay):
            item = ExtFlagsItem()
            item.ext = MuBiTrue
            item.drive_ext = True
            await self.seqr.start_item(item)
            await self.seqr.finish_item(item)
            _ = await self.seqr.get_response()
        item = ExtFlagsItem()
        item.ext = MuBiFalse
        item.drive_ext = True
        await self.seqr.start_item(item)
        await self.seqr.finish_item(item)
        _ = await self.seqr.get_response()


class RecoveryInterfaceSequence(uvm_sequence):
    """
    A sequence which drives recovery interface
    """

    def __init__(self, name, seqr, reg_map):
        self.reg_map = copy.deepcopy(reg_map)
        self.seqr = seqr
        self.finish_no_en = False
        super().__init__(name)

    async def body(self):
        while True:
            item = RegBusItem()
            item.wait_enable = True
            await self.seqr.start_item(item)
            await self.seqr.finish_item(item)
            sitem = RegBusItem()
            sitem.sample_bus = True
            await self.seqr.start_item(sitem)
            await self.seqr.finish_item(sitem)
            sample = await self.seqr.get_response()
            while sample.en == MuBiTrue:
                ritem = RegBusItem()
                ritem.rddata = self.reg_map[int(sample.rdaddr)]
                ritem.drive_rddata = True
                await self.seqr.start_item(ritem)
                await self.seqr.finish_item(ritem)
                if int(sample.write) == 1:
                    self.reg_map[int(sample.wraddr)] = int(sample.wrdata)
                sitem = RegBusItem()
                sitem.sample_bus = True
                await self.seqr.start_item(sitem)
                await self.seqr.finish_item(sitem)
                sample = await self.seqr.get_response()
            if sample.en == MuBiFalse:
                ritem = RegBusItem()
                ritem.rddata = 0
                ritem.drive_rddata = True
                await self.seqr.start_item(ritem)
                await self.seqr.finish_item(ritem)
                if self.finish_no_en:
                    break
