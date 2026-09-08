# Copyright (c) 2026 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0
import copy

from pyuvm import uvm_sequence
from testbench import (
    BaseScoreboard,
    CPUCtrlStatusItem,
    ExtFlagsItem,
    MuBiFalse,
    MuBiTrue,
    RegBusItem,
)


class RegBusScoreboard(BaseScoreboard):

    def check_phase(self):
        self.passed = True

        def majority_vote(val1, val2, val3):
            """
            Vote for the correct value based on 3 inputs. If not possible to pick the winner, return None.
            """
            if val1 == val2:
                return val1
            elif val2 == val3:
                return val2
            elif val1 == val3:
                return val3
            else:
                return None

        def check_if_transfers(if_name):
            assert if_name in ["gpr", "csr"]

            recovery_ports = getattr(self, f"recovery_{if_name}_ports")
            reg_reads = [{}, {}, {}]
            while (
                recovery_ports[0].can_get()
                and recovery_ports[1].can_get()
                and recovery_ports[2].can_get()
            ):
                tr = [None for _ in range(3)]

                # Collect simultaneous transactions
                for i in range(3):
                    _, tr[i] = recovery_ports[i].try_get()
                    if not isinstance(tr[i], RegBusItem):
                        self.passed = False
                        continue

                    read_reg_value = reg_reads[i].get(int(tr[i].rdaddr))
                    if tr[i].write and (read_reg_value is None):
                        self.passed = False
                        self.logger.error(
                            f"[{tr[i].timestamp}] {if_name.upper()} written without prior read at this address"
                        )
                        continue

                    if not tr[i].write:
                        # Save read value for later comparison
                        reg_reads[i][int(tr[i].rdaddr)] = int(tr[i].rddata)
                        self.logger.debug(
                            f"[{tr[i].timestamp}] {if_name.upper()} read value {hex(tr[i].rddata)} at {hex(tr[i].rdaddr)}"
                        )

                if not (tr[0].timestamp == tr[1].timestamp == tr[2].timestamp):
                    self.passed = False
                    self.logger.error(
                        f"Received {if_name.upper()} transactions do not match in time"
                    )
                    break

                rddata = majority_vote(
                    reg_reads[0][int(tr[0].rdaddr)],
                    reg_reads[1][int(tr[1].rdaddr)],
                    reg_reads[2][int(tr[2].rdaddr)],
                )
                if rddata is None:
                    self.logger.error("Voter failed")
                    continue

                for i in range(3):
                    if tr[i].write:
                        if rddata != int(tr[i].wrdata):
                            self.passed = False
                            self.logger.error(
                                f"[{tr[i].timestamp}] {if_name.upper()} written different value than earlier read at address {hex(tr[i].wraddr)}, expected: {hex(rddata)}, got: {hex(tr[i].wrdata)}"
                            )
                            continue
                        if int(tr[i].rddata) not in [0, int(tr[i].wrdata)]:
                            self.passed = False
                            self.logger.error(
                                f"[{tr[i].timestamp}] During write, read data should be either 0 or equal to write data"
                            )
                            continue
                        if int(tr[i].wraddr) != int(tr[i].rdaddr):
                            self.passed = False
                            self.logger.error(
                                f"[{tr[i].timestamp}] Simultaneous read and write on {if_name.upper()} interface is only allowed at the same address"
                            )
                            continue

        check_if_transfers("gpr")
        check_if_transfers("csr")


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
