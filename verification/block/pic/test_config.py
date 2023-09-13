# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0
import random

import pyuvm
from pyuvm import *
from testbench import BaseEnv, BaseTest, BusReadItem, BusWriteItem, RegisterMap

# =============================================================================


class TestSequence(uvm_sequence):
    """
    A sequence of randomized register and content writes followed by randomized
    reads of them.
    """

    def __init__(self, name):
        super().__init__(name)
        self.reg_map = RegisterMap()

    async def body(self):
        num_itr = ConfigDB().get(None, "", "TEST_ITERATIONS")
        max_pri = ConfigDB().get(None, "", "PIC_NUM_PRIORITIES")

        for i in range(num_itr):
            # Issue register writes
            names = list(self.reg_map.reg.keys())
            random.shuffle(names)

            written = []

            for name in names:
                reg = self.reg_map.reg[name]
                val = None

                if name.startswith("meipl"):
                    val = random.randint(0, max_pri)
                elif name.startswith("meigwctrl"):
                    val = random.randint(0, 3)  # 2-bit combinations
                elif name.startswith("meie"):
                    val = random.randint(0, 1)  # 1-bit combinations

                if val is None:
                    continue

                item = BusWriteItem(reg, val)
                await self.start_item(item)
                await self.finish_item(item)

                written.append(reg)

            # Issue register reads for the written ones
            random.shuffle(written)

            for reg in written:
                item = BusReadItem(reg)
                await self.start_item(item)
                await self.finish_item(item)


class Scoreboard(uvm_component):
    """
    A scoreboard that keeps track of data written to registers and compares
    it with data read afterwards.
    """

    def __init__(self, name, parent):
        super().__init__(name, parent)

        self.passed = None
        self.reg_map = RegisterMap()
        self.reg_content = dict()

    def build_phase(self):
        self.fifo = uvm_tlm_analysis_fifo("fifo", self)
        self.port = uvm_get_port("port", self)

    def connect_phase(self):
        self.port.connect(self.fifo.get_export)

    def check_phase(self):
        while self.port.can_get():
            # Get an item
            got_item, item = self.port.try_get()
            assert got_item

            # Initially pass
            if self.passed is None:
                self.passed = True

            # Bus write
            if isinstance(item, BusWriteItem):
                self.reg_content[item.addr] = item.data

            # Bus read
            elif isinstance(item, BusReadItem):
                # Get register name
                reg_name = "0x{:08X}".format(item.addr)
                name = self.reg_map.adr.get(item.addr)
                if name is not None:
                    reg_name += " '{}'".format(name)

                # No entry
                golden = self.reg_content.get(item.addr)
                if golden is None:
                    self.logger.error("Register {} was not written".format(reg_name))
                    self.passed = False

                # Mismatch
                elif golden != item.data:
                    self.logger.error(
                        "Register {} content mismatch, is 0x{:08X} should be 0x{:08X}".format(
                            reg_name, item.data, golden
                        )
                    )
                    self.passed = False
                else:
                    self.logger.debug(
                        "Register {} ok, 0x{:08X}".format(
                            reg_name,
                            item.data,
                        )
                    )

    def final_phase(self):
        if not self.passed:
            self.logger.critical("{} reports a failure".format(type(self)))
            assert False


# ==============================================================================


class TestEnv(BaseEnv):
    def build_phase(self):
        super().build_phase()

        # Add scoreboard
        self.scoreboard = Scoreboard("scoreboard", self)

    def connect_phase(self):
        super().connect_phase()

        # Connect monitors
        self.reg_mon.ap.connect(self.scoreboard.fifo.analysis_export)


@pyuvm.test()
class TestConfig(BaseTest):
    """
    A test for PIC configuration register access
    """

    def __init__(self, name, parent):
        super().__init__(name, parent, TestEnv)

    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = TestSequence.create("stimulus")

    async def run(self):
        await self.seq.start(self.env.reg_seqr)
