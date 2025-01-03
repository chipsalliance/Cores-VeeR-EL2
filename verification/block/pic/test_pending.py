# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0
import random

import cocotb
import pyuvm
from cocotb.triggers import ClockCycles
from pyuvm import *
from testbench import BaseEnv, BaseTest, BusReadItem, BusWriteItem, IrqItem, RegisterMap

# =============================================================================


class TestSequence(uvm_sequence):
    def __init__(self, name):
        super().__init__(name)

        self.reg_seqr = ConfigDB().get(None, "", "REG_SEQR")
        self.irq_seqr = ConfigDB().get(None, "", "IRQ_SEQR")

        self.regs = RegisterMap()

    async def body(self):
        num_irq = ConfigDB().get(None, "", "PIC_NUM_INTERRUPTS")

        # Disable all interrupts
        for i in range(1, num_irq):
            reg = self.regs.reg["meie{}".format(i)]

            item = BusWriteItem(reg, 0)
            await self.reg_seqr.start_item(item)
            await self.reg_seqr.finish_item(item)

        # Configure gateways
        for i in range(1, num_irq):
            reg = self.regs.reg["meigwctrl{}".format(i)]
            val = 0x2  # Edge, active-high

            item = BusWriteItem(reg, val)
            await self.reg_seqr.start_item(item)
            await self.reg_seqr.finish_item(item)

        # Wait
        await ClockCycles(cocotb.top.clk, 4)

        # Randomize IRQ
        irqs = 0
        while irqs == 0:
            for i in range(1, num_irq):
                if random.random() > 0.5:
                    irqs |= 1 << i

        item = IrqItem(irqs)
        await self.irq_seqr.start_item(item)
        await self.irq_seqr.finish_item(item)

        # Read IRQ pending status register(s)
        num_meip = (num_irq + 31) // 32
        for i in range(0, num_meip):
            reg = self.regs.reg["meip{}".format(i)]
            item = BusReadItem(reg)
            await self.reg_seqr.start_item(item)
            await self.reg_seqr.finish_item(item)


# ==============================================================================


class Scoreboard(uvm_component):
    def __init__(self, name, parent):
        super().__init__(name, parent)

        self.passed = None
        self.regs = RegisterMap()

    def build_phase(self):
        self.fifo = uvm_tlm_analysis_fifo("fifo", self)
        self.port = uvm_get_port("port", self)

    def connect_phase(self):
        self.port.connect(self.fifo.get_export)

    def check_phase(self):

        irqs = 0

        while self.port.can_get():
            _, item = self.port.try_get()

            # Register read
            if isinstance(item, BusReadItem):
                # Get the reg name
                reg = self.regs.adr.get(item.addr)
                if not reg:
                    self.logger.error("Unknown register address 0x{:08X}".format(item.addr))
                    self.passed = False
                    continue

                # This is a meipX register
                if reg.startswith("meip") and reg[4] != "l":
                    x = int(reg[4:])

                    # Initially pass
                    if self.passed is None:
                        self.passed = True

                    # Check if the content matches current IRQ pending status
                    mask = 0xFFFFFFFF << (32 * x)
                    pend = item.data << (32 * x)
                    if irqs & mask != pend:
                        self.logger.error(
                            f"{reg} value {item.data:032b} does not match IRQ state {irqs:032b}"
                        )
                        self.passed = False
                        continue

            # IRQ state
            elif isinstance(item, IrqItem):
                irqs = item.irqs

    def final_phase(self):
        if not self.passed:
            self.logger.critical("{} reports a failure".format(type(self)))
            assert False


# ==============================================================================


class TestEnv(BaseEnv):
    def build_phase(self):
        super().build_phase()

        # Increase iteration count
        count = ConfigDB().get(None, "", "TEST_ITERATIONS")
        ConfigDB().set(None, "*", "TEST_ITERATIONS", count * 2)

        # Add scoreboard
        self.scoreboard = Scoreboard("scoreboard", self)

    def connect_phase(self):
        super().connect_phase()

        # Connect monitors
        self.reg_mon.ap.connect(self.scoreboard.fifo.analysis_export)
        self.irq_mon.ap.connect(self.scoreboard.fifo.analysis_export)


@pyuvm.test()
class TestPending(BaseTest):
    """
    Test reporting of pending IRQs
    """

    def __init__(self, name, parent):
        super().__init__(name, parent, TestEnv)

    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = TestSequence.create("stimulus")

    async def run(self):
        count = ConfigDB().get(None, "", "TEST_ITERATIONS")
        for i in range(count):
            await self.seq.start()
            await self.do_reset()
