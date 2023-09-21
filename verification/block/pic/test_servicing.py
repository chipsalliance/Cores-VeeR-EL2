# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0
import random

import cocotb
import pyuvm
from cocotb.triggers import ClockCycles
from pyuvm import *
from testbench import (
    BaseEnv,
    BaseTest,
    BusReadItem,
    BusWriteItem,
    ClaimItem,
    IrqItem,
    PrioLvlItem,
    PriorityPredictor,
    PrioThrItem,
    RegisterMap,
)

# =============================================================================


class TestSequence(uvm_sequence):
    def __init__(self, name):
        super().__init__(name)

        self.reg_seqr = ConfigDB().get(None, "", "REG_SEQR")
        self.pri_seqr = ConfigDB().get(None, "", "PRI_SEQR")
        self.irq_seqr = ConfigDB().get(None, "", "IRQ_SEQR")

        self.regs = RegisterMap()

    async def body(self):
        num_irq = ConfigDB().get(None, "", "PIC_NUM_INTERRUPTS")
        max_pri = ConfigDB().get(None, "", "PIC_NUM_PRIORITIES")
        num_itr = ConfigDB().get(None, "", "TEST_ITERATIONS")
        ena_prob = ConfigDB().get(None, "", "TEST_IRQ_ENA_PROB")

        # Basic PIC config
        item = BusWriteItem(self.regs.reg["mpiccfg"], 0)
        await self.reg_seqr.start_item(item)
        await self.reg_seqr.finish_item(item)

        predictor = PriorityPredictor()
        enabled_irqs = list()

        for i in range(num_itr):
            # Randomize priorities
            for i in range(1, num_irq):
                reg = self.regs.reg["meipl{}".format(i)]
                val = random.randint(0, max_pri)

                predictor.irqs[i].priority = val

                item = BusWriteItem(reg, val)
                await self.reg_seqr.start_item(item)
                await self.reg_seqr.finish_item(item)

            # Randomize enables
            for i in range(1, num_irq):
                reg = self.regs.reg["meie{}".format(i)]
                val = int(random.random() < ena_prob)

                predictor.irqs[i].enabled = val

                if val:
                    enabled_irqs.append(i)

                item = BusWriteItem(reg, val)
                await self.reg_seqr.start_item(item)
                await self.reg_seqr.finish_item(item)

            # Configure gateways
            for i in range(1, num_irq):
                reg = self.regs.reg["meigwctrl{}".format(i)]
                val = 0x2  # Edge, active-high

                item = BusWriteItem(reg, val)
                await self.reg_seqr.start_item(item)
                await self.reg_seqr.finish_item(item)

            # Set interrupt threshold
            item = PrioThrItem(random.randint(0, max_pri))
            await self.pri_seqr.start_item(item)
            await self.pri_seqr.finish_item(item)

            # Wait
            await ClockCycles(cocotb.top.clk, 4)

            # Request IRQs
            irqs = 0
            for i in enabled_irqs:
                predictor.irqs[i].triggered = val
                irqs |= 1 << i

            item = IrqItem(irqs)
            await self.irq_seqr.start_item(item)
            await self.irq_seqr.finish_item(item)

            # Wait
            await ClockCycles(cocotb.top.clk, 2)

            # Clear IRQ
            item = IrqItem(0)
            await self.irq_seqr.start_item(item)
            await self.irq_seqr.finish_item(item)

            # Wait
            await ClockCycles(cocotb.top.clk, 4)

            # Mimic interrupt servicing
            for i in range(50):  # Limit iterations
                # Predict the IRQ to be serviced
                irq = predictor.predict()
                if irq.id == 0:
                    break

                # Begin servicing, set meicurpl
                item = PrioLvlItem(irq.priority)
                await self.pri_seqr.start_item(item)
                await self.pri_seqr.finish_item(item)

                # Servicing period
                await ClockCycles(cocotb.top.clk, 5)

                # Finish servicing, set meicurpl to 0
                item = PrioLvlItem(0)
                await self.pri_seqr.start_item(item)
                await self.pri_seqr.finish_item(item)

                # Clear pending
                reg = self.regs.reg["meigwclr{}".format(irq.id)]
                val = 0

                item = BusWriteItem(reg, val)
                await self.reg_seqr.start_item(item)
                await self.reg_seqr.finish_item(item)

                predictor.irqs[irq.id].triggered = False

                await ClockCycles(cocotb.top.clk, 4)


# ==============================================================================


class Scoreboard(uvm_component):
    def __init__(self, name, parent):
        super().__init__(name, parent)

        self.passed = None
        self.predictor = PriorityPredictor(self.logger)
        self.regs = RegisterMap()

    def build_phase(self):
        self.fifo = uvm_tlm_analysis_fifo("fifo", self)
        self.port = uvm_get_port("port", self)

    def connect_phase(self):
        self.port.connect(self.fifo.get_export)

    def check_phase(self):
        num_irq = ConfigDB().get(None, "", "PIC_NUM_INTERRUPTS")

        pri_thr = 0

        irq_order = []

        while self.port.can_get():
            _, item = self.port.try_get()

            # Register write
            if isinstance(item, BusWriteItem):
                # Get the reg name
                reg = self.regs.adr.get(item.addr)
                if not reg:
                    self.logger.error("Unknown register address 0x{:08X}".format(item.addr))
                    self.passed = False
                    continue

                if reg.startswith("meipl"):
                    s = int(reg[5:])
                    self.predictor.irqs[s].priority = item.data

                if reg.startswith("meie"):
                    s = int(reg[4:])
                    self.predictor.irqs[s].enabled = bool(item.data)

            # Priority threshold
            elif isinstance(item, PrioThrItem):
                pri_thr = item.prio

            # IRQ
            elif isinstance(item, IrqItem):
                # Nothing triggered
                if not item.irqs:
                    continue

                # Mark triggered interrupts
                for i in range(1, num_irq):
                    if item.irqs & (1 << i):
                        self.predictor.irqs[i].triggered = True

                # Predict the order of interrupt servicing
                for i in range(50):  # Limit iterations
                    # Predict the IRQ to be serviced
                    irq = self.predictor.predict()
                    if irq.id == 0:
                        break

                    irq_order.append(irq.id)

                    # Clear pending
                    self.predictor.irqs[irq.id].triggered = False

                self.logger.debug("Interrupt order: {}".format(irq_order))

            # Interrupt claim
            elif isinstance(item, ClaimItem):
                # Not waiting for any interrupt
                if not irq_order:
                    continue

                # Initially pass
                if self.passed is None:
                    self.passed = True

                self.logger.debug(
                    "Servicing {}, mexintpend={}".format(
                        item.claimid,
                        item.mexintpend,
                    )
                )

                # check id
                if item.claimid != irq_order[0]:
                    self.logger.error(
                        "Incorrect interrupt servicing order, claimed {} should be {}".format(
                            item.claimid, irq_order[0]
                        )
                    )
                    self.passed = False

                # mexintpend must be set
                if not item.mexintpend and item.claimpl > pri_thr:
                    self.logger.error("Interrupt not reported to the core")
                    self.passed = False

                # Remove the serviced id
                irq_order = irq_order[1:]

        # Check if all interrupts were services
        if irq_order:
            self.logger.error("Interrupts {} were not serviced".format(irq_order))
            self.passed = False

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
        self.pri_mon.ap.connect(self.scoreboard.fifo.analysis_export)
        self.irq_mon.ap.connect(self.scoreboard.fifo.analysis_export)
        self.claim_mon.ap.connect(self.scoreboard.fifo.analysis_export)


@pyuvm.test()
class TestServicing(BaseTest):
    """ """

    def __init__(self, name, parent):
        super().__init__(name, parent, TestEnv)

    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = TestSequence.create("stimulus")

    async def run(self):
        await self.seq.start()
