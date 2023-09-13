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
        irq_prob = ConfigDB().get(None, "", "TEST_IRQ_REQ_PROB")

        # Basic PIC config
        item = BusWriteItem(self.regs.reg["mpiccfg"], random.randint(0, 1))
        await self.reg_seqr.start_item(item)
        await self.reg_seqr.finish_item(item)

        for i in range(num_itr):
            # Randomize priorities
            for i in range(1, num_irq):
                reg = self.regs.reg["meipl{}".format(i)]
                val = random.randint(0, max_pri)

                item = BusWriteItem(reg, val)
                await self.reg_seqr.start_item(item)
                await self.reg_seqr.finish_item(item)

            # Randomize enables
            for i in range(1, num_irq):
                reg = self.regs.reg["meie{}".format(i)]
                val = int(random.random() < ena_prob)

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

            # Randomize current priority and threshold
            lvl = random.randint(0, max_pri)
            thr = random.randint(0, max_pri)

            item = PrioLvlItem(lvl)
            await self.pri_seqr.start_item(item)
            await self.pri_seqr.finish_item(item)

            item = PrioThrItem(thr)
            await self.pri_seqr.start_item(item)
            await self.pri_seqr.finish_item(item)

            # Wait
            await ClockCycles(cocotb.top.clk, 4)

            # Randomize IRQ
            irqs = 0
            while irqs == 0:
                for i in range(1, num_irq):
                    if random.random() > irq_prob:
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

            # Clear pending gateways
            for i in range(1, num_irq):
                if irqs & (1 << i):
                    reg = self.regs.reg["meigwclr{}".format(i)]
                    val = 0

                    item = BusWriteItem(reg, val)
                    await self.reg_seqr.start_item(item)
                    await self.reg_seqr.finish_item(item)

            # Wait
            await ClockCycles(cocotb.top.clk, 5)


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
        max_pri = ConfigDB().get(None, "", "PIC_NUM_PRIORITIES")

        pri_lvl = 0
        pri_thr = 0
        irqs = 0

        claimid = 0
        mexintpend = 0
        mhwakeup = 0

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

                if reg == "mpiccfg":
                    self.predictor.inv_order = bool(item.data)

            # Priority level
            elif isinstance(item, PrioLvlItem):
                pri_lvl = item.prio

            # Priority threshold
            elif isinstance(item, PrioThrItem):
                pri_thr = item.prio

            # IRQ
            elif isinstance(item, IrqItem):
                # Mark triggered interrupts
                for i in range(1, num_irq):
                    if item.irqs & (1 << i):
                        self.predictor.irqs[i].triggered = True

                # Store requested irqs
                if item.irqs != 0:
                    irqs = item.irqs

            # Interrupt claim
            elif isinstance(item, ClaimItem):
                claimid = item.claimid
                mexintpend = item.mexintpend
                mhwakeup = item.mhwakeup

                # Check only if IRQs were requested
                if not irqs:
                    continue
                irqs = 0

                # Initially pass
                if self.passed is None:
                    self.passed = True

                # Predict the claim
                pred = self.predictor.predict()

                # Check
                if claimid != pred.id:
                    self.logger.error(
                        "Interrupt mismatch, is {} should be {}".format(claimid, pred.id)
                    )
                    self.passed = False

                # Check if the interrupt is above the current priority level
                # and threshold. Check if it is signaled correctly.
                else:
                    # Predict mexintpend
                    if self.predictor.inv_order:
                        pred_mexintpend = (
                            pred.id != 0
                            and pred.priority != max_pri
                            and pred.priority < pri_thr
                            and pred.priority < pri_lvl
                        )
                    else:
                        pred_mexintpend = (
                            pred.id != 0
                            and pred.priority != 0
                            and pred.priority > pri_thr
                            and pred.priority > pri_lvl
                        )

                    # Predict mhwakeup
                    if self.predictor.inv_order:
                        pred_mhwakeup = pred.id != 0 and pred.priority == 0
                    else:
                        pred_mhwakeup = pred.id != 0 and pred.priority == max_pri

                    # Check
                    if pred_mexintpend != mexintpend:
                        self.logger.error(
                            "Signaling mismatch, mexintpend is {} should be {}. irq {}, meicurpl={}, meipt={}".format(
                                bool(mexintpend),
                                bool(pred_mexintpend),
                                pred.id,
                                pri_lvl,
                                pri_thr,
                            )
                        )
                        self.passed = False

                    if pred_mhwakeup != mhwakeup:
                        self.logger.error(
                            "Signaling mismatch, mhwakeup is {} should be {}. irq {}, meicurpl={}, meipt={}".format(
                                bool(mhwakeup),
                                bool(pred_mhwakeup),
                                pred.id,
                                pri_lvl,
                                pri_thr,
                            )
                        )
                        self.passed = False

                # Clear triggers
                for i in range(1, num_irq):
                    self.predictor.irqs[i].triggered = False

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
class TestPrioritization(BaseTest):
    """ """

    def __init__(self, name, parent):
        super().__init__(name, parent, TestEnv)

    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = TestSequence.create("stimulus")

    async def run(self):
        await self.seq.start()
