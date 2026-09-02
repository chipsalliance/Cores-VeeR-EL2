# Copyright (c) 2026 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0
import random

import cocotb
from cocotb.triggers import Combine, Timer
from pyuvm import ConfigDB, test, uvm_sequence
from testbench import (
    BaseScoreboard,
    BaseTest,
    CPUCtrlStatusItem,
)

# =============================================================================


class PassthroughScoreboard(BaseScoreboard):

    def check_phase(self):

        # Collect all CPU Ctrl items
        self.passed = True
        for i in range(3):
            while self.external_cpu_ctrl_ports[i].can_get():
                if not self.internal_cpu_ctrl_ports[i].can_get():
                    self.logger.error("No more transactions observed on the CPU side")
                    self.passed = False
                    break
                _, tr_soc = self.internal_cpu_ctrl_ports[i].try_get()
                _, tr_cpu = self.external_cpu_ctrl_ports[i].try_get()
                if not isinstance(tr_soc, CPUCtrlStatusItem):
                    self.passed = False
                    continue
                if not isinstance(tr_cpu, CPUCtrlStatusItem):
                    self.passed = False
                    continue
                if tr_soc.timestamp != tr_cpu.timestamp:
                    self.logger.error(
                        f"Wrong timestamp CPU={tr_cpu.timestamp}, SoC={tr_soc.timestamp}"
                    )
                    self.passed = False
                    continue
                if tr_soc != tr_cpu:
                    self.logger.error(f"CPU={tr_cpu} not equal SoC={tr_soc}")
                    self.passed = False
                    continue
            if self.internal_cpu_ctrl_ports[i].can_get():
                self.logger.error("No more transactions observed on the SOC side")
                self.passed = False


# =============================================================================


class TransactionSequence(uvm_sequence):
    """
    A sequence which plays the given list of items
    """

    def __init__(self, name, items, seqr):
        self.items = items
        self.seqr = seqr
        super().__init__(name)

    async def body(self):
        for item in self.items:
            await self.seqr.start_item(item)
            await self.seqr.finish_item(item)


# =============================================================================


@test()
class TestPassthrough(BaseTest):
    def __init__(self, name, parent):
        super().__init__(name, parent, PassthroughScoreboard)

    async def run(self):
        period = ConfigDB().get(None, "", "TEST_CLK_PERIOD")
        iterations = ConfigDB().get(None, "", "TEST_ITERATIONS")

        for it in range(iterations):

            # Generate random items
            soc_items = []
            cpu_items = []
            for i in range(3):
                soc_sub_array = []
                cpu_sub_array = []
                for i in range(20):
                    soc_item = CPUCtrlStatusItem()
                    soc_item.drive_ext = True
                    soc_item.i_cpu_halt_req = random.randint(0, 1)
                    soc_item.i_cpu_run_req = random.randint(0, 1)
                    soc_item.mpc_reset_run_req = random.randint(0, 1)
                    soc_sub_array.append(soc_item)

                    cpu_item = CPUCtrlStatusItem()
                    cpu_item.drive_ext = True
                    cpu_item.o_cpu_halt_ack = random.randint(0, 1)
                    cpu_item.o_cpu_halt_status = random.randint(0, 1)
                    cpu_item.o_cpu_run_ack = random.randint(0, 1)
                    cpu_sub_array.append(cpu_item)

                soc_items.append(soc_sub_array)
                cpu_items.append(cpu_sub_array)

            # Get sequencers
            cpu_sequencers = [ConfigDB().get(None, "", f"CPU_CTRL{i}_CPU_SEQ") for i in range(3)]
            soc_sequencers = [ConfigDB().get(None, "", f"CPU_CTRL{i}_SOC_SEQ") for i in range(3)]

            # Create sequences
            cpu_sequences = [
                TransactionSequence(f"cpu_seq{i}", it, s)
                for i, it, s in zip(range(3), cpu_items, cpu_sequencers)
            ]
            soc_sequences = [
                TransactionSequence(f"soc_seq{i}", it, s)
                for i, it, s in zip(range(3), soc_items, soc_sequencers)
            ]

            # Start tasks
            tasks = [cocotb.start_soon(s.start()) for s in cpu_sequences]
            tasks.extend([cocotb.start_soon(s.start()) for s in soc_sequences])
            timer = Timer(20 * period)

            await Combine(*tasks, timer)

            # Reset
            await self.reset()
