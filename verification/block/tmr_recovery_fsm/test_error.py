# Copyright (c) 2026 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0
import random

import cocotb
from cocotb.triggers import Combine, Timer
from common_fsm import (
    CPUReactiveCtrlSequence,
    ExternalFlagSequence,
    RecoveryInterfaceSequence,
    RegBusScoreboard,
)
from pyuvm import ConfigDB, test, uvm_sequence
from testbench import BaseTest

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

    def __str__(self):
        return f"TransactionSequence(items={self.items}, seqr={self.seqr})"


# =============================================================================


@test()
class TestRecoverableError(BaseTest):
    # There are always 32 GPRs, specified by ISA
    num_of_gprs = 32

    def __init__(self, name, parent):
        super().__init__(name, parent, RegBusScoreboard)

    async def run(self):
        period = ConfigDB().get(None, "", "TEST_CLK_PERIOD")
        iterations = ConfigDB().get(None, "", "TEST_ITERATIONS")

        flag_seqr = ConfigDB().get(None, "", "EXT_FLAG_SEQ")
        cpu_seqrs = [ConfigDB().get(None, "", f"CPU_CTRL{i}_CPU_SEQ") for i in range(3)]
        gpr_seqrs = [ConfigDB().get(None, "", f"GPR{i}_SEQ") for i in range(3)]
        csr_seqrs = [ConfigDB().get(None, "", f"CSR{i}_SEQ") for i in range(3)]

        for it in range(iterations):
            faulty_core = random.randint(0, 2)

            # Generate register values
            gpr_values = {}
            gpr_faulty_values = {}

            # Register x0 must always contain 0
            gpr_values[0] = 0
            gpr_faulty_values[0] = 0

            for i in range(1, self.num_of_gprs):
                gpr_values[i] = random.randrange(0, 2**32)
                gpr_faulty_values[i] = gpr_values[i] ^ random.randint(0, 2**32)

            zero_values = {}
            csr_values = {}
            csr_faulty_values = {}
            for i in range(2**12):
                zero_values[i] = 0
                csr_values[i] = random.randrange(0, 2**32)
                csr_faulty_values[i] = csr_values[i] ^ random.randint(0, 2**32)

            gpr_values_tmr = [gpr_values for _ in range(3)]
            gpr_values_tmr[faulty_core] = gpr_faulty_values

            csr_values_tmr = [csr_values for _ in range(3)]
            csr_values_tmr[faulty_core] = csr_faulty_values

            # Create sequences
            cpu_seqs = [
                CPUReactiveCtrlSequence(f"cpu_seq{i}", s) for i, s in zip(range(3), cpu_seqrs)
            ]
            flag_seq = ExternalFlagSequence("ext_flag_seq", flag_seqr)

            gpr_seqs = [
                RecoveryInterfaceSequence(f"gpr_seq{i}", s, gpr_vals)
                for i, s, gpr_vals in zip(range(3), gpr_seqrs, gpr_values_tmr)
            ]
            csr_seqs = [
                RecoveryInterfaceSequence(f"csr_seq{i}", s, csr_vals)
                for i, s, csr_vals in zip(range(3), csr_seqrs, csr_values_tmr)
            ]
            post_reset_gpr_seqs = [
                RecoveryInterfaceSequence(f"empty_gpr_seq{i}", s, zero_values)
                for i, s in zip(range(3), gpr_seqrs)
            ]
            post_reset_csr_seqs = [
                RecoveryInterfaceSequence(f"empty_csr_seq{i}", s, zero_values)
                for i, s in zip(range(3), csr_seqrs)
            ]
            for s in [*gpr_seqs, *csr_seqs, *post_reset_gpr_seqs, *post_reset_csr_seqs]:
                s.finish_no_en = True

            # Start tasks
            self.logger.debug("Starting the test")
            for s in cpu_seqs:
                cocotb.start_soon(s.start())
            fl_s = cocotb.start_soon(flag_seq.start())

            reg_tasks = [cocotb.start_soon(s.start()) for s in gpr_seqs]
            reg_tasks.extend([cocotb.start_soon(s.start()) for s in csr_seqs])
            await Combine(*reg_tasks)

            reg_tasks = [cocotb.start_soon(s.start()) for s in post_reset_gpr_seqs]
            reg_tasks.extend([cocotb.start_soon(s.start()) for s in post_reset_csr_seqs])
            await Combine(*reg_tasks)

            await fl_s
            await Timer(20 * period)

            # Reset
            await self.reset()
