# Copyright (c) 2026 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0
import random

import cocotb
from cocotb.triggers import Timer
from common_fsm import (
    CPUNoHaltReactiveCtrlSequence,
    CPUReactiveCtrlSequence,
    ExternalFlagSequence,
    RecoveryInterfaceSequence,
    RegBusScoreboard,
)
from pyuvm import ConfigDB, test, uvm_sequence
from testbench import BaseTest

# =============================================================================


@test()
class TestNoHaltRecovery(BaseTest):
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

        gpr_seqs = [RecoveryInterfaceSequence(f"gpr_seq{i}", s) for i, s in enumerate(gpr_seqrs)]
        csr_seqs = [RecoveryInterfaceSequence(f"csr_seq{i}", s) for i, s in enumerate(csr_seqrs)]

        for s in [*gpr_seqs, *csr_seqs]:
            cocotb.start_soon(s.start())

        for it in range(iterations):
            faulty_core = random.randint(0, 2)

            # Generate register values
            gpr_values = {}

            for i in range(self.num_of_gprs):
                gpr_values[i] = random.randrange(0, 2**32)

            csr_values = {}
            for i in range(2**12):
                csr_values[i] = random.randrange(0, 2**32)

            # Setup reactive sequences
            cpu_seqs = []
            for i, s in zip(range(3), cpu_seqrs):
                if i != faulty_core:
                    cpu_seqs.append(
                        CPUReactiveCtrlSequence(f"cpu_seq{i}", s, stop_on_hard_reset=True)
                    )
                else:
                    cpu_seqs.append(
                        CPUNoHaltReactiveCtrlSequence(f"cpu_seq{i}", s, stop_on_hard_reset=True)
                    )
            for s in cpu_seqs:
                cocotb.start_soon(s.start())

            for s in gpr_seqs:
                s.update_reg_map(gpr_values)
            for s in csr_seqs:
                s.update_reg_map(csr_values)

            gpr_seqs[faulty_core].arm_random_response()
            csr_seqs[faulty_core].arm_random_response()

            # Create sequences
            flag_seq = ExternalFlagSequence("ext_flag_seq", flag_seqr, faulty_core=faulty_core)

            # Start tasks
            self.logger.debug("Starting the test")
            fl_s = cocotb.start_soon(flag_seq.start())

            await fl_s
            await Timer(20 * period)

            # Reset
            await self.reset()
