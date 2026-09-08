# Copyright (c) 2026 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0
import random

import cocotb
from cocotb.triggers import Combine
from common_fsm import (
    CPUReactiveCtrlSequence,
    ExternalFlagSequence,
    RecoveryInterfaceSequence,
    RegBusScoreboard,
)
from pyuvm import ConfigDB, test
from testbench import BaseTest

# =============================================================================


@test()
class TestNoErrs(BaseTest):
    def __init__(self, name, parent):
        super().__init__(name, parent, RegBusScoreboard)

    async def run(self):
        iterations = ConfigDB().get(None, "", "TEST_ITERATIONS")

        for it in range(iterations):

            # Generate register values
            gpr_state = {}
            empty_gpr_state = {}
            for i in range(32):
                gpr_state[i] = random.randrange(0, 2**32)
                empty_gpr_state[i] = 0

            csr_state = {}
            empty_csr_state = {}
            for i in range(2**12):
                csr_state[i] = random.randrange(0, 2**32)
                empty_csr_state[i] = 0

            # Get sequencers
            cpu_sequencers = [ConfigDB().get(None, "", f"CPU_CTRL{i}_CPU_SEQ") for i in range(3)]

            flag_sequencer = ConfigDB().get(None, "", "EXT_FLAG_SEQ")

            gpr_sequencers = [ConfigDB().get(None, "", f"GPR{i}_SEQ") for i in range(3)]
            csr_sequencers = [ConfigDB().get(None, "", f"CSR{i}_SEQ") for i in range(3)]

            # Create sequences
            cpu_sequences = [
                CPUReactiveCtrlSequence(f"cpu_seq{i}", s) for i, s in zip(range(3), cpu_sequencers)
            ]

            flag_sequence = ExternalFlagSequence("ext_flag_seq", flag_sequencer)

            gpr_sequences = [
                RecoveryInterfaceSequence(f"gpr_seq{i}", s, gpr_state)
                for i, s in zip(range(3), gpr_sequencers)
            ]
            csr_sequences = [
                RecoveryInterfaceSequence(f"csr_seq{i}", s, csr_state)
                for i, s in zip(range(3), csr_sequencers)
            ]
            post_reset_gpr_sequences = [
                RecoveryInterfaceSequence(f"empty_gpr_seq{i}", s, empty_gpr_state)
                for i, s in zip(range(3), gpr_sequencers)
            ]
            post_reset_csr_sequences = [
                RecoveryInterfaceSequence(f"empty_csr_seq{i}", s, empty_csr_state)
                for i, s in zip(range(3), csr_sequencers)
            ]
            for s in [
                *gpr_sequences,
                *csr_sequences,
                *post_reset_gpr_sequences,
                *post_reset_csr_sequences,
            ]:
                s.finish_no_en = True

            # Start tasks
            for s in cpu_sequences:
                cocotb.start_soon(s.start())
            fl_s = cocotb.start_soon(flag_sequence.start())

            reg_tasks = [cocotb.start_soon(s.start()) for s in gpr_sequences]
            reg_tasks.extend([cocotb.start_soon(s.start()) for s in csr_sequences])
            await Combine(*reg_tasks)

            reg_tasks = [cocotb.start_soon(s.start()) for s in post_reset_gpr_sequences]
            reg_tasks.extend([cocotb.start_soon(s.start()) for s in post_reset_csr_sequences])
            await Combine(*reg_tasks)

            await fl_s
            # Reset
            await self.reset()
