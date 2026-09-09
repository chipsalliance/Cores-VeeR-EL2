# Copyright (c) 2026 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0
import random

import cocotb
from cocotb.triggers import Timer
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
        period = ConfigDB().get(None, "", "TEST_CLK_PERIOD")
        iterations = ConfigDB().get(None, "", "TEST_ITERATIONS")

        cpu_sequencers = [ConfigDB().get(None, "", f"CPU_CTRL{i}_CPU_SEQ") for i in range(3)]
        gpr_sequencers = [ConfigDB().get(None, "", f"GPR{i}_SEQ") for i in range(3)]
        csr_sequencers = [ConfigDB().get(None, "", f"CSR{i}_SEQ") for i in range(3)]

        # Setup reactive sequences
        cpu_sequences = [
            CPUReactiveCtrlSequence(f"cpu_seq{i}", s) for i, s in zip(range(3), cpu_sequencers)
        ]
        for s in cpu_sequences:
            cocotb.start_soon(s.start())

        gpr_sequences = [
            RecoveryInterfaceSequence(f"gpr_seq{i}", s) for i, s in enumerate(gpr_sequencers)
        ]
        csr_sequences = [
            RecoveryInterfaceSequence(f"csr_seq{i}", s) for i, s in enumerate(csr_sequencers)
        ]

        for s in gpr_sequences:
            cocotb.start_soon(s.start())
        for s in csr_sequences:
            cocotb.start_soon(s.start())

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
            flag_sequencer = ConfigDB().get(None, "", "EXT_FLAG_SEQ")

            # Create sequences
            flag_sequence = ExternalFlagSequence("ext_flag_seq", flag_sequencer)

            for s in gpr_sequences:
                s.update_reg_map(gpr_state)
            for s in csr_sequences:
                s.update_reg_map(csr_state)

            # Start tasks
            fl_s = cocotb.start_soon(flag_sequence.start())

            await fl_s
            await Timer(20 * period)
            # Reset
            await self.reset()
