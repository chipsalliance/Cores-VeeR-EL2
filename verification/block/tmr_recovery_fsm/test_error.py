# Copyright (c) 2026 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0
import copy
import logging
import random

import cocotb
from cocotb.triggers import Combine, First, ReadWrite, RisingEdge, Timer
from common_fsm import (
    CPUReactiveCtrlSequence,
    ExternalFlagSequence,
    RecoveryInterfaceSequence,
    RegBusScoreboard,
)
from pyuvm import ConfigDB, test, uvm_sequence
from testbench import MCSR, UCSR, BaseTest, ExtFlagsItem, MuBiFalse, MuBiTrue

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

        # Setup reactive sequences
        cpu_seqs = [CPUReactiveCtrlSequence(f"cpu_seq{i}", s) for i, s in zip(range(3), cpu_seqrs)]
        gpr_seqs = [RecoveryInterfaceSequence(f"gpr_seq{i}", s) for i, s in enumerate(gpr_seqrs)]
        csr_seqs = [RecoveryInterfaceSequence(f"csr_seq{i}", s) for i, s in enumerate(csr_seqrs)]

        for s in [*gpr_seqs, *csr_seqs, *cpu_seqs]:
            cocotb.start_soon(s.start())

        for it in range(iterations):
            self.logger.debug(f"Initializing the test, iteration {it}")
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

            for i, s in enumerate(gpr_seqs):
                s.update_reg_map(gpr_values_tmr[i])
            for i, s in enumerate(csr_seqs):
                s.update_reg_map(csr_values_tmr[i])

            # Create sequences
            flag_seq = ExternalFlagSequence("ext_flag_seq", flag_seqr, faulty_core=faulty_core)

            # Start tasks
            self.logger.debug("Starting the test")
            fl_s = cocotb.start_soon(flag_seq.start())

            await fl_s
            await Timer(20 * period)

            # Reset
            await self.reset()


@test()
class TestFatalError(BaseTest):
    # There are always 32 GPRs, specified by ISA
    num_of_gprs = 32

    def __init__(self, name, parent):
        super().__init__(name, parent, RegBusScoreboard)

    async def run(self):

        async def wait_for_fatal_err():
            while cocotb.top.fatal_err.value != MuBiTrue:
                await RisingEdge(cocotb.top.clk)
                await ReadWrite()
            self.logger.debug("Success! Fatal error from FSM detected")

        user_mode = ConfigDB().get(None, "", "USER_MODE")
        CSRs = MCSR if not user_mode else UCSR
        iterations = ConfigDB().get(None, "", "TEST_ITERATIONS")

        flag_seqr = ConfigDB().get(None, "", "EXT_FLAG_SEQ")
        cpu_seqrs = [ConfigDB().get(None, "", f"CPU_CTRL{i}_CPU_SEQ") for i in range(3)]
        gpr_seqrs = [ConfigDB().get(None, "", f"GPR{i}_SEQ") for i in range(3)]
        csr_seqrs = [ConfigDB().get(None, "", f"CSR{i}_SEQ") for i in range(3)]

        cpu_seqs = [CPUReactiveCtrlSequence(f"cpu_seq{i}", s) for i, s in zip(range(3), cpu_seqrs)]
        gpr_seqs = [RecoveryInterfaceSequence(f"gpr_seq{i}", s) for i, s in enumerate(gpr_seqrs)]
        csr_seqs = [RecoveryInterfaceSequence(f"csr_seq{i}", s) for i, s in enumerate(csr_seqrs)]

        # Start CPU reactive sequences
        for s in [*gpr_seqs, *csr_seqs, *cpu_seqs]:
            cocotb.start_soon(s.start())

        for it in range(iterations):
            self.logger.debug(f"Initializing the test, iteration {it}")
            faulty_core, second_faulty_core = random.sample(range(3), 2)
            # Generate register values
            gpr_values = {}
            gpr_faulty_values = {}

            zero_values = {}
            csr_values = {}
            csr_faulty_values = {}

            # Register x0 must always contain 0
            gpr_values[0] = 0
            gpr_faulty_values[0] = 0

            for i in range(1, self.num_of_gprs):
                gpr_values[i] = random.randrange(0, 2**32)
                gpr_faulty_values[i] = gpr_values[i] ^ random.randint(0, 2**32 - 1)

            for i in range(2**12):
                zero_values[i] = 0
                csr_values[i] = random.randrange(0, 2**32)
                csr_faulty_values[i] = csr_values[i] ^ random.randint(0, 2**32 - 1)

            gpr_values_tmr = [copy.deepcopy(gpr_values) for _ in range(3)]
            gpr_values_tmr[faulty_core] = gpr_faulty_values

            csr_values_tmr = [copy.deepcopy(csr_values) for _ in range(3)]
            csr_values_tmr[faulty_core] = csr_faulty_values

            # Create sequences
            fsm_start_item = ExtFlagsItem()
            fsm_start_item.ext = MuBiTrue
            fsm_start_item.faulty_core[faulty_core] = MuBiTrue
            fsm_start_item.drive_ext = True
            fsm_start_seq = TransactionSequence("fsm_start_seq", [fsm_start_item], flag_seqr)

            # Randomize error injection type (CSR or GPR bus) and index
            err_inj_type = random.choice(["csr", "gpr"])
            if err_inj_type == "csr":
                err_idx = random.sample(CSRs, 1)[0]
                csr_values_tmr[second_faulty_core][err_idx] = csr_values[err_idx] ^ random.randint(
                    1, 2**32 - 1
                )
            elif err_inj_type == "gpr":
                err_idx = random.randint(1, self.num_of_gprs - 1)
                gpr_values_tmr[second_faulty_core][err_idx] = gpr_values[err_idx] ^ random.randint(
                    1, 2**32 - 1
                )
            self.logger.debug(
                f"Error will be injected on {err_inj_type.upper()} bus at index {err_idx}, faulty cores: {faulty_core}, {second_faulty_core}"
            )

            for i, s in enumerate(gpr_seqs):
                s.update_reg_map(gpr_values_tmr[i])
            for i, s in enumerate(csr_seqs):
                s.update_reg_map(csr_values_tmr[i])

            self.logger.debug("Starting the sequences")

            # Initiate the FSM
            cocotb.start_soon(fsm_start_seq.start())

            # Disable the FSM
            await wait_for_fatal_err()

            # Reset
            await self.reset()
