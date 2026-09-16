# Copyright (c) 2026 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0
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
from testbench import (
    BaseTest,
    ExtFlagsItem,
    MuBiFalse,
    MuBiTrue,
)

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


@test(expect_fail=True)
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
            self.logger.info(f"Initializing the test, iteration {it}")
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


@test()
class TestFatalError(BaseTest):
    # There are always 32 GPRs, specified by ISA
    num_of_gprs = 32

    def __init__(self, name, parent):
        super().__init__(name, parent, RegBusScoreboard)
        self.logger.setLevel(logging.INFO)

    async def run(self):

        async def wait_for_fatal_err():
            while cocotb.top.fatal_err.value != MuBiTrue:
                await RisingEdge(cocotb.top.clk)
                await ReadWrite()
            self.logger.info("Success! Fatal error from FSM detected")

        def terminate_tasks(tasks):
            self.logger.info("Terminating tasks")
            for t in tasks:
                t.kill()

        async def finish_test(tasks):
            await wait_for_fatal_err()
            delay = random.randint(10, 1000)
            await Timer(period * delay, "ns")
            terminate_tasks(tasks)

        period = ConfigDB().get(None, "", "TEST_CLK_PERIOD")
        user_mode = ConfigDB().get(None, "", "USER_MODE")
        num_of_csrs = 146 if not user_mode else 163
        iterations = ConfigDB().get(None, "", "TEST_ITERATIONS")

        flag_seqr = ConfigDB().get(None, "", "EXT_FLAG_SEQ")
        cpu_seqrs = [ConfigDB().get(None, "", f"CPU_CTRL{i}_CPU_SEQ") for i in range(3)]
        gpr_seqrs = [ConfigDB().get(None, "", f"GPR{i}_SEQ") for i in range(3)]
        csr_seqrs = [ConfigDB().get(None, "", f"CSR{i}_SEQ") for i in range(3)]

        for it in range(iterations):
            self.logger.info(f"Initializing the test, iteration {it}")
            # Generate register values
            gpr_values = {}
            gpr_faulty_values = {}

            zero_values = {}
            csr_values = {}

            # Register x0 must always contain 0
            gpr_values[0] = 0
            gpr_faulty_values[0] = 0

            for i in range(1, self.num_of_gprs):
                gpr_values[i] = random.randrange(0, 2**32)

            for i in range(2**12):
                zero_values[i] = 0
                csr_values[i] = random.randrange(0, 2**32)

            gpr_values_tmr = [gpr_values for _ in range(3)]
            csr_values_tmr = [csr_values for _ in range(3)]

            # Create sequences
            fsm_start_item = ExtFlagsItem()
            fsm_start_item.ext = MuBiTrue
            fsm_start_item.drive_ext = True
            fsm_start_seq = TransactionSequence("fsm_start_seq", [fsm_start_item], flag_seqr)

            cpu_seqs = [
                CPUReactiveCtrlSequence(f"cpu_seq{i}", s) for i, s in zip(range(3), cpu_seqrs)
            ]

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
            fsm_stop_item = ExtFlagsItem()
            fsm_stop_item.ext = MuBiFalse
            fsm_stop_item.drive_ext = True
            fsm_stop_seq = TransactionSequence("fsm_stop_seq", [fsm_stop_item], flag_seqr)

            # Randomize error injection type (CSR or GPR bus) and index
            err_inj_type = random.choice(["csr", "gpr"])
            if err_inj_type == "csr":
                err_idx = random.randint(0, (num_of_csrs * 2) - 1)
            elif err_inj_type == "gpr":
                err_idx = random.randint(0, (self.num_of_gprs * 2) - 1)
            self.logger.info(
                f"Error will be injected on {err_inj_type.upper()} bus at index {err_idx}"
            )

            # Enable error injection on the randomized bus
            # If randomized index is lower or equal to the number of available registers,
            # inject error in write (post-reset) phase, otherwise, inject error in read phase
            if err_inj_type == "csr":
                for i in range(3):
                    if err_idx >= num_of_csrs:
                        post_reset_csr_seqs[i].err_idx = err_idx - num_of_csrs
                        post_reset_csr_seqs[i].err_inj_en = True
                    else:
                        csr_seqs[i].err_idx = err_idx
                        csr_seqs[i].err_inj_en = True
            elif err_inj_type == "gpr":
                for i in range(3):
                    if err_idx >= self.num_of_gprs:
                        post_reset_gpr_seqs[i].err_idx = err_idx - self.num_of_gprs
                        post_reset_gpr_seqs[i].err_inj_en = True
                    else:
                        gpr_seqs[i].err_idx = err_idx
                        gpr_seqs[i].err_inj_en = True

            # In normal flow, sequences should finish when the enable signal gets deasserted,
            # otherwise, they will be manually terminated later
            for s in [*gpr_seqs, *csr_seqs]:
                s.finish_no_en = True

            self.logger.info("Starting the sequences")

            # Start CPU reactive sequences
            for s in cpu_seqs:
                cocotb.start_soon(s.start())

            # Initiate the FSM
            cocotb.start_soon(fsm_start_seq.start())

            # Enable register bus sequences
            gpr_tasks = [cocotb.start_soon(s.start()) for s in gpr_seqs]
            csr_tasks = [cocotb.start_soon(s.start()) for s in csr_seqs]

            # If error injected on read phase, do not proceed to write phase and finish the test on fatal error
            test_done = False
            if err_inj_type == "csr" and err_idx < num_of_csrs:
                await finish_test([*gpr_tasks, *csr_tasks])
                test_done = True
            elif err_inj_type == "gpr" and err_idx < self.num_of_gprs:
                await finish_test([*gpr_tasks, *csr_tasks])
                test_done = True
            else:
                self.logger.debug(f"Waiting for {err_inj_type.upper()} sequences to finish")
                await Combine(*gpr_tasks, *csr_tasks)

            if not test_done:
                gpr_tasks = [cocotb.start_soon(s.start()) for s in post_reset_gpr_seqs]
                csr_tasks = [cocotb.start_soon(s.start()) for s in post_reset_csr_seqs]
                await finish_test([*gpr_tasks, *csr_tasks])

            # Disable the FSM
            await cocotb.start_soon(fsm_stop_seq.start())

            # Reset
            await self.reset()
