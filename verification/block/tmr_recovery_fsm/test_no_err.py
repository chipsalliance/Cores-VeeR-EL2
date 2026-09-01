# Copyright (c) 2026 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0
import random
from copy import deepcopy

import cocotb
from cocotb.triggers import ClockCycles, Combine, First, Timer
from common_seq import (
    CPUReactiveCtrlSequence,
    ExternalFlagSequence,
    RecoveryInterfaceSequence,
)
from pyuvm import ConfigDB, test, uvm_sequence
from testbench import (
    BaseScoreboard,
    BaseTest,
    CPUCtrlStatusItem,
    MuBiFalse,
    MuBiTrue,
    RegBusItem,
)

# =============================================================================


class NoErrsScoreboard(BaseScoreboard):

    def check_phase(self):
        self.passed = True

        def majority_vote(val1, val2, val3):
            """
            Vote for the correct value based on 3 inputs. If not possible to pick the winner, return None.
            """
            if val1 == val2:
                return val1
            elif val2 == val3:
                return val2
            elif val1 == val3:
                return val3
            else:
                return None

        def check_if_transfers(if_name):
            assert if_name in ["gpr", "csr"]

            recovery_ports = getattr(self, f"recovery_{if_name}_ports")
            reg_reads = [{}, {}, {}]
            while (
                recovery_ports[0].can_get()
                and recovery_ports[1].can_get()
                and recovery_ports[2].can_get()
            ):
                tr = [None for _ in range(3)]

                # Collect simultaneous transactions
                for i in range(3):
                    _, tr[i] = recovery_ports[i].try_get()
                    if not isinstance(tr[i], RegBusItem):
                        self.passed = False
                        continue

                    read_reg_value = reg_reads[i].get(int(tr[i].rdaddr))
                    if tr[i].write and (read_reg_value is None):
                        self.passed = False
                        self.logger.error(
                            f"[{tr[i].timestamp}] {if_name.upper()} written without prior read at this address"
                        )
                        continue

                    if not tr[i].write:
                        # Save read value for later comparison
                        reg_reads[i][int(tr[i].rdaddr)] = int(tr[i].rddata)
                        self.logger.debug(
                            f"[{tr[i].timestamp}] {if_name.upper()} read value {hex(tr[i].rddata)} at {hex(tr[i].rdaddr)}"
                        )

                if not (tr[0].timestamp == tr[1].timestamp == tr[2].timestamp):
                    self.passed = False
                    self.logger.error(
                        f"Received {if_name.upper()} transactions do not match in time"
                    )
                    break

                rddata = majority_vote(
                    reg_reads[0][int(tr[0].rdaddr)],
                    reg_reads[1][int(tr[1].rdaddr)],
                    reg_reads[2][int(tr[2].rdaddr)],
                )
                if rddata is None:
                    self.logger.error("Voter failed")
                    continue

                for i in range(3):
                    if tr[i].write:
                        if rddata != int(tr[i].wrdata):
                            self.passed = False
                            self.logger.error(
                                f"[{tr[i].timestamp}] {if_name.upper()} written different value than earlier read at address {hex(tr[i].wraddr)}, expected: {hex(rddata)}, got: {hex(tr[i].wrdata)}"
                            )
                            continue
                        if int(tr[i].rddata) not in [0, int(tr[i].wrdata)]:
                            self.passed = False
                            self.logger.error(
                                f"[{tr[i].timestamp}] During write, read data should be either 0 or equal to write data"
                            )
                            continue
                        if int(tr[i].wraddr) != int(tr[i].rdaddr):
                            self.passed = False
                            self.logger.error(
                                f"[{tr[i].timestamp}] Simultaneous read and write on {if_name.upper()} interface is only allowed at the same address"
                            )
                            continue

        check_if_transfers("gpr")
        check_if_transfers("csr")


# =============================================================================


# =============================================================================


@test()
class TestNoErrs(BaseTest):
    def __init__(self, name, parent):
        super().__init__(name, parent, NoErrsScoreboard)

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
