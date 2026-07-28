# Copyright (c) 2026 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0
import random
from copy import deepcopy

import cocotb
from axi_agent import (
    AxiReadTransaction,
    AxiTransaction,
    AxiTransactionType,
    AxiWriteTransaction,
)
from cocotb.triggers import ClockCycles, Combine, Timer
from cocotbext.axi import AxiBurstType
from pyuvm import ConfigDB, test, uvm_sequence
from testbench import (
    BaseScoreboard,
    BaseTest,
    MuBiFalse,
    MuBiTrue,
)

# =============================================================================


class FaultScoreboard(BaseScoreboard):

    def check_phase(self):

        events = []

        # Collect all AXI items
        self.passed = True
        while self.m_axi_tr_port.can_get():

            if not self.s_axi_a_tr_port.can_get():
                self.logger.error("No more transactions observed on AXI A port")
                self.passed = False
                break

            if not self.s_axi_b_tr_port.can_get():
                self.logger.error("No more transactions observed on AXI B port")
                self.passed = False
                break

            if not self.s_axi_c_tr_port.can_get():
                self.logger.error("No more transactions observed on AXI C port")
                self.passed = False
                break

            _, tr_m = self.m_axi_tr_port.try_get()
            _, tr_a = self.s_axi_a_tr_port.try_get()
            _, tr_b = self.s_axi_b_tr_port.try_get()
            _, tr_c = self.s_axi_c_tr_port.try_get()

            if isinstance(tr_m, AxiWriteTransaction):
                timestamp = tr_m.b.timestamp
            elif isinstance(tr_m, AxiReadTransaction):
                timestamp = tr_m.r[-1].timestamp
            else:
                assert False, type(tr_m)

            event = (timestamp, {"m": tr_m, "a": tr_a, "b": tr_b, "c": tr_c})
            events.append(event)

        # Collect all fault items
        while self.fault_port.can_get():
            _, fault = self.fault_port.try_get()

            event = (fault.timestamp, {"fault": fault})
            events.append(event)

        # Sort by timestamps
        events.sort(key=lambda ev: ev[0])

        # Check
        fault = [False, False, False]
        for timestamp, event in events:

            # Update fault state
            if "fault" in event:
                fault = event["fault"].fault
                continue

            # Get a correct AXI transaction basing of the current indicated
            # fault state
            if fault == [False, False, False]:
                s_axi = event["a"]
            elif fault == [True, False, False]:
                s_axi = event["b"]
            elif fault == [False, True, False]:
                s_axi = event["c"]
            elif fault == [False, False, True]:
                s_axi = event["a"]
            else:
                # TODO: Handle the case, currently should not happen in this
                # test
                assert False, fault

            # Compare
            if event["m"] != s_axi:
                self.logger.error(f"AXI transaction mismatch at {timestamp}ps")
                self.logger.error(f" Fault: {str(fault)}")

                for ev in ["a", "b", "c", "m"]:
                    self.logger.error(f" AXI {ev.upper()}:")
                    for line in str(event[ev]).splitlines():
                        self.logger.error("  " + line)

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
class TestFaults(BaseTest):
    def __init__(self, name, parent):
        super().__init__(name, parent, FaultScoreboard)

    async def run(self):
        period = ConfigDB().get(None, "", "TEST_CLK_PERIOD")
        iterations = ConfigDB().get(None, "", "TEST_ITERATIONS")

        for it in range(iterations):

            # Generate random items
            base_items = []
            for i in range(20):
                item = AxiTransaction()
                item.type = random.choice(list(AxiTransactionType))
                item.address = random.randrange(1 << 32)
                item.id = random.randrange(1 << 4)

                if item.type == AxiTransactionType.WRITE:
                    item.data = bytearray([random.randrange(256) for j in range(8)])

                elif item.type == AxiTransactionType.READ:
                    item.length = 1

                else:
                    assert False, item.type

                base_items.append(item)

            # Replicate and inject discrepancies
            fault = random.randrange(3)
            items = []

            for i in range(3):
                core_items = deepcopy(base_items)
                items.append(core_items)

                if i == fault:
                    which = random.randrange(len(core_items))

                    # opts = ["addr", "burst"]
                    opts = ["addr"]
                    if core_items[which].type == AxiTransactionType.WRITE:
                        opts.append("data")

                    what = random.choice(opts)

                    if what == "addr":
                        core_items[which].address ^= 1 << random.randrange(32)

                    elif what == "data":
                        j = random.randrange(len(core_items[which].data))
                        core_items[which].data[j] ^= 1 << random.randrange(8)

                    # elif what == "id":
                    #    core_items[which].id ^= 1 << random.randrange(4)

                    elif what == "burst":
                        core_items[which].burst = random.choice(list(AxiBurstType))

                    else:
                        assert False, what

            # Get sequencers
            sequencers = [
                ConfigDB().get(None, "", "AXI_AGENT_" + i).sequencer for i in ["A", "B", "C"]
            ]

            # Create sequences
            sequences = [
                TransactionSequence("seq_" + i, it, s)
                for i, it, s in zip(["a", "b", "c"], items, sequencers)
            ]

            # Start tasks
            tasks = [cocotb.start_soon(s.start()) for s in sequences]
            timer = Timer(20 * period)

            await Combine(*tasks, timer)

            # Reset
            await self.reset()
