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
from cocotb.triggers import ClockCycles
from cocotbext.axi import AxiBurstType
from pyuvm import ConfigDB, test, uvm_sequence
from testbench import (  # BaseScoreboard,
    BaseTest,
)

from common import (
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


# =============================================================================


@test()
class TestCounting(BaseTest):

    AXI_WIDTH = 64

    def __init__(self, name, parent):
        super().__init__(name, parent)  # , FaultScoreboard)

    async def run(self):
        iterations = ConfigDB().get(None, "", "TEST_ITERATIONS")

        for it in range(iterations):

            # Generate random items
            items = []
            for i in range(20):
                item = AxiTransaction()
                item.is_blocking = False
                item.type = random.choice(list(AxiTransactionType))
                item.address = random.randrange(1 << 32)
                item.id = random.randrange(1 << 8)

                if item.type == AxiTransactionType.WRITE:
                    n_bytes = random.randrange(1, self.AXI_WIDTH * 4)
                    item.data = bytearray([random.randrange(256) for j in range(n_bytes)])

                elif item.type == AxiTransactionType.READ:
                    item.length = random.randrange(1, 4)

                else:
                    assert False, item.type

                items.append(item)

            # Get sequencer
            sequencer = ConfigDB().get(None, "", "AXI_AGENT").sequencer
            # Create sequence
            sequence = TransactionSequence("seq", items, sequencer)

            # Start
            await cocotb.start_soon(sequence.start())

            # Wait for all transactions to complete
            driver = ConfigDB().get(None, "", "AXI_AGENT").driver
            await driver.axi_master.wait()

            # Check if all counters are at 0 and that the module does not report
            # pending state
            await ClockCycles(cocotb.top.clk_i, 2)
            assert cocotb.top.u_axi_counter.aw_count.value == 0
            assert cocotb.top.u_axi_counter.w_count.value == 0
            assert cocotb.top.u_axi_counter.ar_count.value == 0
            assert cocotb.top.u_axi_counter.pending_o == MuBiFalse

            # Reset
            await self.reset()
