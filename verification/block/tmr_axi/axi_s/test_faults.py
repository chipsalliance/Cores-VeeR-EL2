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
from cocotb.handle import Force, ModifiableObject, Release
from cocotb.triggers import Combine, RisingEdge, Timer
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
        period = ConfigDB().get(None, "", "TEST_CLK_PERIOD")  # [ns]

        # Collect all AXI items
        self.passed = True
        while self.s_axi_tr_port.can_get():

            if not self.m_axi_a_tr_port.can_get():
                self.logger.error("No more transactions observed on AXI A port")
                self.passed = False
                break

            if not self.m_axi_b_tr_port.can_get():
                self.logger.error("No more transactions observed on AXI B port")
                self.passed = False
                break

            if not self.m_axi_c_tr_port.can_get():
                self.logger.error("No more transactions observed on AXI C port")
                self.passed = False
                break

            _, tr_s = self.s_axi_tr_port.try_get()
            _, tr_a = self.m_axi_a_tr_port.try_get()
            _, tr_b = self.m_axi_b_tr_port.try_get()
            _, tr_c = self.m_axi_c_tr_port.try_get()

            if isinstance(tr_s, AxiWriteTransaction):
                timestamp = tr_s.b.timestamp
            elif isinstance(tr_s, AxiReadTransaction):
                timestamp = tr_s.r[-1].timestamp
            else:
                assert False, type(tr_s)

            # Faults are reported with 1-2 cycle delay. Move AXI transaction
            # to the future by 2x clock period
            timestamp += 2000 * period  # [ps]

            event = (timestamp, {"s": tr_s, "a": tr_a, "b": tr_b, "c": tr_c})
            events.append(event)

        # No AXI events, fail
        if not events:
            self.passed = False
            return

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
                m_axi = event["a"]
            elif fault == [True, False, False]:
                m_axi = event["b"]
            elif fault == [False, True, False]:
                m_axi = event["c"]
            elif fault == [False, False, True]:
                m_axi = event["a"]
            else:
                # TODO: Handle the case, currently should not happen in this
                # test
                assert False, fault

            # Compare
            if event["s"] != m_axi:
                self.logger.error(f"AXI transaction mismatch at {timestamp}ps")
                self.logger.error(f" Fault: {str(fault)}")

                for ev in ["a", "b", "c", "s"]:
                    self.logger.error(f" AXI {ev.upper()}:")
                    for line in str(event[ev]).splitlines():
                        self.logger.error("  " + line)

                self.passed = False


# =============================================================================


class TransactionSequenceWithFaultInjection(uvm_sequence):
    """
    This sequence stores pairs of transaction items and signal upsets. Prior
    to executing a transaction item, upsets are imposed on the communication bus
    and cleared once the transaction is complete.
    """

    class Item:
        def __init__(self, tr=None, upsets=None):
            self.tr = tr
            self.upsets = [] if upsets is None else upsets

    def __init__(self, name, items, seqr):
        self.items = items
        self.seqr = seqr
        self.logger = seqr.logger
        super().__init__(name)

    async def body(self):
        for item in self.items:

            # Set bus upsets
            for bus, sig, val in item.upsets:
                bus.upsets[sig] = val

            await self.seqr.start_item(item.tr)
            await self.seqr.finish_item(item.tr)

            # Clear bus upsets
            buses = set([bus for bus, sig, val in item.upsets])
            for bus in buses:
                bus.upsets = dict()
                bus.upset()


# =============================================================================


@test()
class TestFaults(BaseTest):
    def __init__(self, name, parent):
        super().__init__(name, parent, FaultScoreboard)

    async def run(self):
        iterations = ConfigDB().get(None, "", "TEST_ITERATIONS")

        for it in range(iterations):

            # Generate items
            items = []
            for i in range(20):

                # Transaction
                tr = AxiTransaction()
                tr.type = random.choice(list(AxiTransactionType))
                tr.address = random.randrange(1 << 32)
                tr.id = random.randrange(1 << 4)

                if tr.type == AxiTransactionType.WRITE:
                    tr.data = bytearray([random.randrange(256) for j in range(8)])

                elif tr.type == AxiTransactionType.READ:
                    tr.length = 1

                else:
                    assert False, tr.type

                item = TransactionSequenceWithFaultInjection.Item(tr)
                items.append(item)

            # Upset
            if random.random() < 0.50:
                which = random.randrange(len(items))
                bus_name = "m_axi_" + random.choice(["a", "b", "c"])
                bus_obj = getattr(self.env, bus_name)

                # Get bus bundle basing on transaction direction
                if tr.type == AxiTransactionType.WRITE:
                    bus_obj = bus_obj.write.b
                elif tr.type == AxiTransactionType.READ:
                    bus_obj = bus_obj.read.r
                else:
                    assert False, tr.type

                # Discover bus signals
                # Don't upset valid/ready not to break handshake
                # Don't upset rid/bid not to confuse bus monitor
                # Don't upset rlast
                signals = [
                    s
                    for s in dir(bus_obj)
                    if isinstance(getattr(bus_obj, s), ModifiableObject)
                    and "valid" not in s
                    and "ready" not in s
                    and s != "rlast"
                    and "id" not in s
                ]

                # Upset
                signal = random.choice(signals)
                items[which].upsets.append(
                    (bus_obj, signal, random.randrange(1 << len(getattr(bus_obj, signal))))
                )

            # Get sequencer
            sequencer = ConfigDB().get(None, "", "M_AXI_AGENT").sequencer
            # Create sequence
            sequence = TransactionSequenceWithFaultInjection("seq", items, sequencer)

            # Run the sequence
            await sequence.start()

            # Reset
            await self.reset()
