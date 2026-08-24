# Copyright (c) 2026 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0
import random
from collections import defaultdict
from copy import deepcopy

import cocotb
from cocotb.triggers import ClockCycles, Combine, Timer
from pyuvm import ConfigDB, test, uvm_sequence
from testbench import (
    BaseScoreboard,
    BaseTest,
)

from common import (
    BusItem,
    MuBiFalse,
    MuBiTrue,
)

# =============================================================================


class BusSequence(uvm_sequence):
    """
    A generic bus sequence which blindly drives bus states
    """

    def __init__(self, name, seqr):
        self.items = []
        self.seqr = seqr
        super().__init__(name)

    async def body(self):
        for item in self.items:
            await self.seqr.start_item(item)
            await self.seqr.finish_item(item)


# =============================================================================


class FaultScoreboard(BaseScoreboard):
    """
    The scoreboard collects bus' state change items, recovers bus state,
    predicts output state via majority voting and fault state, compares with
    observation.
    """

    def check_phase(self):
        events = []
        period = 1000 * ConfigDB().get(None, "", "TEST_CLK_PERIOD")  # [ps]

        # Collect all veer bus items
        while self.veer_bus_port.can_get():
            _, item = self.veer_bus_port.try_get()

            event = (item.timestamp + period, {"veer": item})
            events.append(event)

        # Collect all out bus items
        while self.out_bus_port.can_get():
            _, item = self.out_bus_port.try_get()

            event = (item.timestamp + period, {"out": item})
            events.append(event)

        # Collect all fault items
        while self.fault_port.can_get():
            _, fault = self.fault_port.try_get()

            event = (fault.timestamp, {"fault": fault})
            events.append(event)

        # Unique sorted timestamps
        timestamps = set([ev[0] for ev in events])
        timestamps = sorted(list(timestamps))

        # Group by timestamps
        ts_events = defaultdict(lambda: list())
        for ev in events:
            ts_events[ev[0]].append(ev[1])

        # Check
        fault_state = [False, False, False]
        veer_bus_state = None
        out_bus_state = None

        self.passed = True
        for timestamp in timestamps:

            # Update state
            for event in ts_events[timestamp]:
                if "fault" in event:
                    fault_state = event["fault"].fault
                if "veer" in event:
                    veer_bus_state = event["veer"].signals
                if "out" in event:
                    out_bus_state = event["out"].signals

            if veer_bus_state is None or out_bus_state is None:
                continue

            # Predict
            if fault_state == [False, False, False]:
                index = 0  # Arbitrary
            elif fault_state == [True, False, False]:
                index = 1
            elif fault_state == [False, True, False]:
                index = 2
            elif fault_state == [False, False, True]:
                index = 0
            else:
                # TODO: Handle the case, currently should not happen in this
                # test
                assert False, fault_state

            pred_bus_state = {k.replace("_veer", ""): v[index] for k, v in veer_bus_state.items()}

            # Compare
            if pred_bus_state != out_bus_state:
                self.passed = False

                self.logger.error(f"Bus state mismatch at {timestamp}ps")
                self.logger.error(f" Fault: {str(fault_state)}")

                def sig2str(d):
                    keys = sorted(list(d.keys()))
                    return ", ".join([f"{k}={d[k]}" for k in keys])

                self.logger.error(f" Out  : {sig2str(out_bus_state)}")
                self.logger.error(f" Pred.: {sig2str(pred_bus_state)}")


# =============================================================================


@test()
class TestFaults(BaseTest):
    """
    Drives randomized state on the input buses occassionally upsetting one
    signal.
    """

    def __init__(self, name, parent):
        super().__init__(name, parent, FaultScoreboard)

    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = BusSequence("seq", self.env.veer_bus_seqr)

    async def run(self):
        iterations = ConfigDB().get(None, "", "TEST_ITERATIONS")

        signals = {
            "dmi_reg_rdata_veer": None,
        }

        # Get signal lengths
        for name in signals:
            sig = getattr(cocotb.top, name + "[0]")
            signals[name] = len(sig)

        # Run test iterations
        for it in range(iterations):

            # Generate random items
            items = []
            for i in range(20):
                item = BusItem()

                for name in signals:
                    value = random.randrange(1 << signals[name])
                    for j in range(3):
                        item.signals[name + f"[{j}]"] = value

                items.append(item)

            # Inject discrepancies
            fault = random.randrange(3)
            what = random.choice(list(signals.keys()))

            # Don't upset the last transaction. The upset would last during
            # reset which clears the fault state making the scoreboard report
            # error.
            which = random.randrange(len(items) - 1)

            items[which].signals[what + f"[{fault}]"] ^= 1 << random.randrange(signals[what])

            # Run the sequence
            self.seq.items = items
            await self.seq.start()

            # Reset
            await self.reset()
