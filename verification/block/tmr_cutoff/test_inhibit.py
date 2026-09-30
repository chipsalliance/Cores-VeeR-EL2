# Copyright (c) 2026 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0
from pyuvm import ConfigDB, test, uvm_sequence
from testbench import (
    BaseTest,
    DriverItem,
)

# =============================================================================


class Sequence(uvm_sequence):
    """
    Loop over all output signals with inhibit asserted and deasserted.
    """

    def __init__(self, name, seqr):
        self.seqr = seqr
        super().__init__(name)

    async def body(self):
        env = ConfigDB().get(None, "", "env")

        for src_signals, dst_signals in env.signals:
            for inhibit in (0, 1):
                item = DriverItem()
                item.inhibit = inhibit
                item.signals = src_signals
                await self.seqr.start_item(item)
                await self.seqr.finish_item(item)


@test()
class TestInhibit(BaseTest):
    """
    Checks operation of the output inhibit signal of the TMR complex
    """

    def __init__(self, name, parent):
        super().__init__(name, parent)

    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = Sequence("seq", self.env.seqr)

    async def run(self):
        await self.seq.start()
