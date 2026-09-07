# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

import pyuvm
from coordinator_seq import TestFastWriteSeq, TestWriteChannelSeq
from testbench import BaseTest


@pyuvm.test()
class TestAXIWriteChannel(BaseTest):
    def end_of_elaboration_phase(self):
        self.seq = TestWriteChannelSeq.create("stimulus")

    async def run(self):
        self.raise_objection()
        await self.seq.start()
        self.drop_objection()


@pyuvm.test()
class TestAXIFastWrite(BaseTest):
    """Verify two back-to-back writes through the AXI and AHB interfaces."""

    def end_of_elaboration_phase(self):
        self.seq = TestFastWriteSeq.create("stimulus")

    async def run(self):
        self.raise_objection()
        await self.seq.start()
        self.drop_objection()
