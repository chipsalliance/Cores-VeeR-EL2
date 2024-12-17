# Copyright (c) 2024 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

import pyuvm
from cocotb.queue import QueueFull
from coordinator_seq import TestReadChannelMultipleSeq
from testbench import BaseTest


@pyuvm.test(expect_error=TimeoutError)
class TestAXIReadChannelMultiple(BaseTest):
    def end_of_elaboration_phase(self):
        self.seq = TestReadChannelMultipleSeq.create("stimulus")

    async def run(self):
        self.raise_objection()
        await self.seq.start()
        self.drop_objection()
