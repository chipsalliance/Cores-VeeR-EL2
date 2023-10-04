# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

import pyuvm
from coordinator_seq import TestWriteChannelSeq
from testbench import BaseTest

# FIXME       : This test is expected to fail.
# See description in `test_axi.py`


@pyuvm.test(expect_error=TimeoutError)
class TestAXIWriteChannel(BaseTest):
    def end_of_elaboration_phase(self):
        self.seq = TestWriteChannelSeq.create("stimulus")

    async def run(self):
        self.raise_objection()
        await self.seq.start()
        self.drop_objection()
