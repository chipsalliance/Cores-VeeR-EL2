# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

import pyuvm
from testbench import BaseTest
from jtag_seq import *


@pyuvm.test()
class TestJTAGReadIDCODE(BaseTest):
    def end_of_elaboration_phase(self):
        self.seqr = ConfigDB().get(None, "", "SEQR")
        self.read_idcode_seq = CaptureDRSequence("read_idcode_seq")

    async def run(self):
        await self.read_idcode_seq.start(self.seqr)
