# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

import pyuvm
from testbench import BaseTest
from jtag_seq import *
from common import JTAG_CMDS

@pyuvm.test()
class TestJTAGSetIR(BaseTest):
    def end_of_elaboration_phase(self):
        self.seqr = ConfigDB().get(None, "", "SEQR")
        self.set_ir_seq = SetIRSequence("set_ir_seq", JTAG_CMDS.IDCODE)

    async def run(self):
        await self.set_ir_seq.start(self.seqr)
