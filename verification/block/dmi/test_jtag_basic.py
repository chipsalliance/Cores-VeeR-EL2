# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

from copy import deepcopy

import cocotb
import pyuvm
from testbench import BaseTest
from jtag_agent import *
from jtag_bfm import *
from jtag_seq import *
from pyuvm import *



@pyuvm.test()
class TestJTAGBasic(BaseTest):
    def end_of_elaboration_phase(self):
        self.seqr = ConfigDB().get(None, "", "SEQR")
        self.set_ir_seq = SetIRSequence("set_ir_seq")

    async def run(self):
        self.raise_objection()
        await self.set_ir_seq.start(self.seqr)
        self.drop_objection()
