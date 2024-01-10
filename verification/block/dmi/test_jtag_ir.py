# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

import pyuvm
from jtag_pkg import JTAGInstructions
from jtag_seq import *
from testbench import BaseTest


@pyuvm.test()
class TestJTAGSetIR(BaseTest):
    def end_of_elaboration_phase(self):
        self.seqr = ConfigDB().get(None, "", "JTAG_SEQR")
        self.set_ir_seq = SetIRSequence("set_ir_seq", JTAGInstructions.DEVICE_ID_SEL.integer)

    async def run(self):
        await self.set_ir_seq.start(self.seqr)


@pyuvm.test()
class TestJTAGReadIDCODE(BaseTest):
    def end_of_elaboration_phase(self):
        self.seqr = ConfigDB().get(None, "", "JTAG_SEQR")
        self.read_idcode_seq = CaptureDRSequence("read_idcode_seq")

    async def run(self):
        await self.read_idcode_seq.start(self.seqr)


@pyuvm.test()
class TestJTAGSetIRReadDR(BaseTest):
    def end_of_elaboration_phase(self):
        self.seqr = ConfigDB().get(None, "", "JTAG_SEQR")
        self.set_ir_seq = SetIRSequence("set_ir_seq", JTAGInstructions.DEVICE_ID_SEL.integer)
        self.read_idcode_seq = CaptureDRSequence("read_idcode_seq")

    async def run(self):
        await self.set_ir_seq.start(self.seqr)
        await self.read_idcode_seq.start(self.seqr)
