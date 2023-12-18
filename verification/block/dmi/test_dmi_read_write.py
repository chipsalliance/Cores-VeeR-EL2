# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0

import pyuvm
from dmi_seq import *
from jtag_seq import *
from testbench import BaseTest


@pyuvm.test()
class TestDMIReadRegs(BaseTest):
    def end_of_elaboration_phase(self):
        self.seqr = ConfigDB().get(None, "", "JTAG_SEQR")
        self.set_ir_dren0_seq = SetIRSequence("set_ir_seq", 0b10000)
        self.set_ir_dren1_seq = SetIRSequence("set_ir_seq", 0b10001)
        self.read_dmcontrol_seq = AccessDMIRegSequence("read_dmcontrol_seq", addr=0x10)
        self.read_dmstatus_seq = AccessDMIRegSequence("read_dmstatus_seq", addr=0x11)

    async def run(self):
        await self.set_ir_dren0_seq.start(self.seqr)
        await self.read_dmcontrol_seq.start(self.seqr)
        await self.set_ir_dren1_seq.start(self.seqr)
        await self.read_dmstatus_seq.start(self.seqr)


@pyuvm.test()
class TestDMIWriteRegs(BaseTest):
    def end_of_elaboration_phase(self):
        self.seqr = ConfigDB().get(None, "", "JTAG_SEQR")
        self.set_ir_dren1_seq = SetIRSequence("set_ir_seq", 0b10001)
        self.write_dmcontrol_seq = AccessDMIRegSequence(
            "write_dmcontrol_seq", addr=0x10, data=0x01234567, is_write=True
        )
        self.write_dmstatus_seq = AccessDMIRegSequence(
            "write_dmstatus_seq", addr=0x11, data=0xDEADBEEF, is_write=True
        )

    async def run(self):
        await self.set_ir_dren1_seq.start(self.seqr)
        await self.write_dmcontrol_seq.start(self.seqr)
        await self.write_dmstatus_seq.start(self.seqr)


@pyuvm.test()
class TestDMIReadWriteRegs(BaseTest):
    def end_of_elaboration_phase(self):
        self.seqr = ConfigDB().get(None, "", "JTAG_SEQR")
        self.set_ir_dren1_seq = SetIRSequence("set_ir_seq", 0b10001)
        self.write_dmcontrol_seq = AccessDMIRegSequence(
            "write_dmcontrol_seq", addr=0x10, data=0x01234567, is_write=True
        )
        self.write_dmstatus_seq = AccessDMIRegSequence(
            "write_dmstatus_seq", addr=0x11, data=0xDEADBEEF, is_write=True
        )
        self.read_dmcontrol_seq = AccessDMIRegSequence("read_dmcontrol_seq", addr=0x10)
        self.read_dmstatus_seq = AccessDMIRegSequence("read_dmstatus_seq", addr=0x11)

    async def run(self):
        await self.set_ir_dren1_seq.start(self.seqr)
        await self.write_dmcontrol_seq.start(self.seqr)
        await self.write_dmstatus_seq.start(self.seqr)
        await self.read_dmcontrol_seq.start(self.seqr)
        await self.read_dmstatus_seq.start(self.seqr)


@pyuvm.test()
class TestUncoreDMIReadWriteRegs(BaseTest):
    def end_of_elaboration_phase(self):
        self.jtag_seqr = ConfigDB().get(None, "", "JTAG_SEQR")
        self.dmi_seqr = ConfigDB().get(None, "", "DMI_SEQR")
        self.uncore_enable_seq = SetUncoreEnableSequence("uncore_enable_seq", 1)
        self.set_ir_dren1_seq = SetIRSequence("set_ir_seq", 0b10001)
        self.write_core_seq1 = AccessDMIRegSequence(
            "write_core_seq1", addr=0x11, data=0xDEADBEEF, is_write=True
        )
        self.write_uncore_seq1 = AccessDMIRegSequence(
            "write_uncore_seq1", addr=0x7F, data=0x76543210, is_write=True
        )
        self.read_core_seq1 = AccessDMIRegSequence("read_core_seq1", addr=0x11)
        self.read_uncore_seq1 = AccessDMIRegSequence("read_uncore_seq1", addr=0x7F)
        self.write_core_seq2 = AccessDMIRegSequence(
            "write_core_seq2", addr=0x4F, data=0xBEEFDEAD, is_write=True
        )
        self.write_uncore_seq2 = AccessDMIRegSequence(
            "write_uncore_seq2", addr=0x50, data=0xFEEDABED, is_write=True
        )
        self.read_core_seq2 = AccessDMIRegSequence("read_core_seq2", addr=0x4F)
        self.read_uncore_seq2 = AccessDMIRegSequence("read_uncore_seq2", addr=0x50)

    async def run(self):
        await self.uncore_enable_seq.start(self.dmi_seqr)
        await self.set_ir_dren1_seq.start(self.jtag_seqr)
        await self.write_core_seq1.start(self.jtag_seqr)
        await self.write_uncore_seq1.start(self.jtag_seqr)
        await self.read_core_seq1.start(self.jtag_seqr)
        await self.read_uncore_seq1.start(self.jtag_seqr)
        await self.write_core_seq2.start(self.jtag_seqr)
        await self.write_uncore_seq2.start(self.jtag_seqr)
        await self.read_core_seq2.start(self.jtag_seqr)
        await self.read_uncore_seq2.start(self.jtag_seqr)
