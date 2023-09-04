#
# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: BSD-2-Clause

import pyuvm
from pyuvm import *
from .irq_uvm import VeerEl2Env, IrqRandomSeq
from cocotb.clock import Clock

@pyuvm.test()
class BaseTest(uvm_test):
    def build_phase(self):
        self.set_default_logging_level(logging.DEBUG)
        self.env = VeerEl2Env("env", self)

    def end_of_elaboration_phase(self):
        self.test_all = IrqRandomSeq.create("test_irq")

    async def run_phase(self):
        self.raise_objection()
        clock = Clock(cocotb.top.clk, 10, units="ns")
        cocotb.start_soon(clock.start(start_high=False))
        await self.test_all.start()
        self.drop_objection()
