#
# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: BSD-2-Clause

import random
from pyuvm import *
from .irq_utils import IrqBfm


class IrqRandomSeq(uvm_sequence):
    async def body(self):
        seqr = ConfigDB().get(None, "", "SEQR")
        random = vIrqSeq("random")
        await random.start(seqr)


class vIrqSeq(uvm_sequence):
    async def body(self):
        for i in range(10):
            int_tr = IrqTriggerSeqItem("irq_trigger", 0, 0, 0, 0)
            await self.start_item(int_tr)
            int_tr.randomize()
            await self.finish_item(int_tr)


class IrqTriggerSeqItem(uvm_sequence_item):
    def __init__(self, name, nmi, soft, timer, ext):
        super().__init__(name)
        self.nmi = nmi
        self.soft = soft
        self.timer = timer
        self.ext = ext

    def __eq__(self, other):
        same = self.nmi == other.nmi and self.soft == other.soft and self.timer == other.timer and self.ext == other.ext
        return same

    def __str__(self):
        return f"{self.get_name()} : NMI {self.nmi}, SOFT: {self.soft}, TIMER: {self.timer}, EXT: {self.ext:0x}"

    def randomize(self):
        self.nmi = random.randrange(2)
        self.soft = random.randrange(2)
        self.timer = random.randrange(2)
        self.ext = random.randrange(2)


class IrqMonitor(uvm_monitor):
    def __init__(self, name, parent, method_name):
        super().__init__(name, parent)
        self.method_name = method_name

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)
        self.bfm = IrqBfm()
        self.get_method = getattr(self.bfm, self.method_name)

    async def run_phase(self):
        while True:
            datum = await self.get_method()
            self.logger.debug(f"MONITORED {datum}")
            self.ap.write(datum)


class Scoreboard(uvm_component):
    def build_phase(self):
        self.interrupt_source_fifo = uvm_tlm_analysis_fifo("interrupt_source_fifo",self)
        self.interrupt_source_get_port = uvm_get_port("interrupt_source_get_port",self)
        self.interrupt_source_export = self.interrupt_source_fifo.analysis_export

        self.trace_interrupt_fifo = uvm_tlm_analysis_fifo("trace_interrupt_fifo",self)
        self.trace_interrupt_get_port = uvm_get_port("trace_interrupt_get_port",self)
        self.trace_interrupt_export = self.trace_interrupt_fifo.analysis_export

    def connect_phase(self):
        self.interrupt_source_get_port.connect(self.interrupt_source_fifo.get_export)
        self.trace_interrupt_get_port.connect(self.trace_interrupt_fifo.get_export)

    def check_phase(self):
        passed = True
        try:
            self.errors = ConfigDB().get(self, "", "CREATE_ERRORS")
        except UVMConfigItemNotFound:
            self.errors = False
        assert passed


class IrqDriver(uvm_driver):
    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    def start_of_simulation_phase(self):
        self.bfm = IrqBfm()

    async def initialize_tb(self):
        await self.bfm.reset()
        self.bfm.start_bfm()

    async def run_phase(self):
        await self.initialize_tb()
        while True:
            ints = await self.seq_item_port.get_next_item()
            await self.bfm.send_interrupt_source(ints)
            result = await self.bfm.get_trace_interrupt()
            self.ap.write(result)
            self.seq_item_port.item_done()

class IrqAgent(uvm_agent):
    def build_phase(self):
        self.seqr = uvm_sequencer("seqr", self)
        ConfigDB().set(None, "*", "SEQR", self.seqr)
        self.monitor = IrqMonitor("int_monitor", self, "get_interrupt_source")
        self.driver = IrqDriver("int_driver", self)

    def connect_phase(self):
        # Driver takes sequence items from sequencer
        self.driver.seq_item_port.connect(self.seqr.seq_item_export)

class VeerEl2Env(uvm_env):
    def build_phase(self):
        self.scoreboard = Scoreboard("scoreboard", self)
        self.agent = IrqAgent("agent",self)

    def connect_phase(self):
        # Monitor pushes observed data to the scoreboard
        self.agent.monitor.ap.connect(self.scoreboard.interrupt_source_export)

        # Driver
        self.agent.driver.ap.connect(self.scoreboard.trace_interrupt_export)
