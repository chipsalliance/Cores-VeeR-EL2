import random
from pyuvm import *
from .uvm_common import VeerEl2Bfm


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

class IrqMonitor(uvm_monitor):
    def __init__(self, name, parent):
        super().__init__(name, parent)

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)
        self.bfm = VeerEl2Bfm()

    async def run_phase(self):
        while True:
            datum = await self.bfm.get_interrupts()
            self.logger.debug(f"MONITORED {datum}")
            self.ap.write(datum)

class IrqDriver(uvm_driver):
    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    def start_of_simulation_phase(self):
        self.bfm = VeerEl2Bfm()

    async def run_phase(self):
        self.bfm.start_bfm()
        while True:
            int_triggers = await self.seq_item_port.get_next_item()
            await self.bfm.send_interrupts(int_triggers)
            result = await self.bfm.get_interrupts()
            self.ap.write(result)
            int_triggers.result = result
            self.seq_item_port.item_done()
