import cocotb
import pyuvm
from pyuvm import *
from .uvm_common import Scoreboard
from .irq_agent import IrqMonitor, IrqDriver, IrqTriggerSeqItem

class IrqRandomSeq(uvm_sequence):
    async def body(self):
        int_tr = IrqTriggerSeqItem("irq_trigger", 0, 0, 0, 0)
        await self.start_item(int_tr)
        int_tr.randomize()
        await self.finish_item(int_tr)

class IrqTestSeq(uvm_sequence):
    async def body(self):
        seqr = ConfigDB().get(None, "", "SEQR")
        random = IrqRandomSeq("random")
        await random.start(seqr)

class VeerEl2Env(uvm_env):
    def build_phase(self):
        self.seqr = uvm_sequencer("seqr", self)
        ConfigDB().set(None, "*", "SEQR", self.seqr)
        self.int_mon = IrqMonitor("int_monitor", self)
        self.int_drv = IrqDriver("int_driver", self)
        self.scoreboard = Scoreboard("scoreboard", self)

    def connect_phase(self):
        self.int_drv.seq_item_port.connect(self.seqr.seq_item_export)
        self.int_mon.ap.connect(self.scoreboard.int_export)

@pyuvm.test()
class BaseTest(uvm_test):
    def build_phase(self):
        self.set_default_logging_level(logging.DEBUG)
        self.env = VeerEl2Env("env", self)

    def end_of_elaboration_phase(self):
        self.test_all = IrqTestSeq.create("test_irq")

    async def run_phase(self):
        self.raise_objection()
        await self.test_all.start()
        self.drop_objection()
