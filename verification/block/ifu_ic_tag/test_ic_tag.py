import pyuvm
from testbench import BaseEnv, BaseTest
from pyuvm import uvm_sequence
from ifu_ic_tag_seq import Sequence


@pyuvm.test()
class Test(BaseTest):
    def end_of_elaboration_phase(self):
        self.seq = Sequence.create("stimulus")

    async def run(self):
        self.raise_objection()
        await self.seq.start()
        self.drop_objection()
