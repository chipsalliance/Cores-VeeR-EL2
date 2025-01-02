import pyuvm
from testbench import BaseEnv, BaseTest, Sequence


@pyuvm.test()
class Test(BaseTest):

    def __init__(self, name, parent):
        super().__init__(name, parent, BaseEnv)

    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = Sequence.create("stimulus")

    async def run(self):
        await self.seq.start(self.env.seqr)
