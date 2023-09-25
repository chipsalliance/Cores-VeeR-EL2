import pyuvm
from pyuvm import *
from testbench import BaseEnv, BaseTest, CompressedSequence


@pyuvm.test()
class TestDecompressor(BaseTest):
    """
    Decompression test
    """

    def __init__(self, name, parent):
        super().__init__(name, parent, BaseEnv)

    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = CompressedSequence.create("stimulus")

    async def run(self):
        await self.seq.start(self.env.dcm_seqr)
