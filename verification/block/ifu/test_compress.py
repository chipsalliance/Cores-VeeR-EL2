import pyuvm
from pyuvm import *

from testbench import BaseEnv, BaseTest
from testbench import CompressedSequence


class TestEnv(BaseEnv):
    def build_phase(self):
        super().build_phase()

        # Add scoreboard
        # self.scoreboard = Scoreboard("scoreboard", self)

    def connect_phase(self):
        super().connect_phase()

        # Connect monitors
        # self.dcm_mon.ap.connect(self.scoreboard.fifo.analysis_export)


@pyuvm.test()
class TestDecompressor(BaseTest):
    """
    Decompression test
    """

    def __init__(self, name, parent):
        super().__init__(name, parent, TestEnv)

    def end_of_elaboration_phase(self):
        super().end_of_elaboration_phase()
        self.seq = CompressedSequence.create("stimulus")

    async def run(self):
        await self.seq.start(self.env.dcm_seqr)

