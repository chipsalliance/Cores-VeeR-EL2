from jtag_bfm import JTAGBfm as BFM
from pyuvm import *

from common import *


class JTAGAgent(uvm_agent):
    """
    Seqr <---> Driver <---> Top module
              Monitor <------^
    """

    def build_phase(self):
        self.seqr = uvm_sequencer("seqr", self)
        ConfigDB().set(None, "*", "JTAG_SEQR", self.seqr)

        self.monitor = JTAGMonitor("jtag_monitor", self, "rsp_monitor_q_get")
        self.driver = JTAGDriver("jtag_driver", self)

    def connect_phase(self):
        self.driver.seq_item_port.connect(self.seqr.seq_item_export)


class JTAGDriver(uvm_driver):
    def build_phase(self):
        self.ap = uvm_analysis_port("ap_drv", self)

    def start_of_simulation_phase(self):
        self.bfm = BFM()

    async def run_phase(self):
        await self.bfm.reset()
        self.bfm.start_bfm()

        while True:
            item = await self.seq_item_port.get_next_item()
            await self.bfm.req_driver_q_put(item.tms, item.tdi)
            self.seq_item_port.item_done()


class JTAGMonitor(uvm_component):
    def __init__(self, name, parent, method_name):
        super().__init__(name, parent)
        self.method_name = method_name

    def build_phase(self):
        self.ap = uvm_analysis_port("ap_mon", self)
        self.bfm = BFM()
        self.get_method = getattr(self.bfm, self.method_name)

    async def run_phase(self):
        while True:
            datum = await self.get_method()
            self.logger.debug(f"JTAG Monitor req: {datum}")
            self.ap.write(datum)
