from cocotb.triggers import RisingEdge, First, FallingEdge
from cocotb.queue import Queue

from pyuvm import *

class Scoreboard(uvm_component):
    def build_phase(self):
        self.int_get_port = uvm_get_port("int_get_port", self)
        self.int_fifo = uvm_tlm_analysis_fifo("int_fifo", self)
        self.int_export = self.int_fifo.analysis_export

    def connect_phase(self):
        self.int_get_port.connect(self.int_fifo.get_export)

    def check_phase(self):
        while self.int_get_port.can_get():
            interrupt, actual_int = self.int_get_port.try_get()


class VeerEl2Bfm(metaclass=utility_classes.Singleton):
    def __init__(self):
        self.dut = cocotb.top
        self.interrupt_mon_queue = Queue(maxsize=0)
        self.interrupts = (self.dut.rvtop.nmi_int, self.dut.rvtop.soft_int, self.dut.rvtop.timer_int, self.dut.rvtop.extintsrc_req)

    async def get_interrupts(self):
        ints = await self.interrupt_mon_queue.get()
        return ints

    async def send_interrupts(self, ints):
        self.dut.rvtop.soft_int.value = ints.soft
        self.dut.rvtop.timer_int.value = ints.timer
        self.dut.rvtop.nmi_int.value = ints.nmi
        self.dut.rvtop.extintsrc_req.value = ints.ext

    async def interrupt_mon_bfm(self):
        while True:
            #await FallingEdge(self.dut.core_clk)
            await First( *[ RisingEdge(sig) for sig in self.interrupts ] )
            int_state = ( sig.value for sig in self.interrupts )
            self.interrupt_mon_queue.put_nowait(int_state)
            return int_state

    def start_bfm(self):
        cocotb.start_soon(self.interrupt_mon_bfm())
