import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, Edge
from cocotb.result import TestSuccess, TestFailure


class Harness(object):
    def __init__(self, dut, clock_mhz, **kwargs):
        self.dut = dut
        self.clk_gen = self.make_clock(clock_mhz)

    def make_clock(self, clock_mhz):
        clk_period_ns = round(1 / clock_mhz * 1000, 2)
        self.dut._log.info("input clock = %d MHz, period = %.2f ns" % (clock_mhz, clk_period_ns))
        clock = Clock(self.dut.core_clk, clk_period_ns, units="ns")
        clock_sig = cocotb.start_soon(clock.start())
        return clock_sig

    def finish(self, exec_result):
        self.clk_gen.kill()

        self.dut._log.info("minstret = %0d" % (self.dut.rvtop.veer.dec.tlu.minstretl.value))
        self.dut._log.info("mcycle = %0d" % (self.dut.rvtop.veer.dec.tlu.mcyclel.value))

        if exec_result == True:
            raise TestSuccess("Program execution passed")
        if exec_result == False:
            raise TestFailure("Program execution failed")

    @cocotb.coroutine
    async def mailbox_monitor(self, asciioutput=None):
        while True:
            await RisingEdge(self.dut.mailbox_write)
            if self.dut.mailbox_data_val.value and asciioutput is not None:
                asciioutput(chr(self.dut.WriteData.value & 0xff))
            if (self.dut.WriteData.value & 0xff) == 0xff:
                self.dut._log.info("TEST_PASSED")
                return True
            if (self.dut.WriteData.value & 0xff) == 0x01:
                self.dut._log.info("TEST_FAILED")
                return False

    @cocotb.coroutine
    async def cycle_monitor(self):
        while await Edge(self.dut.cycleCnt):
            assert self.dut.cycleCnt.value.integer < self.dut.MAX_CYCLES.value.integer
