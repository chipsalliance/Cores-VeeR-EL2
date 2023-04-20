import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles


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

    @cocotb.coroutine
    async def reset(self):
        self.dut.rst_l.value = 1
        await ClockCycles(self.dut.core_clk, 2)
        self.dut.rst_l.value = 0
        await ClockCycles(self.dut.core_clk, 2)
        self.dut.rst_l.value = 1
        await ClockCycles(self.dut.core_clk, 2)

