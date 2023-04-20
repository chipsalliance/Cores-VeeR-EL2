import cocotb
from cocotb.triggers import ClockCycles
from .common import Harness


@cocotb.test()
async def test_basic(dut):
    harness = Harness(dut, 100)

    await harness.reset()

    await ClockCycles(harness.dut.core_clk, 100)

    harness.clk_gen.kill()
