#
# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: BSD-2-Clause

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles


class Harness(object):
    def __init__(self, dut, clock_mhz, **kwargs):
        self.dut = dut
        self.clk_gen = self.make_clock(clock_mhz)

        # # Set the signal "test_name" to match this test
        # test_name = kwargs.get('test_name', inspect.stack()[1][3])
        # tn = cocotb.binary.BinaryValue(value=test_name.encode(), n_bits=4096)
        # self.dut.test_name.value = tn

    def make_clock(self, clock_mhz):
        clk_period_ns = round(1 / clock_mhz * 1000, 2)
        self.dut._log.info("input clock = %d MHz, period = %.2f ns" %
                           (clock_mhz, clk_period_ns))
        clock = Clock(self.dut.clk, clk_period_ns, units="ns")
        clock_sig = cocotb.start_soon(clock.start())
        return clock_sig

    @cocotb.coroutine
    async def reset(self):
        self.dut.rst_l.value = 1
        await ClockCycles(self.dut.clk, 2)
        self.dut.rst_l.value = 0
        await ClockCycles(self.dut.clk, 2)
        self.dut.rst_l.value = 1
        await ClockCycles(self.dut.clk, 2)
