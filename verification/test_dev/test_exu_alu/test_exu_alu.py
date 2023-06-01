#
# Copyright (c) 2023 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: BSD-2-Clause

import os
from os import environ
import random
import cocotb
from cocotb.triggers import ClockCycles
from .common import Harness


@cocotb.test()
async def test_add(dut):
    iterations = int(os.environ.get("iterations", "5"))
    inputs = random.sample(range(0x1, 0x3fffffff), 2 * iterations)

    harness = Harness(dut, 100)

    await harness.reset()

    for i in range(iterations):
        offset = i * 2
        harness.dut.enable.value = 1
        harness.dut.ap.value = 1 << 8          # predecoded operation
        harness.dut.a_in.value = inputs[offset + 0]
        harness.dut.b_in.value = inputs[offset + 1]
        harness.dut.valid_in.value = 1

        await ClockCycles(harness.dut.clk, 1)

        assert harness.dut.result.value.integer == (
            inputs[offset + 0] + inputs[offset + 1])

    harness.clk_gen.kill()


@cocotb.test()
async def test_sub(dut):
    iterations = int(os.environ.get("iterations", "5"))
    inputs = random.sample(range(0x1, 0x3fffffff), 2 * iterations)

    harness = Harness(dut, 100)

    await harness.reset()

    for i in range(iterations):
        offset = i * 2
        harness.dut.enable.value = 1
        harness.dut.ap.value = 1 << 7          # predecoded operation
        harness.dut.a_in.value = max(inputs[offset + 0], inputs[offset + 1])
        harness.dut.b_in.value = min(inputs[offset + 0], inputs[offset + 1])
        harness.dut.valid_in.value = 1

        await ClockCycles(harness.dut.clk, 1)

        assert harness.dut.result.value.integer == (max(
            inputs[offset + 0], inputs[offset + 1]) - min(inputs[offset + 0], inputs[offset + 1]))

    harness.clk_gen.kill()
