#
# Copyright (c) 2023 Antmicro
# SPDX-License-Identifier: Apache-2.0

import os

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, FallingEdge

# ==============================================================================


async def start_clocks(dut):
    """
    Starts DUT clocks
    """

    # When VeeR is built in FPGA-optimized mode rawclk is used by rvdffs inside
    # the gateway. Otherwise the gw_clk is used. For testing start both of them.
    gw_clk = Clock(dut.gw_clk, 1, units="ns")
    rawclk = Clock(dut.rawclk, 1, units="ns")

    cocotb.start_soon(gw_clk.start(start_high=False))
    cocotb.start_soon(rawclk.start(start_high=False))

    # Enable
    cocotb.top.clken.value = 1


async def do_reset(dut):
    """
    Resets the DUT
    """

    await ClockCycles(dut.gw_clk, 2)

    dut.rst_l.value = 0

    await ClockCycles(dut.gw_clk, 1)
    await FallingEdge(dut.gw_clk)

    dut.rst_l.value = 1


async def clear_pending(dut):
    """
    Clears the pending interrupt flag of the tested module
    """

    dut.meigwclr.value = 1
    await ClockCycles(dut.gw_clk, 1)
    dut.meigwclr.value = 0

    await ClockCycles(dut.gw_clk, 3)


# ==============================================================================


async def test_level(dut, pol):
    """
    Tests level-sensitive interrupt
    """

    # Default state
    dut.extintsrc_req.value = not pol

    # Level-sensitive
    dut.meigwctrl_type.value = 0
    dut.meigwctrl_polarity.value = not pol

    # Reset
    await do_reset(dut)

    # Wait
    await ClockCycles(dut.gw_clk, 3)

    # The request should not be pending
    assert dut.extintsrc_req_config.value == 0

    # Request an interrupt
    dut.extintsrc_req.value = pol
    await ClockCycles(dut.gw_clk, 3)

    # The request should be pending now
    assert dut.extintsrc_req_config.value == 1

    # Clear the pending bit
    await clear_pending(dut)

    # The request should be still pending (level sensitive)
    assert dut.extintsrc_req_config.value == 1

    # Cancel the request
    dut.extintsrc_req.value = not pol
    await ClockCycles(dut.gw_clk, 3)

    # The request should be still pending (latched state)
    # assert dut.extintsrc_req_config.value == 1

    # FIXME: It appears that the gateway does not latch the trigger state
    # in level-sensitive mode but rather passes through the interrupt request
    # signal.
    assert dut.extintsrc_req_config.value == 0

    # Clear the pending bit again
    await clear_pending(dut)

    # The request should not be pending now
    assert dut.extintsrc_req_config.value == 0

    # Wait
    await ClockCycles(dut.gw_clk, 3)


@cocotb.test()
async def test_level_hi(dut):
    await start_clocks(dut)
    await test_level(dut, True)


@cocotb.test()
async def test_level_lo(dut):
    await start_clocks(dut)
    await test_level(dut, False)


async def test_edge(dut, pol):
    """
    Tests edge-sensitive interrupt
    """

    # Default state
    dut.extintsrc_req.value = not pol

    # Edge-sensitive
    dut.meigwctrl_type.value = 1
    dut.meigwctrl_polarity.value = not pol

    # Reset
    await do_reset(dut)

    # Wait
    await ClockCycles(dut.gw_clk, 3)

    # The request should not be pending
    assert dut.extintsrc_req_config.value == 0

    # Request an interrupt
    dut.extintsrc_req.value = pol
    await ClockCycles(dut.gw_clk, 1)
    dut.extintsrc_req.value = not pol

    await ClockCycles(dut.gw_clk, 3)

    # The request should be pending now
    assert dut.extintsrc_req_config.value == 1

    # Wait
    await ClockCycles(dut.gw_clk, 10)

    # The request should still be pending now
    assert dut.extintsrc_req_config.value == 1

    # Clear the pending bit
    await clear_pending(dut)

    # The request should not be pending now
    assert dut.extintsrc_req_config.value == 0

    # Wait
    await ClockCycles(dut.gw_clk, 3)


@cocotb.test()
async def test_edge_rising(dut):
    await start_clocks(dut)
    await test_edge(dut, True)


# @cocotb.test() # TODO: Falling edge case is failing. Re-enable upon RTL fix
async def test_edge_falling(dut):
    await start_clocks(dut)
    await test_edge(dut, False)


async def test_edge_reset(dut, pol):
    """
    Tests edge-sensitive interrupt
    """

    # Default state
    dut.extintsrc_req.value = not pol

    # Edge-sensitive
    dut.meigwctrl_type.value = 1
    dut.meigwctrl_polarity.value = not pol

    # Reset
    await do_reset(dut)

    # Wait
    await ClockCycles(dut.gw_clk, 3)

    # The request should not be pending
    assert dut.extintsrc_req_config.value == 0

    # Request an interrupt
    dut.extintsrc_req.value = pol
    await ClockCycles(dut.gw_clk, 1)
    dut.extintsrc_req.value = not pol

    await ClockCycles(dut.gw_clk, 3)

    # The request should be pending now
    assert dut.extintsrc_req_config.value == 1

    # Wait
    await ClockCycles(dut.gw_clk, 10)

    # Reset
    await do_reset(dut)

    # Wait
    await ClockCycles(dut.gw_clk, 3)

    # The request should not be pending now
    assert dut.extintsrc_req_config.value == 0

    # Wait
    await ClockCycles(dut.gw_clk, 3)


@cocotb.test()
async def test_edge_rising_reset(dut):
    await start_clocks(dut)
    await test_edge_reset(dut, True)


# @cocotb.test() # TODO: Falling edge case is failing. Re-enable upon RTL fix
async def test_edge_falling_reset(dut):
    await start_clocks(dut)
    await test_edge_reset(dut, False)
