import cocotb
from cocotb.triggers import ClockCycles, RisingEdge

from common import (
    initialize,
    rand_iccm_addr,
    rand_iccm_data,
    rand_ifu_addr,
    reset,
    write,
)

# Miss states
IDLE = 0b000
CRIT_BYP_OK = 0b001
HIT_U_MISS = 0b010
MISS_WAIT = 0b011
CRIT_WRD_RDY = 0b100
SCND_MISS = 0b101
STREAM = 0b110
STALL_SCND_MISS = 0b111


async def fetch_miss(dut, addr, req_bf_raw=1, uncacheable_bf=1, dma_access_ok=0):
    dut.ifc_fetch_req_bf.value = 1
    dut.ifc_fetch_req_bf_raw.value = req_bf_raw
    dut.ifc_fetch_uncacheable_bf.value = uncacheable_bf
    dut.ifc_fetch_addr_bf.value = addr
    dut.ifc_dma_access_ok.value = dma_access_ok
    await RisingEdge(dut.clk)
    dut.ifc_fetch_req_bf.value = 0
    dut.ifc_fetch_req_bf_raw.value = 0
    dut.ifc_fetch_uncacheable_bf.value = 0
    dut.ifc_fetch_addr_bf.value = 0
    dut.ifc_dma_access_ok.value = 0


def verify_state(dut, exp_state):
    state_names = [
        "IDLE",
        "CRIT_BYP_OK",
        "HIT_U_MISS",
        "MISS_WAIT",
        "CRIT_WRD_RDY",
        "SCND_MISS",
        "STREAM",
        "STALL_SCND_MISS",
    ]
    assert (
        dut.ifu_mem_ctl.miss_state.value == exp_state
    ), f"Expected state {state_names[exp_state]}, got {dut.ifu_mem_ctl.miss_state.value}"


async def crit_byp_ok(dut):
    verify_state(dut, IDLE)

    await fetch_miss(dut, 128, dma_access_ok=1)
    await write(dut, rand_iccm_addr(), rand_iccm_data())

    await RisingEdge(dut.clk)
    verify_state(dut, CRIT_BYP_OK)


@cocotb.test()
async def test_crit_byp_ok(dut):
    await initialize(dut)
    await crit_byp_ok(dut)
    await reset(dut)
    verify_state(dut, IDLE)


@cocotb.test()
async def test_crit_byp_ok_force_halt(dut):
    await initialize(dut)
    await crit_byp_ok(dut)

    dut.dec_tlu_force_halt.value = 1
    await ClockCycles(dut.clk, 2)
    verify_state(dut, IDLE)


async def crit_wrd_rdy(dut):
    verify_state(dut, IDLE)

    await fetch_miss(dut, rand_ifu_addr())
    await write(dut, rand_iccm_addr(), rand_iccm_data())

    await RisingEdge(dut.clk)
    verify_state(dut, CRIT_BYP_OK)

    await write(dut, rand_iccm_addr(), rand_iccm_data())

    await ClockCycles(dut.clk, 2)
    verify_state(dut, CRIT_WRD_RDY)


@cocotb.test()
async def test_crit_wrd_rdy(dut):
    await initialize(dut)
    await crit_wrd_rdy(dut)
    await reset(dut)
    verify_state(dut, IDLE)


@cocotb.test()
async def test_crit_wrd_rdy_force_halt(dut):
    await initialize(dut)
    await crit_wrd_rdy(dut)

    dut.dec_tlu_force_halt.value = 1
    await ClockCycles(dut.clk, 2)
    verify_state(dut, IDLE)


async def hit_u_miss(dut):
    verify_state(dut, IDLE)

    await fetch_miss(dut, rand_ifu_addr(), req_bf_raw=0, dma_access_ok=1)
    await write(dut, rand_iccm_addr(), rand_iccm_data())

    await ClockCycles(cocotb.top.clk, 1)
    verify_state(dut, CRIT_BYP_OK)

    dut.exu_flush_final.value = 1
    await ClockCycles(cocotb.top.clk, 2)
    verify_state(dut, HIT_U_MISS)
    dut.exu_flush_final.value = 0


@cocotb.test()
async def test_hit_u_miss(dut):
    await initialize(dut)
    await hit_u_miss(dut)
    await reset(dut)
    verify_state(dut, IDLE)


@cocotb.test()
async def test_hit_u_miss_force_halt(dut):
    await initialize(dut)
    await hit_u_miss(dut)

    dut.dec_tlu_force_halt.value = 1
    await ClockCycles(dut.clk, 2)
    verify_state(dut, IDLE)


async def scnd_miss(dut):
    verify_state(dut, IDLE)
    await hit_u_miss(dut)
    await fetch_miss(dut, rand_ifu_addr(), req_bf_raw=0, dma_access_ok=1)
    await write(dut, rand_iccm_addr(), rand_iccm_data())

    await RisingEdge(dut.clk)
    verify_state(dut, SCND_MISS)


@cocotb.test()
async def test_scnd_miss(dut):
    await initialize(dut)
    await scnd_miss(dut)
    await reset(dut)
    verify_state(dut, IDLE)


@cocotb.test()
async def test_scnd_miss_force_halt(dut):
    await initialize(dut)
    await scnd_miss(dut)

    dut.dec_tlu_force_halt.value = 1
    await ClockCycles(dut.clk, 2)
    verify_state(dut, IDLE)


async def stall_scnd_miss(dut):
    verify_state(dut, IDLE)
    await hit_u_miss(dut)
    await fetch_miss(dut, 0, req_bf_raw=0)
    await write(dut, rand_iccm_addr(), rand_iccm_data())

    await ClockCycles(dut.clk, 1)
    verify_state(dut, STALL_SCND_MISS)


@cocotb.test()
async def test_stall_scnd_miss(dut):
    await initialize(dut)
    await stall_scnd_miss(dut)
    await reset(dut)
    verify_state(dut, IDLE)


@cocotb.test()
async def test_stall_scnd_miss_force_halt(dut):
    await initialize(dut)
    await stall_scnd_miss(dut)

    dut.dec_tlu_force_halt.value = 1
    await ClockCycles(dut.clk, 2)
    verify_state(dut, IDLE)
