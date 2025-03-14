import cocotb
from cocotb.triggers import ClockCycles, RisingEdge

from common import (
    get_bitflip_mask,
    initialize,
    rand_iccm_addr,
    rand_ifu_addr,
    read,
    reset,
)

# Error states
ERR_IDLE = 0b000
IC_WFF = 0b001
ECC_WFF = 0b010
ECC_CORR = 0b011
DMA_SB_ERR = 0b100


async def fetch_miss(dut, addr, req_bf_raw=1, uncacheable_bf=1):
    dut.ifc_fetch_req_bf.value = 1
    dut.ifc_fetch_req_bf_raw.value = req_bf_raw
    dut.ifc_fetch_uncacheable_bf.value = uncacheable_bf
    dut.ifc_fetch_addr_bf.value = addr
    await RisingEdge(dut.clk)
    dut.ifc_fetch_req_bf_raw.value = 0
    dut.ifc_fetch_uncacheable_bf.value = 0
    dut.ifc_fetch_addr_bf.value = 0


def verify_state(dut, exp_state):
    state_names = [
        "ERR_IDLE",
        "IC_WFF",
        "ECC_WFF",
        "ECC_CORR",
        "DMA_SB_ERR",
    ]
    assert (
        dut.ifu_mem_ctl.perr_state.value == exp_state
    ), f"Expected state {state_names[exp_state]}, got {dut.ifu_mem_ctl.perr_state.value}"


async def dma_sb_error(dut, force_halt=False):
    verify_state(dut, ERR_IDLE)
    dut.ifc_dma_access_ok.value = 1
    dut.iccm_rd_data.value = 44
    dut.iccm_rd_data_ecc.value = 44 ^ get_bitflip_mask(0)
    await fetch_miss(dut, rand_ifu_addr())
    await read(dut, rand_iccm_addr())
    await RisingEdge(dut.iccm_dma_rvalid)
    # dec_tlu_force_halt must appear here to achieve DMA_SB_ERR -> ERR_IDLE transition
    # FSM always switches state from `DMA_SB_ERR` in the next cycle
    if force_halt:
        dut.dec_tlu_force_halt.value = 1
    await RisingEdge(dut.clk)
    verify_state(dut, DMA_SB_ERR)


@cocotb.test()
async def test_dma_sb_error(dut):
    await initialize(dut)
    verify_state(dut, ERR_IDLE)

    await dma_sb_error(dut)

    await reset(dut)
    verify_state(dut, ERR_IDLE)


@cocotb.test()
async def test_dma_sb_error_force_halt(dut):
    await initialize(dut)
    verify_state(dut, ERR_IDLE)

    await dma_sb_error(dut, force_halt=True)
    await ClockCycles(dut.clk, 1)
    verify_state(dut, ERR_IDLE)


@cocotb.test()
async def test_ecc_corr(dut):
    await initialize(dut)
    verify_state(dut, ERR_IDLE)

    await dma_sb_error(dut)

    await RisingEdge(dut.clk)
    verify_state(dut, ECC_CORR)

    await reset(dut)
    verify_state(dut, ERR_IDLE)


async def ic_wff(dut):
    verify_state(dut, ERR_IDLE)

    dut.ic_tag_perr.value = 1
    dut.ifc_dma_access_ok.value = 1
    dut.iccm_rd_data.value = 44
    dut.iccm_rd_data_ecc.value = 44 ^ get_bitflip_mask(1)
    await fetch_miss(dut, rand_ifu_addr())
    await read(dut, rand_iccm_addr())

    await RisingEdge(dut.clk)
    verify_state(dut, IC_WFF)


@cocotb.test()
async def test_ic_wff(dut):
    await initialize(dut)

    await ic_wff(dut)

    await reset(dut)
    verify_state(dut, ERR_IDLE)


@cocotb.test()
async def test_ic_wff_force_halt(dut):
    await initialize(dut)

    await ic_wff(dut)

    dut.dec_tlu_force_halt.value = 1
    await ClockCycles(dut.clk, 2)
    verify_state(dut, ERR_IDLE)


async def ecc_wff(dut):
    await initialize(dut)
    verify_state(dut, ERR_IDLE)

    dut.ic_tag_perr.value = 1
    dut.ifc_dma_access_ok.value = 1
    dut.ifc_iccm_access_bf.value = 1
    dut.iccm_rd_data.value = 44
    dut.iccm_rd_data_ecc.value = 44
    await fetch_miss(dut, rand_ifu_addr())

    await ClockCycles(dut.clk, 2)
    verify_state(dut, ECC_WFF)


@cocotb.test()
async def test_ecc_wff(dut):
    await initialize(dut)
    verify_state(dut, ERR_IDLE)

    await ecc_wff(dut)

    await reset(dut)
    verify_state(dut, ERR_IDLE)


@cocotb.test()
async def test_ecc_wff_force_halt(dut):
    await initialize(dut)

    await ecc_wff(dut)

    dut.dec_tlu_force_halt.value = 1
    await ClockCycles(dut.clk, 2)
    verify_state(dut, ERR_IDLE)
