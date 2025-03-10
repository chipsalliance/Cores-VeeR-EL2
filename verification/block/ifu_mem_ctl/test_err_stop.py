import cocotb
from cocotb.triggers import ClockCycles, RisingEdge

from common import initialize, rand_ifu_addr

# Error stop states
ERR_STOP_IDLE = 0b00
ERR_FETCH1 = 0b01
ERR_FETCH2 = 0b10
ERR_STOP_FETCH = 0b11


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
        "ERR_STOP_IDLE",
        "ERR_FETCH1",
        "ERR_FETCH2",
        "ERR_STOP_FETCH",
    ]
    assert (
        dut.ifu_mem_ctl.err_stop_state.value == exp_state
    ), f"Expected state {state_names[exp_state]}, got {dut.ifu_mem_ctl.err_stop_state.value}"


@cocotb.test()
async def test_err_fetch1(dut):
    await initialize(dut)
    verify_state(dut, ERR_STOP_IDLE)
    # verify_state(dut, ERR_IDLE)

    dut.ic_tag_perr.value = 1
    dut.ifc_dma_access_ok.value = 1
    dut.ifc_iccm_access_bf.value = 1
    dut.iccm_rd_data.value = 44
    dut.iccm_rd_data_ecc.value = 44
    await fetch_miss(dut, rand_ifu_addr())

    await ClockCycles(dut.clk, 2)
    dut.dec_tlu_flush_err_wb.value = 1
    # verify_state(dut, ECC_WFF)
    await ClockCycles(dut.clk, 2)
    verify_state(dut, ERR_FETCH1)


@cocotb.test()
async def test_err_fetch2(dut):
    await initialize(dut)
    verify_state(dut, ERR_STOP_IDLE)
    # verify_state(dut, ERR_IDLE)

    dut.ic_tag_perr.value = 1
    dut.ifc_dma_access_ok.value = 1
    dut.ifc_iccm_access_bf.value = 1
    dut.ic_rd_data.value = 2**63 - 1
    dut.iccm_rd_data.value = 44
    dut.iccm_rd_data_ecc.value = 44
    dut.ifu_fetch_val.value = 1
    await fetch_miss(dut, rand_ifu_addr())

    await ClockCycles(dut.clk, 2)
    dut.dec_tlu_flush_err_wb.value = 1
    # verify_state(dut, ECC_WFF)
    await ClockCycles(dut.clk, 2)
    verify_state(dut, ERR_FETCH1)
    dut.ifu_fetch_val.value = 0
    await ClockCycles(dut.clk, 1)
    verify_state(dut, ERR_FETCH2)
    await ClockCycles(dut.clk, 1)
    verify_state(dut, ERR_FETCH2)
    await ClockCycles(dut.clk, 5)

    dut.dec_tlu_force_halt.value = 1
    await ClockCycles(dut.clk, 2)
    verify_state(dut, ERR_STOP_IDLE)


# ERR_STOP_FETCH -> ERR_STOP_FETCH
@cocotb.test()
async def test_err_stop_fetch(dut):
    await initialize(dut)
    verify_state(dut, ERR_STOP_IDLE)
    # verify_state(dut, ERR_IDLE)

    dut.ic_tag_perr.value = 1
    dut.ifc_dma_access_ok.value = 1
    dut.ifc_iccm_access_bf.value = 1
    dut.ic_rd_data.value = 2**63 - 1
    dut.iccm_rd_data.value = 44
    dut.iccm_rd_data_ecc.value = 44
    dut.ifu_fetch_val.value = 1
    await fetch_miss(dut, rand_ifu_addr())

    await ClockCycles(dut.clk, 2)
    dut.dec_tlu_flush_err_wb.value = 1
    # verify_state(dut, ECC_WFF)
    await ClockCycles(dut.clk, 2)
    verify_state(dut, ERR_FETCH1)
    await RisingEdge(dut.clk)
    verify_state(dut, ERR_FETCH2)
    dut.dec_tlu_flush_err_wb.value = 0
    await RisingEdge(dut.clk)
    verify_state(dut, ERR_STOP_FETCH)
    await ClockCycles(dut.clk, 5)
