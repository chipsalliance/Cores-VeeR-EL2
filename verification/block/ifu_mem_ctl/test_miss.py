import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles, FallingEdge

# Miss states
IDLE = 0b000
CRIT_BYP_OK = 0b001
HIT_U_MISS = 0b010
MISS_WAIT = 0b011
CRIT_WRD_RDY = 0b100
SCND_MISS = 0b101
STREAM = 0b110
STALL_SCND_MISS = 0b111


class Axi4LiteBFM:
    def __init__(self, dut):
        self.dut = dut

    async def _wait(self, signal, max_cycles=200):
        """
        Waits for a signal to be asserted in at most max_cycles.
        Raises an exception if it does not
        """
        for _ in range(max_cycles):
            await RisingEdge(self.dut.clk)
            if signal.value != 0:
                break
        else:
            raise RuntimeError("{} timeout".format(signal._name))

    async def read_handler(self):
        cnt = 0
        while cnt < 1:
            axi_araddr = self.dut.ifu_axi_araddr.value
            axi_arid = self.dut.ifu_axi_arid.value
            axi_arsize = self.dut.ifu_axi_arsize.value

            self.dut.ifu_axi_arready = 1
            await RisingEdge(self.dut.clk)

            await self._wait(self.dut.ifu_axi_arvalid)
            self.dut.ifu_axi_arready.value = 0

            self.dut.ifu_axi_rvalid.value = 1
            self.dut.ifu_axi_rdata.value = 0xDEADBEEF
            self.dut.ifu_axi_rresp.value = 0

            await RisingEdge(self.dut.clk)

            self.dut.ifu_axi_rvalid.value = 0
            self.dut.ifu_axi_rdata.value = 0
            self.dut.ifu_axi_rresp.value = 0
            cnt += 1


async def initialize(dut):
    dut.active_clk.value = 0
    dut.free_l2clk.value = 0
    dut.exu_flush_final.value = 0
    dut.dec_tlu_flush_lower_wb.value = 0
    dut.dec_tlu_flush_err_wb.value = 0
    dut.dec_tlu_i0_commit_cmt.value = 0
    dut.dec_tlu_force_halt.value = 0
    dut.ifc_fetch_addr_bf.value = 0
    dut.ifc_fetch_uncacheable_bf.value = 0
    dut.ifc_fetch_req_bf.value = 0
    dut.ifc_fetch_req_bf_raw.value = 0
    dut.ifc_iccm_access_bf.value = 0
    dut.ifc_region_acc_fault_bf.value = 0
    dut.ifc_dma_access_ok.value = 0
    dut.dec_tlu_fence_i_wb.value = 0
    dut.ifu_bp_hit_taken_f.value = 0
    dut.ifu_bp_inst_mask_f.value = 0
    dut.ifu_axi_arready.value = 0
    dut.ifu_axi_rvalid.value = 0
    dut.ifu_axi_rid.value = 0
    dut.ifu_axi_rdata.value = 0
    dut.ifu_axi_rresp.value = 0
    dut.ifu_bus_clk_en.value = 0
    dut.dma_iccm_req.value = 0
    dut.dma_mem_addr.value = 0
    dut.dma_mem_sz.value = 0
    dut.dma_mem_write.value = 0
    dut.dma_mem_wdata.value = 0
    dut.dma_mem_tag.value = 0
    dut.ic_rd_data.value = 0
    dut.ic_debug_rd_data.value = 0
    dut.ictag_debug_rd_data.value = 0
    dut.ic_eccerr.value = 0
    dut.ic_parerr.value = 0
    dut.ic_rd_hit.value = 0
    dut.ic_tag_perr.value = 0
    dut.iccm_rd_data.value = 0
    dut.iccm_rd_data_ecc.value = 0
    dut.ifu_fetch_val.value = 0
    dut.icache_wrdata.value = 0
    dut.icache_dicawics.value = 0
    dut.icache_rd_valid.value = 0
    dut.icache_wr_valid.value = 0
    dut.dec_tlu_core_ecc_disable.value = 0
    dut.ifu_pmp_error.value = 0
    dut.scan_mode.value = 0

    cocotb.start_soon(Clock(dut.clk, 1, units="ns").start())
    cocotb.start_soon(Clock(dut.active_clk, 1, units="ns").start())
    cocotb.start_soon(Clock(dut.free_l2clk, 1, units="ns").start())

    axi_bfm = Axi4LiteBFM(dut)
    cocotb.start_soon(axi_bfm.read_handler())

    # Enable clock
    cocotb.top.ifu_bus_clk_en.value = 1

    # Apply reset (active-low)
    dut.rst_l.value = 0
    await ClockCycles(cocotb.top.clk, 2)
    await FallingEdge(cocotb.top.clk)
    dut.rst_l.value = 1

    await ClockCycles(cocotb.top.clk, 2)


async def write(dut, addr, wdata):
    await RisingEdge(dut.clk)
    dut.dma_iccm_req.value = 1
    dut.dma_mem_addr.value = addr
    dut.dma_mem_write.value = 1
    dut.dma_mem_wdata.value = wdata
    await RisingEdge(dut.clk)
    dut.dma_iccm_req.value = 0
    dut.dma_mem_addr.value = 0
    dut.dma_mem_write.value = 0
    dut.dma_mem_wdata.value = 0


async def read(dut, addr):
    await RisingEdge(dut.clk)
    dut.dma_iccm_req.value = 1
    dut.dma_mem_write.value = 0
    dut.dma_mem_addr.value = addr


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


@cocotb.test()
async def test_full_tap_fsm(dut):
    await initialize(dut)

    # Ensure FSM starts in Test-Logic-Reset
    await RisingEdge(dut.clk)
    verify_state(dut, IDLE)

    # Issue instruction without a hit
    dut.ifc_fetch_req_bf.value = 1
    dut.ifc_fetch_uncacheable_bf.value = 1
    # dut.ifc_fetch_req_bf_raw.value = 1
    dut.ifc_fetch_addr_bf.value = 128
    dut.ifc_dma_access_ok.value = 1

    await RisingEdge(dut.clk)

    dut.ifc_fetch_req_bf.value = 0
    dut.ifc_fetch_uncacheable_bf.value = 0
    dut.ifc_fetch_addr_bf.value = 0
    dut.ifc_dma_access_ok.value = 0

    await write(dut, 42, 44)

    await ClockCycles(cocotb.top.clk, 1)
    verify_state(dut, CRIT_BYP_OK)

    # dut.exu_flush_final.value = 1 HIT_U_MISS

    await ClockCycles(cocotb.top.clk, 2)
    verify_state(dut, CRIT_WRD_RDY)

    # Apply reset (active-low)
    dut.rst_l.value = 0

    await RisingEdge(dut.clk)
    verify_state(dut, IDLE)
