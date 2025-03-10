import random

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, FallingEdge, RisingEdge

ICCM_BASE = 0xEE000000
ICCM_SIZE = 0x10000


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
        while True:
            if not self.dut.rst_l.value:
                await RisingEdge(self.dut.rst_l)

            self.dut.ifu_axi_arready.value = 1
            await self._wait(self.dut.ifu_axi_arvalid)
            self.dut.ifu_axi_arready.value = 0

            self.dut.ifu_axi_rvalid.value = 1
            self.dut.ifu_axi_rdata.value = rand_iccm_data()
            self.dut.ifu_axi_rresp.value = 0

            await RisingEdge(self.dut.clk)

            self.dut.ifu_axi_rvalid.value = 0
            self.dut.ifu_axi_rdata.value = 0
            self.dut.ifu_axi_rresp.value = 0


async def reset(dut):
    # Apply reset (active-low)
    dut.rst_l.value = 0
    await ClockCycles(cocotb.top.clk, 2)
    await FallingEdge(cocotb.top.clk)
    dut.rst_l.value = 1
    await ClockCycles(cocotb.top.clk, 2)

    cocotb.top.ifu_bus_clk_en.value = 1


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

    await reset(dut)


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


def rand_iccm_addr():
    return random.randint(ICCM_BASE, ICCM_BASE + ICCM_SIZE)


def rand_iccm_data():
    return random.randint(0, (2**64) - 1)


def rand_ifu_addr():
    return random.randint(0, (2**31) - 1)


def get_bitflip_mask(do_double_bit):
    return 2 << (random.randint(0, 2**32 - 1) % (37)) | ((2**40) & ((2**40) - do_double_bit))
