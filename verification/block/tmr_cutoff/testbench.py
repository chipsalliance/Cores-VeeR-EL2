# Copyright (c) 2024 Antmicro <www.antmicro.com>
# SPDX-License-Identifier: Apache-2.0
import logging
import os
import random

import cocotb
from cocotb.handle import Force, Release
from cocotb.triggers import Edge, First, Timer
from pyuvm import (
    ConfigDB,
    uvm_analysis_port,
    uvm_component,
    uvm_driver,
    uvm_env,
    uvm_get_port,
    uvm_monitor,
    uvm_report_object,
    uvm_sequence_item,
    uvm_sequencer,
    uvm_test,
    uvm_tlm_analysis_fifo,
)

# ==============================================================================

# FIXME: Sync with makefile somehow
MuBiFalse = 0b01
MuBiTrue = 0b10

# Inputs to the el2_tmr_complex_wrapper. They are not used during the test but
# are initialized to 0 at the beginning
INPUTS = (
    "rst_vec",
    "nmi_int",
    "nmi_vec",
    "i_cpu_halt_req",
    "i_cpu_run_req",
    "core_id",
    "mem_export_iccm_bank_dout",
    "mem_export_iccm_bank_ecc",
    "mem_export_dccm_bank_ecc",
    "icache_export_wb_packeddout_pre",
    "icache_export_wb_dout_pre_up",
    "icache_export_ic_tag_data_raw_packed_pre",
    "icache_export_ic_tag_data_raw_pre",
    "mpc_debug_halt_req",
    "mpc_debug_run_req",
    "mpc_reset_run_req",
    "lsu_axi_awready",
    "lsu_axi_wready",
    "lsu_axi_bvalid",
    "lsu_axi_bresp",
    "lsu_axi_bid",
    "lsu_axi_arready",
    "lsu_axi_rvalid",
    "lsu_axi_rid",
    "lsu_axi_rdata",
    "lsu_axi_rresp",
    "lsu_axi_rlast",
    "ifu_axi_awready",
    "ifu_axi_wready",
    "ifu_axi_bvalid",
    "ifu_axi_bresp",
    "ifu_axi_bid",
    "ifu_axi_arready",
    "ifu_axi_rvalid",
    "ifu_axi_rid",
    "ifu_axi_rdata",
    "ifu_axi_rresp",
    "ifu_axi_rlast",
    "sb_axi_awready",
    "sb_axi_wready",
    "sb_axi_bvalid",
    "sb_axi_bresp",
    "sb_axi_bid",
    "sb_axi_arready",
    "sb_axi_rvalid",
    "sb_axi_rid",
    "sb_axi_rdata",
    "sb_axi_rresp",
    "sb_axi_rlast",
    "dma_axi_awvalid",
    "dma_axi_awid",
    "dma_axi_awaddr",
    "dma_axi_awsize",
    "dma_axi_awprot",
    "dma_axi_awlen",
    "dma_axi_awburst",
    "dma_axi_wvalid",
    "dma_axi_wdata",
    "dma_axi_wstrb",
    "dma_axi_wlast",
    "dma_axi_bready",
    "dma_axi_arvalid",
    "dma_axi_arid",
    "dma_axi_araddr",
    "dma_axi_arsize",
    "dma_axi_arprot",
    "dma_axi_arlen",
    "dma_axi_arburst",
    "dma_axi_rready",
    "hrdata",
    "hready",
    "hresp",
    "lsu_hrdata",
    "lsu_hready",
    "lsu_hresp",
    "sb_hrdata",
    "sb_hready",
    "sb_hresp",
    "dma_hsel",
    "dma_haddr",
    "dma_hburst",
    "dma_hmastlock",
    "dma_hprot",
    "dma_hsize",
    "dma_htrans",
    "dma_hwrite",
    "dma_hwdata",
    "dma_hreadyin",
    "lsu_bus_clk_en",
    "ifu_bus_clk_en",
    "dbg_bus_clk_en",
    "dma_bus_clk_en",
    "dmi_reg_en",
    "dmi_reg_addr",
    "dmi_reg_wr_en",
    "dmi_reg_wdata",
    "extintsrc_req",
    "timer_int",
    "soft_int",
    "scan_mode",
)

# This list contains pairs of signals that are gated. The first one in the pair
# is gate input, the second is the output
SIGNALS = (
    ("el2_tmr_complex.cores.veer.trace_rv_i_address_ip", "trace_rv_i_address_ip"),
    ("el2_tmr_complex.cores.veer.trace_rv_i_valid_ip", "trace_rv_i_valid_ip"),
    ("el2_tmr_complex.cores.veer.trace_rv_i_exception_ip", "trace_rv_i_exception_ip"),
    ("el2_tmr_complex.cores.veer.trace_rv_i_ecause_ip", "trace_rv_i_ecause_ip"),
    ("el2_tmr_complex.cores.veer.trace_rv_i_interrupt_ip", "trace_rv_i_interrupt_ip"),
    ("el2_tmr_complex.cores.veer.trace_rv_i_tval_ip", "trace_rv_i_tval_ip"),
    ("el2_tmr_complex.cores.veer.o_debug_mode_status", "o_debug_mode_status"),
    # For debug/halt status the gates are between each VeeR and the voter as
    # these are muxed lated and monitored by the recovery FSM
    ("el2_tmr_complex.cores.veer.o_cpu_halt_ack", "o_cpu_halt_ack"),
    ("el2_tmr_complex.cores.veer.o_cpu_halt_status", "o_cpu_halt_status"),
    ("el2_tmr_complex.cores.veer.o_cpu_run_ack", "o_cpu_run_ack"),
    ("el2_tmr_complex.cores.veer.mpc_debug_halt_ack", "mpc_debug_halt_ack"),
    ("el2_tmr_complex.cores.veer.mpc_debug_run_ack", "mpc_debug_run_ack"),
    # FIXME: Interfaces...
    # ("el2_tmr_complex.cores.mem.mem_export.clk", "mem_export_clk"),
    # ("el2_tmr_complex.cores.mem.mem_export.iccm_clken", "mem_export_iccm_clken"),
    # ("el2_tmr_complex.cores.mem.mem_export.iccm_wren_bank", "mem_export_iccm_wren_bank"),
    # ("el2_tmr_complex.cores.mem.mem_export.iccm_addr_bank", "mem_export_iccm_addr_bank"),
    # ("el2_tmr_complex.cores.mem.mem_export.iccm_bank_wr_data", "mem_export_iccm_bank_wr_data"),
    # ("el2_tmr_complex.cores.mem.mem_export.iccm_bank_wr_ecc", "mem_export_iccm_bank_wr_ecc"),
    # ("el2_tmr_complex.cores.mem.mem_export.dccm_clken", "mem_export_dccm_clken"),
    # ("el2_tmr_complex.cores.mem.mem_export.dccm_wren_bank", "mem_export_dccm_wren_bank"),
    # ("el2_tmr_complex.cores.mem.mem_export.dccm_addr_bank", "mem_export_dccm_addr_bank"),
    # ("el2_tmr_complex.cores.mem.mem_export.dccm_wr_data_bank", "mem_export_dccm_wr_data_bank"),
    # ("el2_tmr_complex.cores.mem.mem_export.dccm_wr_ecc_bank", "mem_export_dccm_wr_ecc_bank"),
    # ("el2_tmr_complex.cores.mem.mem_export.dccm_bank_dout", "mem_export_dccm_bank_dout"),
    # ("el2_tmr_complex.cores.mem.icache_export.clk", "icache_export_clk"),
    # ("el2_tmr_complex.cores.mem.icache_export.ic_b_sb_wren", "icache_export_ic_b_sb_wren"),
    # ("el2_tmr_complex.cores.mem.icache_export.ic_b_sb_bit_en_vec", "icache_export_ic_b_sb_bit_en_vec"),
    # ("el2_tmr_complex.cores.mem.icache_export.ic_sb_wr_data", "icache_export_ic_sb_wr_data"),
    # ("el2_tmr_complex.cores.mem.icache_export.ic_rw_addr_bank_q", "icache_export_ic_rw_addr_bank_q"),
    # ("el2_tmr_complex.cores.mem.icache_export.ic_bank_way_clken_final", "icache_export_ic_bank_way_clken_final"),
    # ("el2_tmr_complex.cores.mem.icache_export.ic_bank_way_clken_final_up", "icache_export_ic_bank_way_clken_final_up"),
    # ("el2_tmr_complex.cores.mem.icache_export.ic_tag_clken_final", "icache_export_ic_tag_clken_final"),
    # ("el2_tmr_complex.cores.mem.icache_export.ic_tag_wren_q", "icache_export_ic_tag_wren_q"),
    # ("el2_tmr_complex.cores.mem.icache_export.ic_tag_wren_biten_vec", "icache_export_ic_tag_wren_biten_vec"),
    # ("el2_tmr_complex.cores.mem.icache_export.ic_tag_wr_data", "icache_export_ic_tag_wr_data"),
    # ("el2_tmr_complex.cores.mem.icache_export.ic_rw_addr_q", "icache_export_ic_rw_addr_q"),
    ("el2_tmr_complex.cores.veer.debug_brkpt_status", "debug_brkpt_status"),
    ("el2_tmr_complex.cores.veer.dec_tlu_perfcnt0", "dec_tlu_perfcnt0"),
    ("el2_tmr_complex.cores.veer.dec_tlu_perfcnt1", "dec_tlu_perfcnt1"),
    ("el2_tmr_complex.cores.veer.dec_tlu_perfcnt2", "dec_tlu_perfcnt2"),
    ("el2_tmr_complex.cores.veer.dec_tlu_perfcnt3", "dec_tlu_perfcnt3"),
    ("el2_tmr_complex.cores.veer.lsu_axi_awvalid", "lsu_axi_awvalid"),
    ("el2_tmr_complex.cores.veer.lsu_axi_awid", "lsu_axi_awid"),
    ("el2_tmr_complex.cores.veer.lsu_axi_awaddr", "lsu_axi_awaddr"),
    ("el2_tmr_complex.cores.veer.lsu_axi_awregion", "lsu_axi_awregion"),
    ("el2_tmr_complex.cores.veer.lsu_axi_awlen", "lsu_axi_awlen"),
    ("el2_tmr_complex.cores.veer.lsu_axi_awsize", "lsu_axi_awsize"),
    ("el2_tmr_complex.cores.veer.lsu_axi_awburst", "lsu_axi_awburst"),
    ("el2_tmr_complex.cores.veer.lsu_axi_awlock", "lsu_axi_awlock"),
    ("el2_tmr_complex.cores.veer.lsu_axi_awcache", "lsu_axi_awcache"),
    ("el2_tmr_complex.cores.veer.lsu_axi_awprot", "lsu_axi_awprot"),
    ("el2_tmr_complex.cores.veer.lsu_axi_awqos", "lsu_axi_awqos"),
    ("el2_tmr_complex.cores.veer.lsu_axi_wvalid", "lsu_axi_wvalid"),
    ("el2_tmr_complex.cores.veer.lsu_axi_wdata", "lsu_axi_wdata"),
    ("el2_tmr_complex.cores.veer.lsu_axi_wstrb", "lsu_axi_wstrb"),
    ("el2_tmr_complex.cores.veer.lsu_axi_wlast", "lsu_axi_wlast"),
    ("el2_tmr_complex.cores.veer.lsu_axi_bready", "lsu_axi_bready"),
    ("el2_tmr_complex.cores.veer.lsu_axi_arvalid", "lsu_axi_arvalid"),
    ("el2_tmr_complex.cores.veer.lsu_axi_arid", "lsu_axi_arid"),
    ("el2_tmr_complex.cores.veer.lsu_axi_araddr", "lsu_axi_araddr"),
    ("el2_tmr_complex.cores.veer.lsu_axi_arregion", "lsu_axi_arregion"),
    ("el2_tmr_complex.cores.veer.lsu_axi_arlen", "lsu_axi_arlen"),
    ("el2_tmr_complex.cores.veer.lsu_axi_arsize", "lsu_axi_arsize"),
    ("el2_tmr_complex.cores.veer.lsu_axi_arburst", "lsu_axi_arburst"),
    ("el2_tmr_complex.cores.veer.lsu_axi_arlock", "lsu_axi_arlock"),
    ("el2_tmr_complex.cores.veer.lsu_axi_arcache", "lsu_axi_arcache"),
    ("el2_tmr_complex.cores.veer.lsu_axi_arprot", "lsu_axi_arprot"),
    ("el2_tmr_complex.cores.veer.lsu_axi_arqos", "lsu_axi_arqos"),
    ("el2_tmr_complex.cores.veer.lsu_axi_rready", "lsu_axi_rready"),
    ("el2_tmr_complex.cores.veer.ifu_axi_awvalid", "ifu_axi_awvalid"),
    ("el2_tmr_complex.cores.veer.ifu_axi_awid", "ifu_axi_awid"),
    ("el2_tmr_complex.cores.veer.ifu_axi_awaddr", "ifu_axi_awaddr"),
    ("el2_tmr_complex.cores.veer.ifu_axi_awregion", "ifu_axi_awregion"),
    ("el2_tmr_complex.cores.veer.ifu_axi_awlen", "ifu_axi_awlen"),
    ("el2_tmr_complex.cores.veer.ifu_axi_awsize", "ifu_axi_awsize"),
    ("el2_tmr_complex.cores.veer.ifu_axi_awburst", "ifu_axi_awburst"),
    ("el2_tmr_complex.cores.veer.ifu_axi_awlock", "ifu_axi_awlock"),
    ("el2_tmr_complex.cores.veer.ifu_axi_awcache", "ifu_axi_awcache"),
    ("el2_tmr_complex.cores.veer.ifu_axi_awprot", "ifu_axi_awprot"),
    ("el2_tmr_complex.cores.veer.ifu_axi_awqos", "ifu_axi_awqos"),
    ("el2_tmr_complex.cores.veer.ifu_axi_wvalid", "ifu_axi_wvalid"),
    ("el2_tmr_complex.cores.veer.ifu_axi_wdata", "ifu_axi_wdata"),
    ("el2_tmr_complex.cores.veer.ifu_axi_wstrb", "ifu_axi_wstrb"),
    ("el2_tmr_complex.cores.veer.ifu_axi_wlast", "ifu_axi_wlast"),
    ("el2_tmr_complex.cores.veer.ifu_axi_bready", "ifu_axi_bready"),
    ("el2_tmr_complex.cores.veer.ifu_axi_arvalid", "ifu_axi_arvalid"),
    ("el2_tmr_complex.cores.veer.ifu_axi_arid", "ifu_axi_arid"),
    ("el2_tmr_complex.cores.veer.ifu_axi_araddr", "ifu_axi_araddr"),
    ("el2_tmr_complex.cores.veer.ifu_axi_arregion", "ifu_axi_arregion"),
    ("el2_tmr_complex.cores.veer.ifu_axi_arlen", "ifu_axi_arlen"),
    ("el2_tmr_complex.cores.veer.ifu_axi_arsize", "ifu_axi_arsize"),
    ("el2_tmr_complex.cores.veer.ifu_axi_arburst", "ifu_axi_arburst"),
    ("el2_tmr_complex.cores.veer.ifu_axi_arlock", "ifu_axi_arlock"),
    ("el2_tmr_complex.cores.veer.ifu_axi_arcache", "ifu_axi_arcache"),
    ("el2_tmr_complex.cores.veer.ifu_axi_arprot", "ifu_axi_arprot"),
    ("el2_tmr_complex.cores.veer.ifu_axi_arqos", "ifu_axi_arqos"),
    ("el2_tmr_complex.cores.veer.ifu_axi_rready", "ifu_axi_rready"),
    ("el2_tmr_complex.cores.veer.sb_axi_awvalid", "sb_axi_awvalid"),
    ("el2_tmr_complex.cores.veer.sb_axi_awid", "sb_axi_awid"),
    ("el2_tmr_complex.cores.veer.sb_axi_awaddr", "sb_axi_awaddr"),
    ("el2_tmr_complex.cores.veer.sb_axi_awregion", "sb_axi_awregion"),
    ("el2_tmr_complex.cores.veer.sb_axi_awlen", "sb_axi_awlen"),
    ("el2_tmr_complex.cores.veer.sb_axi_awsize", "sb_axi_awsize"),
    ("el2_tmr_complex.cores.veer.sb_axi_awburst", "sb_axi_awburst"),
    ("el2_tmr_complex.cores.veer.sb_axi_awlock", "sb_axi_awlock"),
    ("el2_tmr_complex.cores.veer.sb_axi_awcache", "sb_axi_awcache"),
    ("el2_tmr_complex.cores.veer.sb_axi_awprot", "sb_axi_awprot"),
    ("el2_tmr_complex.cores.veer.sb_axi_awqos", "sb_axi_awqos"),
    ("el2_tmr_complex.cores.veer.sb_axi_wvalid", "sb_axi_wvalid"),
    ("el2_tmr_complex.cores.veer.sb_axi_wdata", "sb_axi_wdata"),
    ("el2_tmr_complex.cores.veer.sb_axi_wstrb", "sb_axi_wstrb"),
    ("el2_tmr_complex.cores.veer.sb_axi_wlast", "sb_axi_wlast"),
    ("el2_tmr_complex.cores.veer.sb_axi_bready", "sb_axi_bready"),
    ("el2_tmr_complex.cores.veer.sb_axi_arvalid", "sb_axi_arvalid"),
    ("el2_tmr_complex.cores.veer.sb_axi_arid", "sb_axi_arid"),
    ("el2_tmr_complex.cores.veer.sb_axi_araddr", "sb_axi_araddr"),
    ("el2_tmr_complex.cores.veer.sb_axi_arregion", "sb_axi_arregion"),
    ("el2_tmr_complex.cores.veer.sb_axi_arlen", "sb_axi_arlen"),
    ("el2_tmr_complex.cores.veer.sb_axi_arsize", "sb_axi_arsize"),
    ("el2_tmr_complex.cores.veer.sb_axi_arburst", "sb_axi_arburst"),
    ("el2_tmr_complex.cores.veer.sb_axi_arlock", "sb_axi_arlock"),
    ("el2_tmr_complex.cores.veer.sb_axi_arcache", "sb_axi_arcache"),
    ("el2_tmr_complex.cores.veer.sb_axi_arprot", "sb_axi_arprot"),
    ("el2_tmr_complex.cores.veer.sb_axi_arqos", "sb_axi_arqos"),
    ("el2_tmr_complex.cores.veer.sb_axi_rready", "sb_axi_rready"),
    ("el2_tmr_complex.cores.veer.dma_axi_awready", "dma_axi_awready"),
    ("el2_tmr_complex.cores.veer.dma_axi_wready", "dma_axi_wready"),
    ("el2_tmr_complex.cores.veer.dma_axi_bvalid", "dma_axi_bvalid"),
    ("el2_tmr_complex.cores.veer.dma_axi_bresp", "dma_axi_bresp"),
    ("el2_tmr_complex.cores.veer.dma_axi_bid", "dma_axi_bid"),
    ("el2_tmr_complex.cores.veer.dma_axi_arready", "dma_axi_arready"),
    ("el2_tmr_complex.cores.veer.dma_axi_rvalid", "dma_axi_rvalid"),
    ("el2_tmr_complex.cores.veer.dma_axi_rid", "dma_axi_rid"),
    ("el2_tmr_complex.cores.veer.dma_axi_rdata", "dma_axi_rdata"),
    ("el2_tmr_complex.cores.veer.dma_axi_rresp", "dma_axi_rresp"),
    ("el2_tmr_complex.cores.veer.dma_axi_rlast", "dma_axi_rlast"),
    # TODO: In TMR mode, the AXI to AHB converter is to be placed outside the
    # TMR complex. Remove the signals from el2_tmr_complex.sv
    # ("el2_tmr_complex.cores.veer.haddr", "haddr"),
    # ("el2_tmr_complex.cores.veer.hburst", "hburst"),
    # ("el2_tmr_complex.cores.veer.hmastlock", "hmastlock"),
    # ("el2_tmr_complex.cores.veer.hprot", "hprot"),
    # ("el2_tmr_complex.cores.veer.hsize", "hsize"),
    # ("el2_tmr_complex.cores.veer.htrans", "htrans"),
    # ("el2_tmr_complex.cores.veer.hwrite", "hwrite"),
    # ("el2_tmr_complex.cores.veer.lsu_haddr", "lsu_haddr"),
    # ("el2_tmr_complex.cores.veer.lsu_hburst", "lsu_hburst"),
    # ("el2_tmr_complex.cores.veer.lsu_hmastlock", "lsu_hmastlock"),
    # ("el2_tmr_complex.cores.veer.lsu_hprot", "lsu_hprot"),
    # ("el2_tmr_complex.cores.veer.lsu_hsize", "lsu_hsize"),
    # ("el2_tmr_complex.cores.veer.lsu_htrans", "lsu_htrans"),
    # ("el2_tmr_complex.cores.veer.lsu_hwrite", "lsu_hwrite"),
    # ("el2_tmr_complex.cores.veer.lsu_hwdata", "lsu_hwdata"),
    # ("el2_tmr_complex.cores.veer.sb_haddr", "sb_haddr"),
    # ("el2_tmr_complex.cores.veer.sb_hburst", "sb_hburst"),
    # ("el2_tmr_complex.cores.veer.sb_hmastlock", "sb_hmastlock"),
    # ("el2_tmr_complex.cores.veer.sb_hprot", "sb_hprot"),
    # ("el2_tmr_complex.cores.veer.sb_hsize", "sb_hsize"),
    # ("el2_tmr_complex.cores.veer.sb_htrans", "sb_htrans"),
    # ("el2_tmr_complex.cores.veer.sb_hwrite", "sb_hwrite"),
    # ("el2_tmr_complex.cores.veer.sb_hwdata", "sb_hwdata"),
    # ("el2_tmr_complex.cores.veer.dma_hrdata", "dma_hrdata"),
    # ("el2_tmr_complex.cores.veer.dma_hreadyout", "dma_hreadyout"),
    # ("el2_tmr_complex.cores.veer.dma_hresp", "dma_hresp"),
    ("el2_tmr_complex.cores.veer.dmi_reg_rdata", "dmi_reg_rdata"),
    ("el2_tmr_complex.cores.veer.iccm_ecc_single_error", "iccm_ecc_single_error"),
    ("el2_tmr_complex.cores.veer.iccm_ecc_double_error", "iccm_ecc_double_error"),
    ("el2_tmr_complex.cores.veer.dccm_ecc_single_error", "dccm_ecc_single_error"),
    ("el2_tmr_complex.cores.veer.dccm_ecc_double_error", "dccm_ecc_double_error"),
)

# ==============================================================================


class DriverItem(uvm_sequence_item):
    def __init__(self, name="DriverItem"):
        super().__init__(name)
        self.inhibit = 0
        self.signals = []


class MonitorItem(uvm_sequence_item):
    def __init__(self, name="MonitorItem"):
        super().__init__(name)
        self.inhibit = 0
        self.driver = None
        self.sink = None

    def __str__(self):
        return f"{self.get_name()}: inh={self.inhibit}, {self.driver} -> {self.sink}"


# ==============================================================================


class Driver(uvm_driver):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

    def set_inhibit(self, value):
        value = MuBiTrue if value else MuBiFalse
        cocotb.top.el2_tmr_complex.tmr_output_inhibit = Force(value)

    async def run_phase(self):
        while True:
            it = await self.seq_item_port.get_next_item()
            assert isinstance(it, DriverItem)

            # Drive inhibit
            self.set_inhibit(it.inhibit)
            await Timer(10, "ns")

            # Drive the signal(s). The signals come from inside the TMR complex
            # so they are majority voted. Drive the same value to all 3 of
            # them.
            nbits = len(it.signals[0])
            value = random.randrange(1, 1 << nbits)
            for s in it.signals:
                s.value = Force(value)
            await Timer(10, "ns")

            # Release the signal
            for s in it.signals:
                s.value = Release()
            await Timer(10, "ns")

            self.seq_item_port.item_done()


class Monitor(uvm_monitor):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)

    def sample_inhibit(self):
        # TODO: Replace with the signal coming out of the recovery FSM once its
        # integrated
        value = cocotb.top.el2_tmr_complex.axi_output_inhibit.value

        if value == MuBiTrue:
            return True
        if value == MuBiFalse:
            return False

        return None

    async def run_phase(self):
        env = ConfigDB().get(None, "", "env")

        # Make a trigger list
        triggers = []
        for src_signals, dst_signal in env.signals:
            triggers.append(Edge(dst_signal))

        # Monitor
        while True:

            # Wait for any change
            trig = await First(*triggers)
            indx = triggers.index(trig)

            src, dst = env.signals[indx]

            # Sample
            item = MonitorItem(dst._path)
            item.inhibit = self.sample_inhibit()
            item.driver = [s.value for s in src]
            item.sink = dst.value

            self.logger.debug(f"{dst._path}: inh={item.inhibit}, {item.driver} -> {item.sink}")
            self.ap.write(item)


class Scoreboard(uvm_component):

    def build_phase(self):
        self.passed = False

        self.fifo = uvm_tlm_analysis_fifo("fifo", self)
        self.port = uvm_get_port("port", self)

    def connect_phase(self):
        self.port.connect(self.fifo.get_export)

    def check_phase(self):
        self.passed = True
        while self.port.can_get():
            _, item = self.port.try_get()

            # Inhibit asserted, the output should be 0
            if item.inhibit:
                if item.sink != 0:
                    self.logger.error(str(item))
                    self.logger.error("Output signal is not 0 while inhibit is asserted")
                    self.passed = False

            # Inhibit deasserted, signals should match
            else:
                for i, drv in enumerate(item.driver):
                    if drv != item.sink:
                        self.logger.error(str(item))
                        self.logger.error(f"Output signal does not match input signal {i}")
                        self.passed = False

    def final_phase(self):
        if not self.passed:
            self.logger.critical("{} reports a failure".format(type(self)))
            assert False


# ==============================================================================


class BaseEnv(uvm_env):
    """
    Base PyUVM test environment
    """

    def __init__(self, name, parent):
        super().__init__(name, parent)
        self.signals = []

    def build_phase(self):
        self.driver = Driver("driver", self)
        self.seqr = uvm_sequencer("seqr", self)
        self.monitor = Monitor("monitor", self)
        self.scoreboard = Scoreboard("scoreboard", self)

        # Collect gated signal pairs
        for src_name, dst_name in SIGNALS:
            error = False

            # Find sink
            try:
                dst_obj = getattr(cocotb.top, dst_name)
            except AttributeError:
                self.logger.error(f"Signal {dst_name} not found!")
                error = True

            # Find sources
            parts = src_name.split(".")
            src_obj = []
            for i in range(3):
                name = [p + f"[{i}]" if p == "cores" else p for p in parts]
                name = ".".join(name)
                try:
                    src_obj.append(getattr(cocotb.top, name))
                except AttributeError:
                    self.logger.error(f"Signal {name} not found!")
                    error = True

            if error:
                continue

            # Store objects
            self.signals.append(
                (
                    src_obj,
                    dst_obj,
                )
            )

        self.logger.info(f"{len(self.signals)}/{len(SIGNALS)} signals found")
        if len(self.signals) != len(SIGNALS):
            self.logger.error("Not all TMR signals are found in DUT")
            assert False

    def connect_phase(self):
        self.driver.seq_item_port.connect(self.seqr.seq_item_export)
        if self.scoreboard:
            self.monitor.ap.connect(self.scoreboard.fifo.analysis_export)


# ==============================================================================


class BaseTest(uvm_test):
    """
    Base test for the module
    """

    def __init__(self, name, parent, env_class=BaseEnv):
        super().__init__(name, parent)
        self.env_class = env_class

        # Synchronize pyuvm logging level with cocotb logging level. Unclear
        # why it does not happen automatically.
        level = logging.getLevelName(os.environ.get("COCOTB_LOG_LEVEL", "INFO"))
        uvm_report_object.set_default_logging_level(level)

    def build_phase(self):
        self.env = self.env_class("env", self)
        ConfigDB().set(None, "*", "env", self.env)

    async def run_phase(self):
        self.raise_objection()

        # Initialize signals
        for name in INPUTS:
            obj = getattr(cocotb.top, name)
            obj.value = 0

        cocotb.top.clk.value = 0
        cocotb.top.rst_l.value = 1
        cocotb.top.dbg_rst_l.value = 1

        # Pulse the reset
        await Timer(10, "ns")
        cocotb.top.rst_l.value = 0
        await Timer(10, "ns")
        cocotb.top.rst_l.value = 1
        await Timer(10, "ns")

        # Run the actual test
        await self.run()

        self.drop_objection()

    async def run(self):
        raise NotImplementedError()
