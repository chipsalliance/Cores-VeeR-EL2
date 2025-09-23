`ifndef VERILATOR

interface el2_veer_lockstep_cov_if
  import el2_mubi_pkg::*;
  import el2_lockstep_pkg::*;
#(
    `include "el2_param.vh"
) (
    input logic        clk,
    input logic        rst_n,
`ifdef RV_LOCKSTEP_REGFILE_ENABLE
    input logic        regfile_corrupted,
`endif
    input logic        outputs_corrupted,
    input el2_mubi_t   corruption_detected_o,
    input el2_mubi_t   lockstep_err_injection_en_i,
    input el2_mubi_t   disable_corruption_detection_i,
    input veer_outputs_t delayed_main_core_outputs,
    input veer_outputs_t shadow_core_outputs
);

    covergroup el2_veer_lockstep_error_source @(posedge clk iff rst_n);
        `ifdef RV_LOCKSTEP_REGFILE_ENABLE
        regfile_corruption_detected_cp: coverpoint regfile_corrupted &
            mubi_check_true(corruption_detected_o);
        `endif
        output_corruption_detected_cp: coverpoint outputs_corrupted &
            mubi_check_true(corruption_detected_o);
        inject_error_cp: coverpoint mubi_check_true(lockstep_err_injection_en_i) &
            mubi_check_true(corruption_detected_o);
        invalid_inject_detected_cp: coverpoint mubi_check_invalid(lockstep_err_injection_en_i) &
            mubi_check_true(corruption_detected_o);
        invalid_disable_detected_cp: coverpoint mubi_check_invalid(disable_corruption_detection_i) &
            mubi_check_true(corruption_detected_o);
    endgroup

    covergroup el2_veer_lockstep_error_disable @(posedge clk iff
        (rst_n & mubi_check_true(disable_corruption_detection_i)));
        `ifdef RV_LOCKSTEP_REGFILE_ENABLE
        regfile_corruption_disabled_cp: coverpoint regfile_corrupted &
            mubi_check_false(corruption_detected_o);
        `endif
        output_corruption_disabled_cp: coverpoint outputs_corrupted &
            mubi_check_false(corruption_detected_o);
        inject_error_disabled_cp: coverpoint mubi_check_true(lockstep_err_injection_en_i) &
            mubi_check_false(corruption_detected_o);
        invalid_inject_disabled_cp: coverpoint mubi_check_invalid(lockstep_err_injection_en_i) &
            mubi_check_false(corruption_detected_o);
    endgroup

`define SINGLE_BIN_FOR(name) name: coverpoint \
    delayed_main_core_outputs.name ^ shadow_core_outputs.name {bins diff = {[1:$]};}

    // ICCM
    covergroup el2_veer_lockstep_iccm_differ @(posedge clk iff rst_n);
        `SINGLE_BIN_FOR(icm_clk_override)
        `SINGLE_BIN_FOR(iccm_rw_addr)
        `SINGLE_BIN_FOR(iccm_wren)
        `SINGLE_BIN_FOR(iccm_rden)
        `SINGLE_BIN_FOR(iccm_wr_size)
        `SINGLE_BIN_FOR(iccm_wr_data)
        `SINGLE_BIN_FOR(iccm_buf_correct_ecc)
        `SINGLE_BIN_FOR(iccm_correction_state)
        `SINGLE_BIN_FOR(iccm_ecc_single_error)
        `SINGLE_BIN_FOR(iccm_ecc_double_error)
    endgroup

    // DCCM
    covergroup el2_veer_lockstep_dccm_differ @(posedge clk iff rst_n);
        `SINGLE_BIN_FOR(dccm_wren)
        `SINGLE_BIN_FOR(dccm_rden)
        `SINGLE_BIN_FOR(dccm_clk_override)
        `SINGLE_BIN_FOR(dccm_wr_addr_lo)
        `SINGLE_BIN_FOR(dccm_wr_addr_hi)
        `SINGLE_BIN_FOR(dccm_rd_addr_lo)
        `SINGLE_BIN_FOR(dccm_rd_addr_hi)
        `SINGLE_BIN_FOR(dccm_wr_data_lo)
        `SINGLE_BIN_FOR(dccm_wr_data_hi)
        `SINGLE_BIN_FOR(dccm_ecc_single_error)
        `SINGLE_BIN_FOR(dccm_ecc_double_error)
    endgroup

    // Trace
    covergroup el2_veer_lockstep_trace_differ  @(posedge clk iff rst_n);
        `SINGLE_BIN_FOR(trace_rv_i_insn_ip)
        `SINGLE_BIN_FOR(trace_rv_i_address_ip)
        `SINGLE_BIN_FOR(trace_rv_i_valid_ip)
        `SINGLE_BIN_FOR(trace_rv_i_exception_ip)
        `SINGLE_BIN_FOR(trace_rv_i_ecause_ip)
        `SINGLE_BIN_FOR(trace_rv_i_interrupt_ip)
        `SINGLE_BIN_FOR(trace_rv_i_tval_ip)
    endgroup

    // LSU
    covergroup el2_veer_lockstep_lsu_differ  @(posedge clk iff rst_n);
    `ifdef RV_BUILD_AXI4
        `SINGLE_BIN_FOR(lsu_axi_awvalid)
        `SINGLE_BIN_FOR(lsu_axi_awid)
        `SINGLE_BIN_FOR(lsu_axi_awaddr)
        `SINGLE_BIN_FOR(lsu_axi_awregion)
        `SINGLE_BIN_FOR(lsu_axi_awlen)
        `SINGLE_BIN_FOR(lsu_axi_awsize)
        `SINGLE_BIN_FOR(lsu_axi_awburst)
        `SINGLE_BIN_FOR(lsu_axi_awlock)
        `SINGLE_BIN_FOR(lsu_axi_awcache)
        `SINGLE_BIN_FOR(lsu_axi_awprot)
        `SINGLE_BIN_FOR(lsu_axi_awqos)
        `SINGLE_BIN_FOR(lsu_axi_wvalid)
        `SINGLE_BIN_FOR(lsu_axi_wdata)
        `SINGLE_BIN_FOR(lsu_axi_wstrb)
        `SINGLE_BIN_FOR(lsu_axi_wlast)
        `SINGLE_BIN_FOR(lsu_axi_bready)
        `SINGLE_BIN_FOR(lsu_axi_arvalid)
        `SINGLE_BIN_FOR(lsu_axi_arid)
        `SINGLE_BIN_FOR(lsu_axi_araddr)
        `SINGLE_BIN_FOR(lsu_axi_arregion)
        `SINGLE_BIN_FOR(lsu_axi_arlen)
        `SINGLE_BIN_FOR(lsu_axi_arsize)
        `SINGLE_BIN_FOR(lsu_axi_arburst)
        `SINGLE_BIN_FOR(lsu_axi_arlock)
        `SINGLE_BIN_FOR(lsu_axi_arcache)
        `SINGLE_BIN_FOR(lsu_axi_arprot)
        `SINGLE_BIN_FOR(lsu_axi_arqos)
        `SINGLE_BIN_FOR(lsu_axi_rready)
    `endif

    `ifdef RV_BUILD_AHB_LITE
        `SINGLE_BIN_FOR(lsu_haddr)
        `SINGLE_BIN_FOR(lsu_hburst)
        `SINGLE_BIN_FOR(lsu_hmastlock)
        `SINGLE_BIN_FOR(lsu_hprot)
        `SINGLE_BIN_FOR(lsu_hsize)
        `SINGLE_BIN_FOR(lsu_htrans)
        `SINGLE_BIN_FOR(lsu_hwrite)
    `endif
    endgroup

    // IFU
    covergroup el2_veer_lockstep_ifu_differ  @(posedge clk iff rst_n);
    `ifdef RV_BUILD_AXI4
        `SINGLE_BIN_FOR(ifu_axi_awvalid)
        `SINGLE_BIN_FOR(ifu_axi_awid)
        `SINGLE_BIN_FOR(ifu_axi_awaddr)
        `SINGLE_BIN_FOR(ifu_axi_awregion)
        `SINGLE_BIN_FOR(ifu_axi_awlen)
        `SINGLE_BIN_FOR(ifu_axi_awsize)
        `SINGLE_BIN_FOR(ifu_axi_awburst)
        `SINGLE_BIN_FOR(ifu_axi_awlock)
        `SINGLE_BIN_FOR(ifu_axi_awcache)
        `SINGLE_BIN_FOR(ifu_axi_awprot)
        `SINGLE_BIN_FOR(ifu_axi_awqos)
        `SINGLE_BIN_FOR(ifu_axi_wvalid)
        `SINGLE_BIN_FOR(ifu_axi_wdata)
        `SINGLE_BIN_FOR(ifu_axi_wstrb)
        `SINGLE_BIN_FOR(ifu_axi_wlast)
        `SINGLE_BIN_FOR(ifu_axi_bready)
        `SINGLE_BIN_FOR(ifu_axi_arvalid)
        `SINGLE_BIN_FOR(ifu_axi_arid)
        `SINGLE_BIN_FOR(ifu_axi_araddr)
        `SINGLE_BIN_FOR(ifu_axi_arregion)
        `SINGLE_BIN_FOR(ifu_axi_arlen)
        `SINGLE_BIN_FOR(ifu_axi_arsize)
        `SINGLE_BIN_FOR(ifu_axi_arburst)
        `SINGLE_BIN_FOR(ifu_axi_arlock)
        `SINGLE_BIN_FOR(ifu_axi_arcache)
        `SINGLE_BIN_FOR(ifu_axi_arprot)
        `SINGLE_BIN_FOR(ifu_axi_arqos)
        `SINGLE_BIN_FOR(ifu_axi_rready)
    `endif

    `ifdef RV_BUILD_AHB_LITE
        `SINGLE_BIN_FOR(haddr)
        `SINGLE_BIN_FOR(hburst)
        `SINGLE_BIN_FOR(hmastlock)
        `SINGLE_BIN_FOR(hprot)
        `SINGLE_BIN_FOR(hsize)
        `SINGLE_BIN_FOR(htrans)
        `SINGLE_BIN_FOR(hwrite)
    `endif
    endgroup

    // DMA
    covergroup el2_veer_lockstep_dma_differ  @(posedge clk iff rst_n);
    `ifdef RV_BUILD_AXI4
        `SINGLE_BIN_FOR(dma_axi_awready)
        `SINGLE_BIN_FOR(dma_axi_wready)
        `SINGLE_BIN_FOR(dma_axi_bvalid)
        `SINGLE_BIN_FOR(dma_axi_bresp)
        `SINGLE_BIN_FOR(dma_axi_bid)
        `SINGLE_BIN_FOR(dma_axi_arready)
        `SINGLE_BIN_FOR(dma_axi_rvalid)
        `SINGLE_BIN_FOR(dma_axi_rid)
        `SINGLE_BIN_FOR(dma_axi_rdata)
        `SINGLE_BIN_FOR(dma_axi_rresp)
        `SINGLE_BIN_FOR(dma_axi_rlast)
    `endif

    `ifdef RV_BUILD_AHB_LITE
        `SINGLE_BIN_FOR(dma_hrdata)
        `SINGLE_BIN_FOR(dma_hreadyout)
        `SINGLE_BIN_FOR(dma_hresp)
    `endif
    endgroup

    // Debug SB
    covergroup el2_veer_lockstep_sb_differ  @(posedge clk iff rst_n);
    `ifdef RV_BUILD_AXI4
        `SINGLE_BIN_FOR(sb_axi_awvalid)
        `SINGLE_BIN_FOR(sb_axi_awid)
        `SINGLE_BIN_FOR(sb_axi_awaddr)
        `SINGLE_BIN_FOR(sb_axi_awregion)
        `SINGLE_BIN_FOR(sb_axi_awlen)
        `SINGLE_BIN_FOR(sb_axi_awsize)
        `SINGLE_BIN_FOR(sb_axi_awburst)
        `SINGLE_BIN_FOR(sb_axi_awlock)
        `SINGLE_BIN_FOR(sb_axi_awcache)
        `SINGLE_BIN_FOR(sb_axi_awprot)
        `SINGLE_BIN_FOR(sb_axi_awqos)
        `SINGLE_BIN_FOR(sb_axi_wvalid)
        `SINGLE_BIN_FOR(sb_axi_wdata)
        `SINGLE_BIN_FOR(sb_axi_wstrb)
        `SINGLE_BIN_FOR(sb_axi_wlast)
        `SINGLE_BIN_FOR(sb_axi_bready)
        `SINGLE_BIN_FOR(sb_axi_arvalid)
        `SINGLE_BIN_FOR(sb_axi_arid)
        `SINGLE_BIN_FOR(sb_axi_araddr)
        `SINGLE_BIN_FOR(sb_axi_arregion)
        `SINGLE_BIN_FOR(sb_axi_arlen)
        `SINGLE_BIN_FOR(sb_axi_arsize)
        `SINGLE_BIN_FOR(sb_axi_arburst)
        `SINGLE_BIN_FOR(sb_axi_arlock)
        `SINGLE_BIN_FOR(sb_axi_arcache)
        `SINGLE_BIN_FOR(sb_axi_arprot)
        `SINGLE_BIN_FOR(sb_axi_arqos)
        `SINGLE_BIN_FOR(sb_axi_rready)
    `endif

    `ifdef RV_BUILD_AHB_LITE
        `SINGLE_BIN_FOR(sb_haddr)
        `SINGLE_BIN_FOR(sb_hburst)
        `SINGLE_BIN_FOR(sb_hmastlock)
        `SINGLE_BIN_FOR(sb_hprot)
        `SINGLE_BIN_FOR(sb_hsize)
        `SINGLE_BIN_FOR(sb_htrans)
        `SINGLE_BIN_FOR(sb_hwrite)
    `endif
    endgroup

    // Instruction Cache
    covergroup el2_veer_lockstep_ic_differ @(posedge clk iff rst_n);
        `SINGLE_BIN_FOR(ic_rw_addr)
        `SINGLE_BIN_FOR(ic_tag_valid)
        `SINGLE_BIN_FOR(ic_wr_en)
        `SINGLE_BIN_FOR(ic_rd_en)
        `SINGLE_BIN_FOR(ic_wr_data)
        `SINGLE_BIN_FOR(ic_debug_wr_data)
        `SINGLE_BIN_FOR(ic_premux_data)
        `SINGLE_BIN_FOR(ic_sel_premux_data)
        `SINGLE_BIN_FOR(ic_debug_addr)
        `SINGLE_BIN_FOR(ic_debug_rd_en)
        `SINGLE_BIN_FOR(ic_debug_wr_en)
        `SINGLE_BIN_FOR(ic_debug_tag_array)
        `SINGLE_BIN_FOR(ic_debug_way)
    endgroup

    // Miscellaneous outputs
    covergroup el2_veer_lockstep_miscellaneous_differ @(posedge clk iff rst_n);
        `SINGLE_BIN_FOR(core_rst_l)
        `SINGLE_BIN_FOR(dec_tlu_core_ecc_disable)
        `SINGLE_BIN_FOR(o_cpu_halt_ack)
        `SINGLE_BIN_FOR(o_cpu_halt_status)
        `SINGLE_BIN_FOR(o_cpu_run_ack)
        `SINGLE_BIN_FOR(o_debug_mode_status)
        `SINGLE_BIN_FOR(mpc_debug_halt_ack)
        `SINGLE_BIN_FOR(mpc_debug_run_ack)
        `SINGLE_BIN_FOR(debug_brkpt_status)
        `SINGLE_BIN_FOR(dec_tlu_perfcnt0)
        `SINGLE_BIN_FOR(dec_tlu_perfcnt1)
        `SINGLE_BIN_FOR(dec_tlu_perfcnt2)
        `SINGLE_BIN_FOR(dec_tlu_perfcnt3)
        `SINGLE_BIN_FOR(dmi_reg_rdata)
    endgroup

    el2_veer_lockstep_error_source el2_veer_lockstep_error_source_cg = new();
    el2_veer_lockstep_error_disable el2_veer_lockstep_error_disable_cg = new();
    el2_veer_lockstep_trace_differ el2_veer_lockstep_trace_differ_cg = new();
    el2_veer_lockstep_lsu_differ el2_veer_lockstep_lsu_differ_cg = new();
    el2_veer_lockstep_ifu_differ el2_veer_lockstep_ifu_differ_cg = new();
    el2_veer_lockstep_dma_differ el2_veer_lockstep_dma_differ_cg = new();
    el2_veer_lockstep_sb_differ el2_veer_lockstep_sb_differ_cg = new();
    el2_veer_lockstep_ic_differ el2_veer_lockstep_ic_differ_cg = new();
    el2_veer_lockstep_miscellaneous_differ el2_veer_lockstep_miscellaneous_differ_cg = new();

endinterface

`endif
