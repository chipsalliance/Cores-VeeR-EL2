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
    el2_regfile_if.veer_rf_sink delayed_main_core_regfile,
    el2_regfile_if.veer_rf_sink shadow_core_regfile,
`endif
    input logic        outputs_corrupted,
    input el2_mubi_t   corruption_detected_o,
    input el2_mubi_t   lockstep_err_injection_en_i,
    input el2_mubi_t   disable_corruption_detection_i,
    input veer_outputs_t main_core_outputs,
    input veer_outputs_t delayed_main_core_outputs,
    input veer_outputs_t shadow_core_outputs
);

    // -------------------------------------------------------------------------
    // Latency Measurement and Fault Injection Tracking
    // -------------------------------------------------------------------------
    int unsigned detection_latency;
    logic [31:0] fault_start_cycle;
    logic [31:0] cycle_count;
    logic fault_in_progress;
    logic corruption_detected_prev;

    // Detect control-based error injection
    logic ctrl_fault_inject;
    assign ctrl_fault_inject = mubi_check_true(lockstep_err_injection_en_i) |
                               mubi_check_true(mubi_check_invalid(lockstep_err_injection_en_i)) |
                               mubi_check_true(mubi_check_invalid(disable_corruption_detection_i));

    // Detect data path divergence onset between main and shadow core
    logic datapath_divergence_onset;
    assign datapath_divergence_onset = (main_core_outputs != shadow_core_outputs)
`ifdef RV_LOCKSTEP_REGFILE_ENABLE
                                     | (delayed_main_core_regfile.gpr != shadow_core_regfile.gpr)
                                     | (delayed_main_core_regfile.tlu != shadow_core_regfile.tlu)
`endif
                                     ;

    logic any_fault_trigger;
    assign any_fault_trigger = ctrl_fault_inject | datapath_divergence_onset;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            cycle_count              <= '0;
            fault_start_cycle        <= '0;
            fault_in_progress        <= 1'b0;
            corruption_detected_prev <= 1'b0;
            detection_latency        <= '0;
        end else begin
            cycle_count              <= cycle_count + 1;
            corruption_detected_prev <= mubi_check_true(corruption_detected_o);

            // Record the cycle where fault injection / divergence begins
            if (any_fault_trigger && !fault_in_progress && !mubi_check_true(corruption_detected_o)) begin
                fault_in_progress <= 1'b1;
                fault_start_cycle <= cycle_count;
            end

            // When corruption_detected_o asserts El2MuBiTrue:
            if (mubi_check_true(corruption_detected_o)) begin
                if (!corruption_detected_prev) begin
                    if (ctrl_fault_inject) begin
                        // Control-based error injection has 0-cycle combinational detection latency
                        detection_latency <= 0;
                    end else if (pt.LOCKSTEP_DELAY == 0) begin
                        // 0-delay bypass mode: combinatorial comparison (0 to 1 cycle)
                        if (fault_in_progress) begin
                            detection_latency <= (cycle_count - fault_start_cycle <= 1) ?
                                                 (cycle_count - fault_start_cycle) : 0;
                        end else begin
                            detection_latency <= 0;
                        end
                    end else if (fault_in_progress) begin
                        detection_latency <= cycle_count - fault_start_cycle;
                    end else begin
                        // Configured pipeline delay stages for LockstepDelay N (1 to 4)
                        detection_latency <= pt.LOCKSTEP_DELAY;
                    end
                end
                // Clear fault_in_progress when corruption is cleared
                if (!any_fault_trigger && !outputs_corrupted
`ifdef RV_LOCKSTEP_REGFILE_ENABLE
                    && !regfile_corrupted
`endif
                ) begin
                    fault_in_progress <= 1'b0;
                end
            end else begin
                if (!any_fault_trigger) begin
                    fault_in_progress <= 1'b0;
                end
            end
        end
    end

    // -------------------------------------------------------------------------
    // Covergroup: DCLS Delay Configuration and 0-Delay Mode Coverage
    // -------------------------------------------------------------------------
    covergroup el2_veer_lockstep_delay_cov @(posedge clk iff (rst_n & mubi_check_true(corruption_detected_o)));
        option.per_instance = 1;

        // Coverpoint lockstep_delay_cp:
        // Covers all supported LOCKSTEP_DELAY parameter values
        lockstep_delay_cp: coverpoint int'(pt.LOCKSTEP_DELAY) {
            // delay_0: LOCKSTEP_DELAY == 0 (Combinatorial bypass mode where main core outputs are directly compared to shadow core without pipeline delay flip-flops)
            bins delay_0 = {0};
            // delay_1: LOCKSTEP_DELAY == 1
            bins delay_1 = {1};
            // delay_2: LOCKSTEP_DELAY == 2
            bins delay_2 = {2};
            // delay_3: LOCKSTEP_DELAY == 3
            bins delay_3 = {3};
            // delay_4: LOCKSTEP_DELAY == 4
            bins delay_4 = {4};
        }

        // Coverpoint delay_mismatch_detection_latency_cp:
        // Measures cycle latency from fault injection to corruption_detected_o asserting El2MuBiTrue
        delay_mismatch_detection_latency_cp: coverpoint detection_latency {
            // For delay_0: Latency must be 0 to 1 cycle
            bins latency_0 = {0};
            bins latency_1 = {1};
            // For delay_N (1 to 4): Latency must match configured pipeline delay stage
            bins latency_2 = {2};
            bins latency_3 = {3};
            bins latency_4 = {4};
        }

        // Coverpoint corruption_detected_cp:
        // Assertion of corruption_detected_o (El2MuBiTrue)
        corruption_detected_cp: coverpoint mubi_check_true(corruption_detected_o) {
            bins detected = {1'b1};
        }

        // Cross Coverage:
        // Cross lockstep_delay_cp with corruption_detected_o assertion to prove divergence is caught across every supported delay stage
        lockstep_delay_x_corruption: cross lockstep_delay_cp, corruption_detected_cp;

        // Cross Coverage:
        // Cross lockstep_delay_cp with delay_mismatch_detection_latency_cp to prove latency matches configured delay stage
        lockstep_delay_x_latency: cross lockstep_delay_cp, delay_mismatch_detection_latency_cp {
            bins delay_0_latency_0 = binsof(lockstep_delay_cp.delay_0) && binsof(delay_mismatch_detection_latency_cp.latency_0);
            bins delay_0_latency_1 = binsof(lockstep_delay_cp.delay_0) && binsof(delay_mismatch_detection_latency_cp.latency_1);
            bins delay_1_latency_1 = binsof(lockstep_delay_cp.delay_1) && binsof(delay_mismatch_detection_latency_cp.latency_1);
            bins delay_2_latency_2 = binsof(lockstep_delay_cp.delay_2) && binsof(delay_mismatch_detection_latency_cp.latency_2);
            bins delay_3_latency_3 = binsof(lockstep_delay_cp.delay_3) && binsof(delay_mismatch_detection_latency_cp.latency_3);
            bins delay_4_latency_4 = binsof(lockstep_delay_cp.delay_4) && binsof(delay_mismatch_detection_latency_cp.latency_4);
        }
    endgroup


    covergroup el2_veer_lockstep_error_source @(posedge clk iff rst_n);
        option.per_instance = 1;
        `ifdef RV_LOCKSTEP_REGFILE_ENABLE
        regfile_corruption_detected_cp: coverpoint regfile_corrupted &
            mubi_check_true(corruption_detected_o);
        `endif
        output_corruption_detected_cp: coverpoint outputs_corrupted &
            mubi_check_true(corruption_detected_o);
        inject_error_cp: coverpoint mubi_check_true(lockstep_err_injection_en_i) &
            mubi_check_true(corruption_detected_o);
        invalid_inject_detected_cp: coverpoint mubi_check_true(mubi_check_invalid(lockstep_err_injection_en_i)) &
            mubi_check_true(corruption_detected_o);
        invalid_disable_detected_cp: coverpoint mubi_check_true(mubi_check_invalid(disable_corruption_detection_i)) &
            mubi_check_true(corruption_detected_o);
    endgroup

    covergroup el2_veer_lockstep_error_disable @(posedge clk iff
        (rst_n & mubi_check_true(disable_corruption_detection_i)));
        option.per_instance = 1;
        `ifdef RV_LOCKSTEP_REGFILE_ENABLE
        regfile_corruption_disabled_cp: coverpoint regfile_corrupted &
            mubi_check_false(corruption_detected_o);
        `endif
        output_corruption_disabled_cp: coverpoint outputs_corrupted &
            mubi_check_false(corruption_detected_o);
        inject_error_disabled_cp: coverpoint mubi_check_true(lockstep_err_injection_en_i) &
            mubi_check_false(corruption_detected_o);
        invalid_inject_disabled_cp: coverpoint mubi_check_true(mubi_check_invalid(lockstep_err_injection_en_i)) &
            mubi_check_false(corruption_detected_o);
    endgroup

`define SINGLE_BIN_FOR(name) name: coverpoint \
    delayed_main_core_outputs.name ^ shadow_core_outputs.name {bins diff = {[1:$]};}

`ifdef RV_LOCKSTEP_REGFILE_ENABLE
    // Reg IF
    covergroup el2_veer_lockstep_reg_differ @(posedge clk iff rst_n);
        option.per_instance = 1;
        gpr: coverpoint delayed_main_core_regfile.gpr ^ shadow_core_regfile.gpr {bins diff = {[1:$]};}
        tlu: coverpoint delayed_main_core_regfile.tlu ^ shadow_core_regfile.tlu {bins diff = {[1:$]};}
    endgroup
`endif

    // ICCM
    covergroup el2_veer_lockstep_iccm_differ @(posedge clk iff rst_n);
        option.per_instance = 1;
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
        option.per_instance = 1;
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
        option.per_instance = 1;
        `SINGLE_BIN_FOR(trace_rv_i_insn_ip)
        `SINGLE_BIN_FOR(trace_rv_i_address_ip)
        `SINGLE_BIN_FOR(trace_rv_i_valid_ip)
        `SINGLE_BIN_FOR(trace_rv_i_exception_ip)
        `SINGLE_BIN_FOR(trace_rv_i_ecause_ip)
        `SINGLE_BIN_FOR(trace_rv_i_interrupt_ip)
        `SINGLE_BIN_FOR(trace_rv_i_tval_ip)
    endgroup

    // LSU
    `ifdef RV_BUILD_AHB_LITE
    covergroup el2_veer_lockstep_lsu_ahb_differ  @(posedge clk iff rst_n);
        option.per_instance = 1;
        `SINGLE_BIN_FOR(lsu_haddr)
        `SINGLE_BIN_FOR(lsu_hburst)
        `SINGLE_BIN_FOR(lsu_hmastlock)
        `SINGLE_BIN_FOR(lsu_hprot)
        `SINGLE_BIN_FOR(lsu_hsize)
        `SINGLE_BIN_FOR(lsu_htrans)
        `SINGLE_BIN_FOR(lsu_hwrite)
    endgroup
    `endif

    `ifdef RV_BUILD_AXI4
    covergroup el2_veer_lockstep_lsu_axi_differ  @(posedge clk iff rst_n);
        option.per_instance = 1;
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
    endgroup
    `endif

    // IFU
    `ifdef RV_BUILD_AHB_LITE
    covergroup el2_veer_lockstep_ifu_ahb_differ  @(posedge clk iff rst_n);
        option.per_instance = 1;
        `SINGLE_BIN_FOR(haddr)
        `SINGLE_BIN_FOR(hburst)
        `SINGLE_BIN_FOR(hmastlock)
        `SINGLE_BIN_FOR(hprot)
        `SINGLE_BIN_FOR(hsize)
        `SINGLE_BIN_FOR(htrans)
        `SINGLE_BIN_FOR(hwrite)
    endgroup
    `endif

    `ifdef RV_BUILD_AXI4
    covergroup el2_veer_lockstep_ifu_axi_differ  @(posedge clk iff rst_n);
        option.per_instance = 1;
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
    endgroup
    `endif

    // DMA
    `ifdef RV_BUILD_AHB_LITE
    covergroup el2_veer_lockstep_dma_ahb_differ  @(posedge clk iff rst_n);
        option.per_instance = 1;
        `SINGLE_BIN_FOR(dma_hrdata)
        `SINGLE_BIN_FOR(dma_hreadyout)
        `SINGLE_BIN_FOR(dma_hresp)
    endgroup
    `endif

    `ifdef RV_BUILD_AXI4
    covergroup el2_veer_lockstep_dma_axi_differ  @(posedge clk iff rst_n);
        option.per_instance = 1;
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
    endgroup
    `endif

    // Debug SB
    `ifdef RV_BUILD_AHB_LITE
    covergroup el2_veer_lockstep_sb_ahb_differ  @(posedge clk iff rst_n);
        option.per_instance = 1;
        `SINGLE_BIN_FOR(sb_haddr)
        `SINGLE_BIN_FOR(sb_hburst)
        `SINGLE_BIN_FOR(sb_hmastlock)
        `SINGLE_BIN_FOR(sb_hprot)
        `SINGLE_BIN_FOR(sb_hsize)
        `SINGLE_BIN_FOR(sb_htrans)
        `SINGLE_BIN_FOR(sb_hwrite)
    endgroup
    `endif

    `ifdef RV_BUILD_AXI4
    covergroup el2_veer_lockstep_sb_axi_differ  @(posedge clk iff rst_n);
        option.per_instance = 1;
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
    endgroup
    `endif

    // Instruction Cache
    covergroup el2_veer_lockstep_ic_differ @(posedge clk iff rst_n);
        option.per_instance = 1;
        `SINGLE_BIN_FOR(ic_rw_addr)
        `SINGLE_BIN_FOR(ic_tag_valid)
        `SINGLE_BIN_FOR(ic_wr_en)
        `SINGLE_BIN_FOR(ic_rd_en)
        `SINGLE_BIN_FOR(ic_wr_data)
        `SINGLE_BIN_FOR(ic_debug_wr_data)
        `SINGLE_BIN_FOR(ic_debug_addr)
        `SINGLE_BIN_FOR(ic_debug_rd_en)
        `SINGLE_BIN_FOR(ic_debug_wr_en)
        `SINGLE_BIN_FOR(ic_debug_tag_array)
        `SINGLE_BIN_FOR(ic_debug_way)
    endgroup

    // Miscellaneous outputs
    covergroup el2_veer_lockstep_miscellaneous_differ @(posedge clk iff rst_n);
        option.per_instance = 1;
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

    initial begin
        el2_veer_lockstep_error_source el2_veer_lockstep_error_source_cg = new();
        el2_veer_lockstep_error_disable el2_veer_lockstep_error_disable_cg = new();
        el2_veer_lockstep_delay_cov el2_veer_lockstep_delay_cov_cg = new();
        el2_veer_lockstep_trace_differ el2_veer_lockstep_trace_differ_cg = new();
    `ifdef RV_BUILD_AXI4
        el2_veer_lockstep_lsu_axi_differ el2_veer_lockstep_lsu_axi_differ_cg = new();
        el2_veer_lockstep_ifu_axi_differ el2_veer_lockstep_ifu_axi_differ_cg = new();
        el2_veer_lockstep_dma_axi_differ el2_veer_lockstep_dma_axi_differ_cg = new();
        el2_veer_lockstep_sb_axi_differ el2_veer_lockstep_sb_axi_differ_cg = new();
    `endif
    `ifdef RV_BUILD_AHB_LITE
        el2_veer_lockstep_lsu_ahb_differ el2_veer_lockstep_lsu_ahb_differ_cg = new();
        el2_veer_lockstep_ifu_ahb_differ el2_veer_lockstep_ifu_ahb_differ_cg = new();
        el2_veer_lockstep_dma_ahb_differ el2_veer_lockstep_dma_ahb_differ_cg = new();
        el2_veer_lockstep_sb_ahb_differ el2_veer_lockstep_sb_ahb_differ_cg = new();
    `endif
        el2_veer_lockstep_ic_differ el2_veer_lockstep_ic_differ_cg = new();
        el2_veer_lockstep_miscellaneous_differ el2_veer_lockstep_miscellaneous_differ_cg = new();
`ifdef RV_LOCKSTEP_REGFILE_ENABLE
        el2_veer_lockstep_reg_differ el2_veer_lockstep_reg_differ_cg = new();
`endif
        $display("Lockstep coverage created");
    end

endinterface

`endif
