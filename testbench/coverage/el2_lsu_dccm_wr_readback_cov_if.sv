/*
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2026 Google LLC
 *
 * DCCM Write Readback Protection Functional Coverage Interface
 * Author: Samip Modi (samipmodi@google.com)
 *
 * Description:
 * Dual-mode functional coverage interface for Synopsys VCS (IEEE 1800 covergroup)
 * and Verilator (SVA cover property) verifying Task #6:
 * - DCCM write-readback runtime/build enable state (dccm_wr_readback_enabled_cp)
 * - Readback verification via idle port steal vs active load snoop (readback_steal_vs_snoop_cp)
 * - Write-readback mismatch error pin assertion (write_readback_error_pin_cp)
 * - DMI first-fault-wins sticky capture registers 0x48-0x4A and W1C clear
 *   (dmi_first_fault_wins_registers_cp, Issue #561)
 * - Issue #566 single-bit correctable vs multi-bit uncorrectable codeword mismatch
 *   hamming distance and ECC scrub interaction (readback_mismatch_hamming_weight_cp)
 * - Issue #572 snoop bank selection (lo vs hi) and store-buffer / DMA write deferral
 */

interface el2_lsu_dccm_wr_readback_cov_if #(
    `include "el2_param.vh"
) (
    input logic                           clk,
    input logic                           rst_l,
    input logic [31:0]                    lsu_addr_d,
    input logic [pt.DCCM_BITS-1:0]        end_addr_d,
    input logic                           stbuf_reqvld_any,
    input logic [pt.LSU_SB_BITS-1:0]      stbuf_addr_any,
    input logic                           dma_dccm_wen,
    input logic                           lsu_stbuf_commit_any,
    input logic                           lsu_dccm_rden_d,
    input logic                           ld_single_ecc_error_r_ff,
    input logic [pt.DCCM_FDATA_WIDTH-1:0] dccm_wr_data_lo,
    input logic [pt.DCCM_FDATA_WIDTH-1:0] dccm_rd_data_lo,
    input logic [pt.DCCM_FDATA_WIDTH-1:0] dccm_rd_data_hi,
    input logic                           dccm_wr_rdbk_pend_ff,
    input logic                           dccm_wr_readback_error,
    input logic                           dec_tlu_dccm_wr_readback_disable,
    input logic                           dccm_wr_rdbk_fault_valid,
    input logic [pt.DCCM_BITS-1:0]        dccm_wr_rdbk_fault_addr,
    input logic [pt.DCCM_FDATA_WIDTH-1:0] dccm_wr_rdbk_fault_data,
    input logic                           dccm_wr_rdbk_fault_clear
);

`ifdef RV_DCCM_WR_READBACK
  localparam bit RdbkHwEnabled = (pt.DCCM_ENABLE == 1);
`else
  localparam bit RdbkHwEnabled = 1'b0;
`endif
  localparam int DccmDataWidth  = int'(pt.DCCM_DATA_WIDTH);
  localparam int DccmFdataWidth = int'(pt.DCCM_FDATA_WIDTH);

  // Readback resolution mode encoding for readback_steal_vs_snoop_cp
  typedef enum logic [1:0] {
    RDBK_RESOLVE_NONE  = 2'd0,
    RDBK_STEAL_CYCLE   = 2'd1,
    RDBK_SNOOP_CYCLE   = 2'd2
  } rdbk_resolve_mode_e;

  logic                           feature_active;
  logic                           rdbk_arm;
  logic                           rdbk_steal;
  logic                           rdbk_snoop_lo;
  logic                           rdbk_snoop_hi;
  logic                           rdbk_snoop_any;
  logic                           rdbk_resolve;
  logic                           rdbk_active;
  logic                           rdbk_active_hi;
  rdbk_resolve_mode_e             rdbk_resolve_mode_ff;

  logic [pt.DCCM_BITS-1:0]        rdbk_addr_ff;
  logic [pt.DCCM_FDATA_WIDTH-1:0] rdbk_data_ff;
  logic [pt.DCCM_FDATA_WIDTH-1:0] rdbk_expect_ff;
  logic [pt.DCCM_FDATA_WIDTH-1:0] rdbk_actual_codeword;
  logic [5:0]                     rdbk_mismatch_bits;

  // DMI first-fault-wins sticky capture tracking
  logic                           fault_capture_en;
  logic                           fault_capture_q;
  logic                           subsequent_fault_q;
  logic [pt.DCCM_BITS-1:0]        expected_first_fault_addr_ff;
  logic [pt.DCCM_FDATA_WIDTH-1:0] expected_first_fault_data_ff;
  logic [5:0]                     dmi_fault_event_vec;

  // Deferral tracking (Issues #566 and #572)
  logic                           stbuf_drain_deferred;
  logic                           dma_write_deferred;
  logic                           rdbk_deferred_by_ecc_scrub;
  logic                           cov_sample_en;

  assign feature_active = RdbkHwEnabled & ~dec_tlu_dccm_wr_readback_disable;
  assign rdbk_arm       = lsu_stbuf_commit_any & feature_active;

  // Steal vs Snoop resolution when dccm_wr_rdbk_pend_ff is active
  assign rdbk_snoop_lo  = dccm_wr_rdbk_pend_ff & lsu_dccm_rden_d &
                          (lsu_addr_d[pt.DCCM_BITS-1:0] == rdbk_addr_ff);
  assign rdbk_snoop_hi  = dccm_wr_rdbk_pend_ff & lsu_dccm_rden_d &
                          (end_addr_d[pt.DCCM_BITS-1:0] == rdbk_addr_ff);
  assign rdbk_snoop_any = rdbk_snoop_lo | rdbk_snoop_hi;
  assign rdbk_steal     = dccm_wr_rdbk_pend_ff & ~lsu_dccm_rden_d & ~ld_single_ecc_error_r_ff;
  assign rdbk_resolve   = rdbk_steal | rdbk_snoop_any;

  // Issue #566 codeword Hamming distance calculation on active readback comparison
  assign rdbk_actual_codeword = rdbk_active_hi ? dccm_rd_data_hi : dccm_rd_data_lo;
  assign rdbk_mismatch_bits   = rdbk_active ?
                                6'($countones(rdbk_actual_codeword ^ rdbk_expect_ff)) : 6'd0;

  // First-fault-wins capture enable
  assign fault_capture_en = dccm_wr_readback_error & ~dccm_wr_rdbk_fault_valid;

  always_ff @(posedge clk or negedge rst_l) begin
    if (!rst_l) begin
      rdbk_addr_ff                 <= '0;
      rdbk_data_ff                 <= '0;
      rdbk_expect_ff               <= '0;
      rdbk_active                  <= 1'b0;
      rdbk_active_hi               <= 1'b0;
      rdbk_resolve_mode_ff         <= RDBK_RESOLVE_NONE;
      fault_capture_q              <= 1'b0;
      subsequent_fault_q           <= 1'b0;
      expected_first_fault_addr_ff <= '0;
      expected_first_fault_data_ff <= '0;
    end else begin
      if (rdbk_arm) begin
        rdbk_addr_ff <= stbuf_addr_any[pt.DCCM_BITS-1:0];
        rdbk_data_ff <= dccm_wr_data_lo;
      end

      rdbk_active    <= rdbk_resolve;
      rdbk_active_hi <= rdbk_snoop_hi & ~rdbk_snoop_lo;

      if (rdbk_resolve) begin
        rdbk_expect_ff       <= rdbk_data_ff;
        rdbk_resolve_mode_ff <= rdbk_steal ? RDBK_STEAL_CYCLE : RDBK_SNOOP_CYCLE;
      end else if (!rdbk_active) begin
        rdbk_resolve_mode_ff <= RDBK_RESOLVE_NONE;
      end

      fault_capture_q    <= fault_capture_en & ~dccm_wr_rdbk_fault_clear;
      subsequent_fault_q <= dccm_wr_readback_error & dccm_wr_rdbk_fault_valid &
                            ~dccm_wr_rdbk_fault_clear;

      if (fault_capture_en) begin
        expected_first_fault_addr_ff <= rdbk_addr_ff;
        expected_first_fault_data_ff <= rdbk_actual_codeword;
      end
    end
  end

  // DMI First-Fault-Wins status/data/ecc/W1C/subsequent-fault event vector (Issue #561):
  // [0]: fault_valid_set          - Offset 0x48 bit 31 set to 1
  // [1]: fault_addr_captured      - Offset 0x48 captures faulty write address
  // [2]: fault_data_captured      - Offset 0x49 captures corrupted readback data [31:0]
  // [3]: fault_ecc_captured       - Offset 0x4A captures readback ECC bits [38:32]
  // [4]: fault_clear_w1c          - Software clears bit 31 via DMI write-1-to-clear
  // [5]: subsequent_fault_ignored - Additional write fault while valid==1 preserves first fault
  assign dmi_fault_event_vec[0] = fault_capture_q & dccm_wr_rdbk_fault_valid;
  assign dmi_fault_event_vec[1] = fault_capture_q & dccm_wr_rdbk_fault_valid &
                                  (dccm_wr_rdbk_fault_addr == expected_first_fault_addr_ff);
  assign dmi_fault_event_vec[2] = fault_capture_q & dccm_wr_rdbk_fault_valid &
                                  (dccm_wr_rdbk_fault_data[DccmDataWidth-1:0] ==
                                   expected_first_fault_data_ff[DccmDataWidth-1:0]);
  assign dmi_fault_event_vec[3] = fault_capture_q & dccm_wr_rdbk_fault_valid &
                                  (dccm_wr_rdbk_fault_data[DccmFdataWidth-1:DccmDataWidth] ==
                                   expected_first_fault_data_ff[DccmFdataWidth-1:DccmDataWidth]);
  assign dmi_fault_event_vec[4] = dccm_wr_rdbk_fault_clear & dccm_wr_rdbk_fault_valid;
  assign dmi_fault_event_vec[5] = subsequent_fault_q & dccm_wr_rdbk_fault_valid &
                                  (dccm_wr_rdbk_fault_addr == expected_first_fault_addr_ff) &
                                  (dccm_wr_rdbk_fault_data == expected_first_fault_data_ff);

  // Deferral conditions while a write-readback window is pending (Issues #566 and #572)
  assign stbuf_drain_deferred       = stbuf_reqvld_any & dccm_wr_rdbk_pend_ff;
  assign dma_write_deferred         = dma_dccm_wen & dccm_wr_rdbk_pend_ff;
  assign rdbk_deferred_by_ecc_scrub = dccm_wr_rdbk_pend_ff & ld_single_ecc_error_r_ff;

  assign cov_sample_en = lsu_stbuf_commit_any | rdbk_resolve | rdbk_active |
                         (|dmi_fault_event_vec) | stbuf_drain_deferred |
                         dma_write_deferred | rdbk_deferred_by_ecc_scrub;

`ifndef VERILATOR
  // -------------------------------------------------------------------------
  // VCS / IEEE 1800 Covergroup: DCCM Write Readback Protection Coverage
  // -------------------------------------------------------------------------
  covergroup el2_lsu_dccm_wr_readback_cov @(posedge clk iff (rst_l && cov_sample_en));
    type_option.merge_instances = 1;

    // Coverpoint dccm_wr_readback_enabled_cp:
    // Covers DCCM stores with write-readback enabled vs disabled via MFDC bit 7 (dwrd)
    dccm_wr_readback_enabled_cp: coverpoint feature_active iff (lsu_stbuf_commit_any) {
      bins feature_disabled = {1'b0};
      bins feature_enabled  = {1'b1};
    }

    // Coverpoint readback_steal_vs_snoop_cp:
    // Covers readback verification via idle cycle steal vs active read snoop
    readback_steal_vs_snoop_cp: coverpoint rdbk_resolve_mode_ff iff (rdbk_active) {
      bins steal_cycle = {RDBK_STEAL_CYCLE};
      bins snoop_cycle = {RDBK_SNOOP_CYCLE};
    }

    // Coverpoint write_readback_error_pin_cp:
    // Covers dccm_wr_readback_error output pin on active readback comparison
    write_readback_error_pin_cp: coverpoint dccm_wr_readback_error iff (rdbk_active) {
      bins no_error       = {1'b0};
      bins error_asserted = {1'b1};
    }

    // Coverpoint dmi_first_fault_wins_registers_cp (Issue #561 DMI offsets 0x48-0x4A):
    // Covers sticky first-fault-wins status, address, data, ECC, W1C clear, and subsequent fault ignore
    dmi_first_fault_wins_registers_cp: coverpoint dmi_fault_event_vec iff (|dmi_fault_event_vec) {
      wildcard bins fault_valid_set          = {6'b????_?1};
      wildcard bins fault_addr_captured      = {6'b????_1?};
      wildcard bins fault_data_captured      = {6'b???1_??};
      wildcard bins fault_ecc_captured       = {6'b??1?_??};
      wildcard bins fault_clear_w1c          = {6'b?1??_??};
      wildcard bins subsequent_fault_ignored = {6'b1???_??};
    }

    // Coverpoint readback_mismatch_hamming_weight_cp (Issue #566):
    // Distinguishes 0-bit match, 1-bit SECDED-correctable stuck-at mismatch, and >=2-bit mismatch
    readback_mismatch_hamming_weight_cp: coverpoint rdbk_mismatch_bits iff (rdbk_active) {
      bins no_bit_mismatch         = {6'd0};
      bins single_bit_mismatch_sbe = {6'd1};
      bins multi_bit_mismatch_dbe  = {[6'd2 : 6'd39]};
    }

    // Coverpoint snoop_bank_select_cp (Issue #572):
    // Covers snoop resolution via lo bank vs hi bank (unaligned dual-bank load)
    snoop_bank_select_cp: coverpoint rdbk_active_hi
        iff (rdbk_active && (rdbk_resolve_mode_ff == RDBK_SNOOP_CYCLE)) {
      bins snoop_lo_bank = {1'b0};
      bins snoop_hi_bank = {1'b1};
    }

    // Coverpoint pending_readback_deferral_cp (Issues #566 & #572):
    // Covers store-buffer drain deferral, DMA write deferral, and ECC scrub priority over steal
    pending_readback_deferral_cp: coverpoint {rdbk_deferred_by_ecc_scrub,
                                              dma_write_deferred,
                                              stbuf_drain_deferred}
        iff (stbuf_drain_deferred | dma_write_deferred | rdbk_deferred_by_ecc_scrub) {
      wildcard bins stbuf_drain_deferred          = {3'b??1};
      wildcard bins dma_write_deferred            = {3'b?1?};
      wildcard bins readback_deferred_by_ecc_scrub = {3'b1??};
    }

    // Cross Coverage:
    // Cross readback resolution mode (steal vs snoop) with error pin state
    readback_mode_x_error_pin: cross readback_steal_vs_snoop_cp, write_readback_error_pin_cp;

    // Cross readback resolution mode with Issue #566 mismatch Hamming weight
    readback_mode_x_mismatch_weight: cross readback_steal_vs_snoop_cp,
                                           readback_mismatch_hamming_weight_cp;
  endgroup

  initial begin
    el2_lsu_dccm_wr_readback_cov el2_lsu_dccm_wr_readback_cov_cg = new();
    $display("DCCM write-readback coverage interface created");
  end
`else
  // -------------------------------------------------------------------------
  // Functional Coverage for Verilator via SystemVerilog Assertions (`cover property`)
  // -------------------------------------------------------------------------

  // 1. Feature enable/disable coverpoints (dccm_wr_readback_enabled_cp)
  cov_dccm_wr_rdbk_feature_enabled: cover property (@(posedge clk) disable iff (!rst_l)
      lsu_stbuf_commit_any && feature_active);
  cov_dccm_wr_rdbk_feature_disabled: cover property (@(posedge clk) disable iff (!rst_l)
      lsu_stbuf_commit_any && !feature_active);

  // 2. Steal vs Snoop resolution coverpoints (readback_steal_vs_snoop_cp)
  cov_rdbk_steal_cycle: cover property (@(posedge clk) disable iff (!rst_l)
      rdbk_active && (rdbk_resolve_mode_ff == RDBK_STEAL_CYCLE));
  cov_rdbk_snoop_cycle: cover property (@(posedge clk) disable iff (!rst_l)
      rdbk_active && (rdbk_resolve_mode_ff == RDBK_SNOOP_CYCLE));

  // 3. Write-readback error pin coverpoints (write_readback_error_pin_cp)
  cov_rdbk_no_error: cover property (@(posedge clk) disable iff (!rst_l)
      rdbk_active && !dccm_wr_readback_error);
  cov_rdbk_error_asserted: cover property (@(posedge clk) disable iff (!rst_l)
      rdbk_active && dccm_wr_readback_error);

  // 4. DMI first-fault-wins sticky register coverpoints (dmi_first_fault_wins_registers_cp, Issue #561)
  cov_dmi_fault_valid_set: cover property (@(posedge clk) disable iff (!rst_l)
      dmi_fault_event_vec[0]);
  cov_dmi_fault_addr_captured: cover property (@(posedge clk) disable iff (!rst_l)
      dmi_fault_event_vec[1]);
  cov_dmi_fault_data_captured: cover property (@(posedge clk) disable iff (!rst_l)
      dmi_fault_event_vec[2]);
  cov_dmi_fault_ecc_captured: cover property (@(posedge clk) disable iff (!rst_l)
      dmi_fault_event_vec[3]);
  cov_dmi_fault_clear_w1c: cover property (@(posedge clk) disable iff (!rst_l)
      dmi_fault_event_vec[4]);
  cov_dmi_subsequent_fault_ignored: cover property (@(posedge clk) disable iff (!rst_l)
      dmi_fault_event_vec[5]);

  // 5. Issue #566 Mismatch Hamming Weight coverpoints (readback_mismatch_hamming_weight_cp)
  cov_rdbk_mismatch_none: cover property (@(posedge clk) disable iff (!rst_l)
      rdbk_active && (rdbk_mismatch_bits == 6'd0));
  cov_rdbk_mismatch_single_bit_sbe: cover property (@(posedge clk) disable iff (!rst_l)
      rdbk_active && (rdbk_mismatch_bits == 6'd1));
  cov_rdbk_mismatch_multi_bit_dbe: cover property (@(posedge clk) disable iff (!rst_l)
      rdbk_active && (rdbk_mismatch_bits >= 6'd2));

  // 6. Issue #572 Snoop Bank Selection & Deferral coverpoints
  cov_rdbk_snoop_lo_bank: cover property (@(posedge clk) disable iff (!rst_l)
      rdbk_active && (rdbk_resolve_mode_ff == RDBK_SNOOP_CYCLE) && !rdbk_active_hi);
  cov_rdbk_snoop_hi_bank: cover property (@(posedge clk) disable iff (!rst_l)
      rdbk_active && (rdbk_resolve_mode_ff == RDBK_SNOOP_CYCLE) && rdbk_active_hi);

  cov_rdbk_stbuf_drain_deferred: cover property (@(posedge clk) disable iff (!rst_l)
      stbuf_drain_deferred);
  cov_rdbk_dma_write_deferred: cover property (@(posedge clk) disable iff (!rst_l)
      dma_write_deferred);
  cov_rdbk_deferred_by_ecc_scrub: cover property (@(posedge clk) disable iff (!rst_l)
      rdbk_deferred_by_ecc_scrub);

  // 7. Cross Coverage: readback_mode_x_error_pin & readback_mode_x_mismatch_weight
  cov_steal_x_no_error: cover property (@(posedge clk) disable iff (!rst_l)
      rdbk_active && (rdbk_resolve_mode_ff == RDBK_STEAL_CYCLE) && !dccm_wr_readback_error);
  cov_steal_x_error_asserted: cover property (@(posedge clk) disable iff (!rst_l)
      rdbk_active && (rdbk_resolve_mode_ff == RDBK_STEAL_CYCLE) && dccm_wr_readback_error);
  cov_snoop_x_no_error: cover property (@(posedge clk) disable iff (!rst_l)
      rdbk_active && (rdbk_resolve_mode_ff == RDBK_SNOOP_CYCLE) && !dccm_wr_readback_error);
  cov_snoop_x_error_asserted: cover property (@(posedge clk) disable iff (!rst_l)
      rdbk_active && (rdbk_resolve_mode_ff == RDBK_SNOOP_CYCLE) && dccm_wr_readback_error);

  cov_steal_x_no_mismatch: cover property (@(posedge clk) disable iff (!rst_l)
      rdbk_active && (rdbk_resolve_mode_ff == RDBK_STEAL_CYCLE) && (rdbk_mismatch_bits == 6'd0));
  cov_steal_x_sbe_mismatch: cover property (@(posedge clk) disable iff (!rst_l)
      rdbk_active && (rdbk_resolve_mode_ff == RDBK_STEAL_CYCLE) && (rdbk_mismatch_bits == 6'd1));
  cov_steal_x_dbe_mismatch: cover property (@(posedge clk) disable iff (!rst_l)
      rdbk_active && (rdbk_resolve_mode_ff == RDBK_STEAL_CYCLE) && (rdbk_mismatch_bits >= 6'd2));
  cov_snoop_x_no_mismatch: cover property (@(posedge clk) disable iff (!rst_l)
      rdbk_active && (rdbk_resolve_mode_ff == RDBK_SNOOP_CYCLE) && (rdbk_mismatch_bits == 6'd0));
  cov_snoop_x_sbe_mismatch: cover property (@(posedge clk) disable iff (!rst_l)
      rdbk_active && (rdbk_resolve_mode_ff == RDBK_SNOOP_CYCLE) && (rdbk_mismatch_bits == 6'd1));
  cov_snoop_x_dbe_mismatch: cover property (@(posedge clk) disable iff (!rst_l)
      rdbk_active && (rdbk_resolve_mode_ff == RDBK_SNOOP_CYCLE) && (rdbk_mismatch_bits >= 6'd2));

  initial begin
    $display("DCCM write-readback coverage interface created (Verilator SVA mode)");
  end
`endif

endinterface
