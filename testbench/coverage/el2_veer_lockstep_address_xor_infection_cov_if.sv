/*
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2026 Google LLC
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// ----------------------------------------------------------------------------
// Dual-mode functional coverage interface for VCS (covergroup) and Verilator
// (SVA cover property)
// Target: Task 4 - Memory Address XOR Infection Coverage (ICCM, DCCM, ICache,
//                  DCLS iccm_rd_data, and Issues #550, #562, #569)
// ----------------------------------------------------------------------------

`include "common_defines.vh"

interface el2_veer_lockstep_address_xor_infection_cov_if
  import el2_pkg::*;
  import el2_mubi_pkg::*;
  import el2_lockstep_pkg::*;
#(
  `include "el2_param.vh"
) (
  input logic                          clk,
  input logic                          rst_n,
  input logic [pt.ICCM_BITS-1:1]       iccm_rw_addr,
  input logic                          iccm_wren,
  input logic                          iccm_rden,
  input logic [2:0]                    iccm_wr_size,
  input logic                          iccm_buf_correct_ecc,
  input logic                          iccm_correction_state,
  input logic [pt.ICACHE_NUM_WAYS-1:0] ic_rd_hit,
  input logic                          iccm_ecc_single_error,
  input logic                          iccm_ecc_double_error,
  input logic                          dccm_ecc_single_error,
  input logic                          dccm_ecc_double_error,
  input logic                          dccm_write_readback_error,
  input logic                          shadow_ic_perr_r,
  input veer_inputs_t                  shadow_core_inputs_pre,
  input veer_inputs_t                  shadow_core_inputs,
  input veer_outputs_t                 delayed_main_core_outputs,
  input veer_outputs_t                 shadow_core_outputs,
  input el2_mubi_t                     corruption_detected_o
);

`ifdef RV_ICCM_ADDR_XOR
  localparam bit IccmAddrXor = 1'b1;
`else
  localparam bit IccmAddrXor = 1'b0;
`endif

`ifdef RV_DCCM_ADDR_XOR
  localparam bit DccmAddrXor = 1'b1;
`else
  localparam bit DccmAddrXor = 1'b0;
`endif

`ifdef RV_ICACHE_ADDR_XOR
  localparam bit IcacheAddrXor = 1'b1;
`else
  localparam bit IcacheAddrXor = 1'b0;
`endif

  // -------------------------------------------------------------------------
  // 1. ICCM Address-XOR Infection & Subordinate Core Divergence Tracking
  // -------------------------------------------------------------------------
  logic       iccm_xor_active;
  logic       iccm_mismatch_detected;
  logic [1:0] iccm_xor_infection_cats;

  // RV_ICCM_ADDR_XOR enabled with an active ICCM ECC error or address/data fault
  assign iccm_xor_active = IccmAddrXor && (
      iccm_ecc_single_error ||
      iccm_ecc_double_error ||
      shadow_core_outputs.iccm_ecc_single_error ||
      shadow_core_outputs.iccm_ecc_double_error ||
      (delayed_main_core_outputs.iccm_rw_addr != shadow_core_outputs.iccm_rw_addr) ||
      (delayed_main_core_outputs.iccm_wr_data != shadow_core_outputs.iccm_wr_data) ||
      (shadow_core_inputs_pre.iccm_rd_data_ecc != shadow_core_inputs.iccm_rd_data_ecc)
  );

  // Subordinate core ICCM address/datapath divergence triggers DCLS mismatch
  assign iccm_mismatch_detected = mubi_check_true(corruption_detected_o) && (
      (delayed_main_core_outputs.iccm_rw_addr != shadow_core_outputs.iccm_rw_addr) ||
      (delayed_main_core_outputs.iccm_wr_data != shadow_core_outputs.iccm_wr_data) ||
      (delayed_main_core_outputs.iccm_wren != shadow_core_outputs.iccm_wren) ||
      (delayed_main_core_outputs.iccm_rden != shadow_core_outputs.iccm_rden) ||
      (delayed_main_core_outputs.iccm_ecc_single_error !=
       shadow_core_outputs.iccm_ecc_single_error) ||
      (delayed_main_core_outputs.iccm_ecc_double_error !=
       shadow_core_outputs.iccm_ecc_double_error) ||
      (shadow_core_inputs_pre.iccm_rd_data_ecc != shadow_core_inputs.iccm_rd_data_ecc)
  );

  assign iccm_xor_infection_cats = {iccm_mismatch_detected, iccm_xor_active};

  // -------------------------------------------------------------------------
  // 2. DCCM Address-XOR Infection & Subordinate Core Divergence Tracking
  // -------------------------------------------------------------------------
  logic       dccm_xor_active;
  logic       dccm_mismatch_detected;
  logic [1:0] dccm_xor_infection_cats;

  // RV_DCCM_ADDR_XOR enabled with an active DCCM ECC/readback error or address/data fault
  assign dccm_xor_active = DccmAddrXor && (
      dccm_ecc_single_error ||
      dccm_ecc_double_error ||
      dccm_write_readback_error ||
      shadow_core_outputs.dccm_ecc_single_error ||
      shadow_core_outputs.dccm_ecc_double_error ||
      shadow_core_outputs.dccm_write_readback_error ||
      (delayed_main_core_outputs.dccm_rd_addr_lo != shadow_core_outputs.dccm_rd_addr_lo) ||
      (delayed_main_core_outputs.dccm_rd_addr_hi != shadow_core_outputs.dccm_rd_addr_hi) ||
      (delayed_main_core_outputs.dccm_wr_addr_lo != shadow_core_outputs.dccm_wr_addr_lo) ||
      (delayed_main_core_outputs.dccm_wr_addr_hi != shadow_core_outputs.dccm_wr_addr_hi) ||
      (delayed_main_core_outputs.dccm_wr_data_lo != shadow_core_outputs.dccm_wr_data_lo) ||
      (delayed_main_core_outputs.dccm_wr_data_hi != shadow_core_outputs.dccm_wr_data_hi) ||
      (shadow_core_inputs_pre.dccm_rd_data_lo != shadow_core_inputs.dccm_rd_data_lo) ||
      (shadow_core_inputs_pre.dccm_rd_data_hi != shadow_core_inputs.dccm_rd_data_hi)
  );

  // Subordinate core DCCM address/datapath divergence triggers DCLS mismatch
  assign dccm_mismatch_detected = mubi_check_true(corruption_detected_o) && (
      (delayed_main_core_outputs.dccm_rd_addr_lo != shadow_core_outputs.dccm_rd_addr_lo) ||
      (delayed_main_core_outputs.dccm_rd_addr_hi != shadow_core_outputs.dccm_rd_addr_hi) ||
      (delayed_main_core_outputs.dccm_wr_addr_lo != shadow_core_outputs.dccm_wr_addr_lo) ||
      (delayed_main_core_outputs.dccm_wr_addr_hi != shadow_core_outputs.dccm_wr_addr_hi) ||
      (delayed_main_core_outputs.dccm_wr_data_lo != shadow_core_outputs.dccm_wr_data_lo) ||
      (delayed_main_core_outputs.dccm_wr_data_hi != shadow_core_outputs.dccm_wr_data_hi) ||
      (delayed_main_core_outputs.dccm_wren != shadow_core_outputs.dccm_wren) ||
      (delayed_main_core_outputs.dccm_rden != shadow_core_outputs.dccm_rden) ||
      (delayed_main_core_outputs.dccm_ecc_single_error !=
       shadow_core_outputs.dccm_ecc_single_error) ||
      (delayed_main_core_outputs.dccm_ecc_double_error !=
       shadow_core_outputs.dccm_ecc_double_error) ||
      (delayed_main_core_outputs.dccm_write_readback_error !=
       shadow_core_outputs.dccm_write_readback_error) ||
      (shadow_core_inputs_pre.dccm_rd_data_lo != shadow_core_inputs.dccm_rd_data_lo) ||
      (shadow_core_inputs_pre.dccm_rd_data_hi != shadow_core_inputs.dccm_rd_data_hi)
  );

  assign dccm_xor_infection_cats = {dccm_mismatch_detected, dccm_xor_active};

  // -------------------------------------------------------------------------
  // 3. ICache Address-XOR Infection & Subordinate Core Divergence Tracking
  // -------------------------------------------------------------------------
  logic       icache_xor_active;
  logic       icache_mismatch_detected;
  logic       icache_dcls_ctrl_divergence;
  logic [1:0] icache_xor_infection_cats;

  // RV_ICACHE_ADDR_XOR enabled with an active ICache ECC/parity error or address/data fault
  assign icache_xor_active = IcacheAddrXor && (
      shadow_ic_perr_r ||
      shadow_core_inputs_pre.ic_tag_perr ||
      shadow_core_inputs.ic_tag_perr ||
      (delayed_main_core_outputs.ic_rw_addr != shadow_core_outputs.ic_rw_addr) ||
      (delayed_main_core_outputs.ic_wr_data != shadow_core_outputs.ic_wr_data) ||
      (shadow_core_inputs_pre.ic_rd_data != shadow_core_inputs.ic_rd_data) ||
      icache_dcls_ctrl_divergence
  );

  // Subordinate core ICache address/datapath divergence triggers DCLS mismatch
  assign icache_mismatch_detected = mubi_check_true(corruption_detected_o) && (
      (delayed_main_core_outputs.ic_rw_addr != shadow_core_outputs.ic_rw_addr) ||
      (delayed_main_core_outputs.ic_rd_en != shadow_core_outputs.ic_rd_en) ||
      (delayed_main_core_outputs.ic_wr_en != shadow_core_outputs.ic_wr_en) ||
      (delayed_main_core_outputs.ic_wr_data != shadow_core_outputs.ic_wr_data) ||
      (delayed_main_core_outputs.ic_tag_valid != shadow_core_outputs.ic_tag_valid) ||
      (delayed_main_core_outputs.ic_debug_addr != shadow_core_outputs.ic_debug_addr) ||
      (shadow_core_inputs_pre.ic_rd_data != shadow_core_inputs.ic_rd_data) ||
      (shadow_core_inputs_pre.ic_rd_hit != shadow_core_inputs.ic_rd_hit) ||
      (shadow_core_inputs_pre.ic_tag_perr != shadow_core_inputs.ic_tag_perr) ||
      icache_dcls_ctrl_divergence
  );

  assign icache_xor_infection_cats = {icache_mismatch_detected, icache_xor_active};

  // -------------------------------------------------------------------------
  // 4. DCLS Domain ICCM Read Data (iccm_rd_data) Divergence Tracking (0b61bfd)
  // -------------------------------------------------------------------------
  // Reconstruct the F-stage de-XORed 64-bit iccm_rd_data for both the delayed
  // main core and the subordinate shadow core inside the DCLS domain (matching
  // el2_ifu_mem_ctl), gated against write cycles so write-only mismatches do
  // not falsely trigger read-data divergence.
  logic [pt.ICCM_BITS-1:1] main_iccm_rw_addr_f;
  logic [pt.ICCM_BITS-1:1] shadow_iccm_rw_addr_f;
  logic                    main_iccm_wren_f;
  logic                    shadow_iccm_wren_f;
  logic                    main_iccm_rden_f;
  logic                    shadow_iccm_rden_f;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      main_iccm_rw_addr_f   <= '0;
      shadow_iccm_rw_addr_f <= '0;
      main_iccm_wren_f      <= 1'b0;
      shadow_iccm_wren_f    <= 1'b0;
      main_iccm_rden_f      <= 1'b0;
      shadow_iccm_rden_f    <= 1'b0;
    end else begin
      main_iccm_rw_addr_f   <= delayed_main_core_outputs.iccm_rw_addr;
      shadow_iccm_rw_addr_f <= shadow_core_outputs.iccm_rw_addr;
      main_iccm_wren_f      <= delayed_main_core_outputs.iccm_wren;
      shadow_iccm_wren_f    <= shadow_core_outputs.iccm_wren;
      main_iccm_rden_f      <= delayed_main_core_outputs.iccm_rden;
      shadow_iccm_rden_f    <= shadow_core_outputs.iccm_rden;
    end
  end

  logic [pt.ICCM_BITS-1:2] main_iccm_rd_wa_w0, main_iccm_rd_wa_w1;
  logic [pt.ICCM_BITS-1:2] shadow_iccm_rd_wa_w0, shadow_iccm_rd_wa_w1;
  logic [31:0]             main_iccm_rd_xor_mask_w0, main_iccm_rd_xor_mask_w1;
  logic [31:0]             shadow_iccm_rd_xor_mask_w0, shadow_iccm_rd_xor_mask_w1;
  logic [31:0]             main_iccm_rdmux_w0, main_iccm_rdmux_w1;
  logic [31:0]             shadow_iccm_rdmux_w0, shadow_iccm_rdmux_w1;
  logic [63:0]             delayed_main_iccm_rd_data;
  logic [63:0]             shadow_iccm_rd_data;
  logic                    iccm_rd_data_divergence;

  assign main_iccm_rd_wa_w0   = main_iccm_rw_addr_f[pt.ICCM_BITS-1:2];
  assign main_iccm_rd_wa_w1   = main_iccm_rw_addr_f[pt.ICCM_BITS-1:2] + 1'b1;
  assign shadow_iccm_rd_wa_w0 = shadow_iccm_rw_addr_f[pt.ICCM_BITS-1:2];
  assign shadow_iccm_rd_wa_w1 = shadow_iccm_rw_addr_f[pt.ICCM_BITS-1:2] + 1'b1;

  assign main_iccm_rd_xor_mask_w0 =
      IccmAddrXor ? 32'({main_iccm_rd_wa_w0, main_iccm_rd_wa_w0}) : 32'h0;
  assign main_iccm_rd_xor_mask_w1 =
      IccmAddrXor ? 32'({main_iccm_rd_wa_w1, main_iccm_rd_wa_w1}) : 32'h0;
  assign shadow_iccm_rd_xor_mask_w0 =
      IccmAddrXor ? 32'({shadow_iccm_rd_wa_w0, shadow_iccm_rd_wa_w0}) : 32'h0;
  assign shadow_iccm_rd_xor_mask_w1 =
      IccmAddrXor ? 32'({shadow_iccm_rd_wa_w1, shadow_iccm_rd_wa_w1}) : 32'h0;

  assign main_iccm_rdmux_w0 =
      shadow_core_inputs_pre.iccm_rd_data_ecc[31:0] ^ main_iccm_rd_xor_mask_w0;
  assign main_iccm_rdmux_w1 =
      shadow_core_inputs_pre.iccm_rd_data_ecc[70:39] ^ main_iccm_rd_xor_mask_w1;
  assign shadow_iccm_rdmux_w0 =
      shadow_core_inputs.iccm_rd_data_ecc[31:0] ^ shadow_iccm_rd_xor_mask_w0;
  assign shadow_iccm_rdmux_w1 =
      shadow_core_inputs.iccm_rd_data_ecc[70:39] ^ shadow_iccm_rd_xor_mask_w1;

  assign delayed_main_iccm_rd_data =
      64'({main_iccm_rdmux_w1, main_iccm_rdmux_w0} >> (16 * main_iccm_rw_addr_f[1]));
  assign shadow_iccm_rd_data =
      64'({shadow_iccm_rdmux_w1, shadow_iccm_rdmux_w0} >> (16 * shadow_iccm_rw_addr_f[1]));

  // Asserts when DCLS catches F-stage de-XORed ICCM read-data or read-ECC divergence
  assign iccm_rd_data_divergence =
      mubi_check_true(corruption_detected_o) &&
      (main_iccm_rden_f || shadow_iccm_rden_f) &&
      !(main_iccm_wren_f || shadow_iccm_wren_f) &&
      !(delayed_main_core_outputs.iccm_wren || shadow_core_outputs.iccm_wren) && (
          (delayed_main_iccm_rd_data != shadow_iccm_rd_data) ||
          (shadow_core_inputs_pre.iccm_rd_data_ecc != shadow_core_inputs.iccm_rd_data_ecc) ||
          (delayed_main_core_outputs.iccm_ecc_single_error !=
           shadow_core_outputs.iccm_ecc_single_error) ||
          (delayed_main_core_outputs.iccm_ecc_double_error !=
           shadow_core_outputs.iccm_ecc_double_error)
      );

  // -------------------------------------------------------------------------
  // 5. Issue #550 (PR #552): ICCM DMA Read Size & Word-Enable with Address-XOR
  // -------------------------------------------------------------------------
  // In el2_ifu_mem_ctl, iccm_wr_size[2:0] = {3{dma_iccm_req}} & dma_mem_sz[2:0].
  // During a DMA read (iccm_rden && !iccm_wren && !iccm_buf_correct_ecc):
  // - iccm_wr_size[1:0] == 2'b10: 32-bit word DMA read (checks word 0 only: 2'b01)
  // - iccm_wr_size[1:0] == 2'b11: 64-bit dword DMA read (checks both words: 2'b11)
  logic iccm_dma_rd_req;
  logic iccm_dma_rd_valid_f;
  logic iccm_dma_rd_dword_f;
  logic iccm_dma_rd_odd_word_f;
  logic iccm_dma_rd_valid_f2;
  logic iccm_dma_rd_dword_f2;
  logic iccm_dma_rd_odd_word_f2;

  assign iccm_dma_rd_req = iccm_rden && !iccm_wren && !iccm_buf_correct_ecc &&
                           ((iccm_wr_size[1:0] == 2'b10) || (iccm_wr_size[1:0] == 2'b11));

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      iccm_dma_rd_valid_f     <= 1'b0;
      iccm_dma_rd_dword_f     <= 1'b0;
      iccm_dma_rd_odd_word_f  <= 1'b0;
      iccm_dma_rd_valid_f2    <= 1'b0;
      iccm_dma_rd_dword_f2    <= 1'b0;
      iccm_dma_rd_odd_word_f2 <= 1'b0;
    end else begin
      iccm_dma_rd_valid_f     <= iccm_dma_rd_req;
      iccm_dma_rd_dword_f     <= iccm_dma_rd_req && (iccm_wr_size[1:0] == 2'b11);
      iccm_dma_rd_odd_word_f  <= iccm_rw_addr[2];
      iccm_dma_rd_valid_f2    <= iccm_dma_rd_valid_f;
      iccm_dma_rd_dword_f2    <= iccm_dma_rd_dword_f;
      iccm_dma_rd_odd_word_f2 <= iccm_dma_rd_odd_word_f;
    end
  end

  // -------------------------------------------------------------------------
  // 6. Issue #562 (PR #565): ICCM Redundant Row ECC Correction Lane Select
  // -------------------------------------------------------------------------
  // Mirrors the 2-entry redundant row CAM (redundant_address[1:0], redundant_valid[1:0],
  // redundant_lru) and dual-bank read address increment (addr_bank_inc) from
  // el2_ifu_iccm_mem under RV_ICCM_ADDR_XOR=1 to track single-bit ECC correction
  // writebacks on even (iccm_rw_addr[2]==0, lane 0) and odd (iccm_rw_addr[2]==1,
  // lane 1) words and subsequent clean re-fetches across both primary and upper lanes.
  localparam int IccmAddrWidth = pt.ICCM_BITS - 1;

  logic [1:0]                   iccm_addr_incr;
  logic [pt.ICCM_BITS-1:1]      iccm_addr_bank_inc;
  logic [1:0]                   iccm_red_valid_q;
  logic [1:0][pt.ICCM_BITS-1:2] iccm_red_addr_q;
  logic                         iccm_red_lru_q;
  logic [1:0]                   iccm_sel_red;
  logic                         iccm_red_lru_en;
  logic                         iccm_red_lru_d;
  logic                         iccm_red_reread_even_hit;
  logic                         iccm_red_reread_odd_hit;
  logic                         iccm_redundant_reread_even_req_f;
  logic                         iccm_redundant_reread_odd_req_f;
  logic                         iccm_redundant_reread_even_clean;
  logic                         iccm_redundant_reread_odd_clean;

  assign iccm_addr_incr     = (iccm_wr_size[1:0] == 2'b11) ? 2'b10 : 2'b01;
  assign iccm_addr_bank_inc = iccm_rw_addr[pt.ICCM_BITS-1:1] + IccmAddrWidth'(iccm_addr_incr);

  for (genvar k = 0; k < 2; k++) begin : gen_iccm_red_match
    assign iccm_sel_red[k] = iccm_red_valid_q[k] && (
        (iccm_rw_addr[pt.ICCM_BITS-1:2] == iccm_red_addr_q[k]) ||
        (iccm_addr_bank_inc[pt.ICCM_BITS-1:2] == iccm_red_addr_q[k])
    );
  end

  assign iccm_red_lru_en = iccm_buf_correct_ecc ||
                           ((|iccm_sel_red) && iccm_rden && iccm_correction_state);
  assign iccm_red_lru_d  = iccm_buf_correct_ecc ? !iccm_red_lru_q :
                           iccm_sel_red[0]      ? 1'b1 : 1'b0;

  assign iccm_red_reread_even_hit = (iccm_sel_red[0] && !iccm_red_addr_q[0][2]) ||
                                    (iccm_sel_red[1] && !iccm_red_addr_q[1][2]);
  assign iccm_red_reread_odd_hit  = (iccm_sel_red[0] && iccm_red_addr_q[0][2]) ||
                                    (iccm_sel_red[1] && iccm_red_addr_q[1][2]);

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      iccm_red_valid_q                 <= 2'b00;
      iccm_red_addr_q                  <= '0;
      iccm_red_lru_q                   <= 1'b0;
      iccm_redundant_reread_even_req_f <= 1'b0;
      iccm_redundant_reread_odd_req_f  <= 1'b0;
    end else begin
      if (iccm_buf_correct_ecc) begin
        if (!iccm_red_lru_q) begin
          iccm_red_valid_q[0] <= 1'b1;
          iccm_red_addr_q[0]  <= iccm_rw_addr[pt.ICCM_BITS-1:2];
        end else begin
          iccm_red_valid_q[1] <= 1'b1;
          iccm_red_addr_q[1]  <= iccm_rw_addr[pt.ICCM_BITS-1:2];
        end
      end
      if (iccm_red_lru_en) begin
        iccm_red_lru_q <= iccm_red_lru_d;
      end
      iccm_redundant_reread_even_req_f <= IccmAddrXor && iccm_rden && !iccm_wren &&
                                          !iccm_dma_rd_req &&
                                          iccm_red_reread_even_hit;
      iccm_redundant_reread_odd_req_f  <= IccmAddrXor && iccm_rden && !iccm_wren &&
                                          !iccm_dma_rd_req &&
                                          iccm_red_reread_odd_hit;
    end
  end

  assign iccm_redundant_reread_even_clean = iccm_redundant_reread_even_req_f &&
                                            !iccm_ecc_double_error;
  assign iccm_redundant_reread_odd_clean  = iccm_redundant_reread_odd_req_f &&
                                            !iccm_ecc_double_error;

  // -------------------------------------------------------------------------
  // 7. Issue #569 (PR #571): DCLS-Internal ICache Bank Select, Cacheline-Wrap
  //    Upper-Bank Check Suppression, and Main-vs-Shadow Control Divergence
  // -------------------------------------------------------------------------
  // Reconstructs the F2-stage DCLS-internal ICache read controls moved into
  // el2_ifu_mem_ctl by PR #571 for both the delayed main core and shadow core:
  // - ic_rd_bank_sel: physical bank order ({bank0, bank1} vs. {bank1, bank0})
  // - ic_rd_rot_sel: halfword rotate offset (ic_rw_addr[2:1])
  // - ic_cacheline_wrap: straddle at last 64B cacheline boundary dropping upper check
  logic       main_ic_rd_bank_sel_f, shadow_ic_rd_bank_sel_f;
  logic [1:0] main_ic_rd_rot_sel_f, shadow_ic_rd_rot_sel_f;
  logic       main_ic_cl_wrap_f, shadow_ic_cl_wrap_f;
  logic       main_ic_up_chk_en_f, shadow_ic_up_chk_en_f;
  logic       main_ic_rd_en_no_dbg, shadow_ic_rd_en_no_dbg;
  logic       main_ic_cl_wrap, shadow_ic_cl_wrap;

  assign main_ic_rd_en_no_dbg =
      delayed_main_core_outputs.ic_rd_en &&
      !(|delayed_main_core_outputs.ic_wr_en) &&
      !(delayed_main_core_outputs.ic_debug_rd_en ||
        delayed_main_core_outputs.ic_debug_wr_en);
  assign shadow_ic_rd_en_no_dbg =
      shadow_core_outputs.ic_rd_en &&
      !(|shadow_core_outputs.ic_wr_en) &&
      !(shadow_core_outputs.ic_debug_rd_en ||
        shadow_core_outputs.ic_debug_wr_en);

  assign main_ic_cl_wrap =
      (delayed_main_core_outputs.ic_rw_addr[pt.ICACHE_TAG_INDEX_LO-1:pt.ICACHE_BANK_LO] ==
       {(pt.ICACHE_TAG_INDEX_LO - pt.ICACHE_BANK_LO){1'b1}});
  assign shadow_ic_cl_wrap =
      (shadow_core_outputs.ic_rw_addr[pt.ICACHE_TAG_INDEX_LO-1:pt.ICACHE_BANK_LO] ==
       {(pt.ICACHE_TAG_INDEX_LO - pt.ICACHE_BANK_LO){1'b1}});

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      main_ic_rd_bank_sel_f   <= 1'b0;
      main_ic_rd_rot_sel_f    <= 2'b00;
      main_ic_cl_wrap_f       <= 1'b0;
      main_ic_up_chk_en_f     <= 1'b0;
      shadow_ic_rd_bank_sel_f <= 1'b0;
      shadow_ic_rd_rot_sel_f  <= 2'b00;
      shadow_ic_cl_wrap_f     <= 1'b0;
      shadow_ic_up_chk_en_f   <= 1'b0;
    end else begin
      {main_ic_rd_bank_sel_f, main_ic_rd_rot_sel_f} <=
          (delayed_main_core_outputs.ic_debug_rd_en ||
           delayed_main_core_outputs.ic_debug_wr_en) ?
          {delayed_main_core_outputs.ic_debug_addr[pt.ICACHE_BANK_HI], 2'b00} :
          delayed_main_core_outputs.ic_rw_addr[pt.ICACHE_BANK_HI:1];

      {shadow_ic_rd_bank_sel_f, shadow_ic_rd_rot_sel_f} <=
          (shadow_core_outputs.ic_debug_rd_en ||
           shadow_core_outputs.ic_debug_wr_en) ?
          {shadow_core_outputs.ic_debug_addr[pt.ICACHE_BANK_HI], 2'b00} :
          shadow_core_outputs.ic_rw_addr[pt.ICACHE_BANK_HI:1];

      main_ic_cl_wrap_f   <= main_ic_rd_en_no_dbg &&
                             (delayed_main_core_outputs.ic_rw_addr[2:1] == 2'b11) &&
                             main_ic_cl_wrap;
      main_ic_up_chk_en_f <= main_ic_rd_en_no_dbg &&
                             (delayed_main_core_outputs.ic_rw_addr[2:1] == 2'b11) &&
                             !main_ic_cl_wrap;

      shadow_ic_cl_wrap_f   <= shadow_ic_rd_en_no_dbg &&
                               (shadow_core_outputs.ic_rw_addr[2:1] == 2'b11) &&
                               shadow_ic_cl_wrap;
      shadow_ic_up_chk_en_f <= shadow_ic_rd_en_no_dbg &&
                               (shadow_core_outputs.ic_rw_addr[2:1] == 2'b11) &&
                               !shadow_ic_cl_wrap;
    end
  end

  // Asserts when DCLS catches divergence in core-side ICache read controls (PR #571)
  assign icache_dcls_ctrl_divergence = mubi_check_true(corruption_detected_o) && (
      (main_ic_rd_bank_sel_f != shadow_ic_rd_bank_sel_f) ||
      (main_ic_rd_rot_sel_f != shadow_ic_rd_rot_sel_f) ||
      (main_ic_up_chk_en_f != shadow_ic_up_chk_en_f) ||
      (main_ic_cl_wrap_f != shadow_ic_cl_wrap_f)
  );

`ifndef VERILATOR
  // -------------------------------------------------------------------------
  // VCS / IEEE 1800 Covergroup: Memory Address XOR Infection Coverage
  // -------------------------------------------------------------------------
  covergroup el2_veer_lockstep_address_xor_infection_cov @(posedge clk iff rst_n);
    option.per_instance = 1;

    // 1. Coverpoint iccm_xor_infection_cp:
    // - iccm_xor_active: ICCM_ADDR_XOR == 1 with ICCM ECC or address/data fault active
    // - iccm_mismatch_detected: Subordinate core ICCM divergence triggers DCLS mismatch
    iccm_xor_infection_cp: coverpoint iccm_xor_infection_cats {
      wildcard bins iccm_xor_active        = {2'b?1};
      wildcard bins iccm_mismatch_detected = {2'b1?};
    }

    // 2. Coverpoint dccm_xor_infection_cp:
    // - dccm_xor_active: DCCM_ADDR_XOR == 1 with DCCM ECC/readback or address/data fault active
    // - dccm_mismatch_detected: Subordinate core DCCM divergence triggers DCLS mismatch
    dccm_xor_infection_cp: coverpoint dccm_xor_infection_cats {
      wildcard bins dccm_xor_active        = {2'b?1};
      wildcard bins dccm_mismatch_detected = {2'b1?};
    }

    // 3. Coverpoint icache_xor_infection_cp:
    // - icache_xor_active: ICACHE_ADDR_XOR == 1 with ICache parity/ECC or address/data fault
    // - icache_mismatch_detected: Subordinate core ICache divergence triggers DCLS mismatch
    icache_xor_infection_cp: coverpoint icache_xor_infection_cats {
      wildcard bins icache_xor_active        = {2'b?1};
      wildcard bins icache_mismatch_detected = {2'b1?};
    }

    // 4. Coverpoint iccm_rd_data_divergence_cp:
    // Monitors DCLS-domain F-stage iccm_rd_data / read-ECC divergence
    iccm_rd_data_divergence_cp: coverpoint iccm_rd_data_divergence {
      bins iccm_rd_data_divergence_caught = {1'b1};
    }

    // 5. Issue #550 (PR #552): ICCM DMA read word-enable & clean reads with Address-XOR
    iccm_dma_rd_xor_cp: coverpoint {
        iccm_dma_rd_dword_f2,
        iccm_dma_rd_odd_word_f2,
        iccm_ecc_double_error
    } iff (IccmAddrXor && iccm_dma_rd_valid_f2) {
      bins          dma_rd_word_even_no_false_err = {3'b0_0_0};
      bins          dma_rd_word_odd_no_false_err  = {3'b0_1_0};
      wildcard bins dma_rd_dword_both_en          = {3'b1_?_?};
    }

    // 6. Issue #562 (PR #565): ICCM redundant row lane select on ECC correction with Address-XOR
    iccm_redundant_row_xor_corr_cp: coverpoint iccm_rw_addr[2]
        iff (IccmAddrXor && iccm_buf_correct_ecc) {
      bins corr_even_word_lane0 = {1'b0};
      bins corr_odd_word_lane1  = {1'b1};
    }

    iccm_redundant_row_xor_reread_cp: coverpoint {
        iccm_redundant_reread_odd_clean,
        iccm_redundant_reread_even_clean
    } iff (IccmAddrXor &&
           (iccm_redundant_reread_even_clean || iccm_redundant_reread_odd_clean)) {
      wildcard bins reread_even_redundant_clean = {2'b?1};
      wildcard bins reread_odd_redundant_clean  = {2'b1?};
    }

    // 7. Issue #569 (PR #571): DCLS-internal ICache bank select, CL-wrap masking, & divergence
    icache_dcls_bank_sel_xor_cp: coverpoint main_ic_rd_bank_sel_f
        iff (IcacheAddrXor && (|ic_rd_hit)) {
      bins lower_chunk_in_bank0 = {1'b0};
      bins lower_chunk_in_bank1 = {1'b1};
    }

    icache_dcls_cl_wrap_straddle_cp: coverpoint {main_ic_cl_wrap_f, main_ic_up_chk_en_f}
        iff ((|ic_rd_hit) && (main_ic_rd_rot_sel_f == 2'b11)) {
      bins straddle_intra_line_both_checked = {2'b01};
      bins straddle_cl_wrap_upper_dropped   = {2'b10};
    }

    icache_dcls_ctrl_divergence_cp: coverpoint icache_dcls_ctrl_divergence {
      bins dcls_icache_ctrl_mismatch_caught = {1'b1};
    }
  endgroup

  initial begin
    el2_veer_lockstep_address_xor_infection_cov
        el2_veer_lockstep_address_xor_infection_cov_cg = new();
    $display("Lockstep address XOR infection coverage interface created");
  end
`else
  // -------------------------------------------------------------------------
  // Functional Coverage for Verilator via SystemVerilog Assertions (`cover property`)
  // -------------------------------------------------------------------------

  // 1. ICCM address XOR infection coverpoints (iccm_xor_infection_cp)
  cov_iccm_xor_active: cover property (@(posedge clk) disable iff (!rst_n)
      iccm_xor_active);
  cov_iccm_mismatch_detected: cover property (@(posedge clk) disable iff (!rst_n)
      iccm_mismatch_detected);

  // 2. DCCM address XOR infection coverpoints (dccm_xor_infection_cp)
  cov_dccm_xor_active: cover property (@(posedge clk) disable iff (!rst_n)
      dccm_xor_active);
  cov_dccm_mismatch_detected: cover property (@(posedge clk) disable iff (!rst_n)
      dccm_mismatch_detected);

  // 3. ICache address XOR infection coverpoints (icache_xor_infection_cp)
  cov_icache_xor_active: cover property (@(posedge clk) disable iff (!rst_n)
      icache_xor_active);
  cov_icache_mismatch_detected: cover property (@(posedge clk) disable iff (!rst_n)
      icache_mismatch_detected);

  // 4. DCLS-domain ICCM read data divergence coverpoint (iccm_rd_data_divergence_cp)
  cov_iccm_rd_data_divergence_caught: cover property (@(posedge clk) disable iff (!rst_n)
      iccm_rd_data_divergence);

  // 5. Issue #550 (PR #552): ICCM DMA read with Address-XOR SVA coverpoints
  cov_iccm_dma_rd_word_even_no_false_err: cover property (@(posedge clk) disable iff (!rst_n)
      IccmAddrXor && iccm_dma_rd_valid_f2 && !iccm_dma_rd_dword_f2 &&
      !iccm_dma_rd_odd_word_f2 && !iccm_ecc_double_error);
  cov_iccm_dma_rd_word_odd_no_false_err: cover property (@(posedge clk) disable iff (!rst_n)
      IccmAddrXor && iccm_dma_rd_valid_f2 && !iccm_dma_rd_dword_f2 &&
      iccm_dma_rd_odd_word_f2 && !iccm_ecc_double_error);
  cov_iccm_dma_rd_dword_both_en: cover property (@(posedge clk) disable iff (!rst_n)
      IccmAddrXor && iccm_dma_rd_valid_f2 && iccm_dma_rd_dword_f2);

  // 6. Issue #562 (PR #565): ICCM redundant row lane select on ECC correction with Address-XOR
  cov_iccm_corr_even_word_lane0: cover property (@(posedge clk) disable iff (!rst_n)
      IccmAddrXor && iccm_buf_correct_ecc && (iccm_rw_addr[2] == 1'b0));
  cov_iccm_corr_odd_word_lane1: cover property (@(posedge clk) disable iff (!rst_n)
      IccmAddrXor && iccm_buf_correct_ecc && (iccm_rw_addr[2] == 1'b1));
  cov_iccm_reread_even_redundant_clean: cover property (@(posedge clk) disable iff (!rst_n)
      iccm_redundant_reread_even_clean);
  cov_iccm_reread_odd_redundant_clean: cover property (@(posedge clk) disable iff (!rst_n)
      iccm_redundant_reread_odd_clean);

  // 7. Issue #569 (PR #571): DCLS-internal ICache bank select, CL wrap straddle, & divergence
  cov_icache_dcls_bank_sel_0: cover property (@(posedge clk) disable iff (!rst_n)
      IcacheAddrXor && (|ic_rd_hit) && (main_ic_rd_bank_sel_f == 1'b0));
  cov_icache_dcls_bank_sel_1: cover property (@(posedge clk) disable iff (!rst_n)
      IcacheAddrXor && (|ic_rd_hit) && (main_ic_rd_bank_sel_f == 1'b1));
  cov_icache_straddle_intra_line_both_checked: cover property (@(posedge clk) disable iff (!rst_n)
      (|ic_rd_hit) && (main_ic_rd_rot_sel_f == 2'b11) &&
      !main_ic_cl_wrap_f && main_ic_up_chk_en_f);
  cov_icache_straddle_cl_wrap_upper_dropped: cover property (@(posedge clk) disable iff (!rst_n)
      (|ic_rd_hit) && (main_ic_rd_rot_sel_f == 2'b11) &&
      main_ic_cl_wrap_f && !main_ic_up_chk_en_f);
  cov_icache_dcls_ctrl_mismatch_caught: cover property (@(posedge clk) disable iff (!rst_n)
      icache_dcls_ctrl_divergence);

  initial begin
    $display("Lockstep address XOR infection coverage interface created (Verilator SVA mode)");
  end
`endif

endinterface : el2_veer_lockstep_address_xor_infection_cov_if
