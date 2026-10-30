/* SPDX-License-Identifier: Apache-2.0
 * Copyright 2026 Google LLC
 *
 * Multi-Memory Core RAS ECC Threshold Alerts Functional Coverage Interface (Task 7)
 * Author: Samip Modi (samipmodi@google.com)
 *
 * Description:
 * Dual-simulator functional coverage interface bound into `el2_dec_tlu_ctl` for
 * Synopsys VCS (`covergroup`) and Verilator (SVA `cover property`).
 *
 * Covers:
 * 1. `MDCCMECT` (CSR 0x7F2 - DCCM):
 *    - `dccm_threshold_values_cp` (threshold exponents 0, 1, 2, 4, 8, 16, 26)
 *    - `dccm_counter_increment_cp` (single-bit ECC error increments counter by 1)
 *    - `dccm_counter_comparison_cp` (`count_below_thresh`, `count_at_thresh`, `count_above_thresh`)
 * 2. `MICCMECT` (CSR 0x7F1 - ICCM):
 *    - `iccm_threshold_values_cp` (threshold exponents 0, 1, 2, 4, 8, 16, 26)
 *    - `iccm_counter_increment_cp` (instruction fetch SBE and DMA read SBE counter increments)
 *    - `iccm_threshold_trigger_cp` (`count_below_thresh`, `count_at_thresh`, `count_above_thresh`)
 * 3. `MICECT` (CSR 0x7F0 - ICache):
 *    - `icache_threshold_values_cp` (threshold exponents 0, 1, 2, 4, 8, 16, 26)
 *    - `icache_counter_increment_cp` (cache fetch parity/ECC SBE counter increment)
 *    - `icache_threshold_trigger_cp` (`count_below_thresh`, `count_at_thresh`, `count_above_thresh`)
 * 4. `core_ecc_interrupt_generation_cp`:
 *    - `interrupt_masked` (`ce_int == 1` with `mie[30]` / internal `mie[5]` == 0, or `mstatus.MIE == 0`)
 *    - `interrupt_taken` (`take_ce_int` trap with `mcause == 0x8000001e`)
 */

interface el2_core_ecc_threshold_cov_if #(
    `include "el2_param.vh"
) (
    input logic        free_clk,
    input logic        rst_l,
    input logic [31:0] mdccmect,
    input logic [31:0] miccmect,
    input logic [31:0] micect,
    input logic        wr_mdccmect_r,
    input logic        wr_miccmect_r,
    input logic        wr_micect_r,
    input logic        lsu_single_ecc_error_r_d1,
    input logic        iccm_sbecc_r,
    input logic        iccm_dma_sb_error,
    input logic        ic_perr_r,
    input logic        mdccme_ce_req,
    input logic        miccme_ce_req,
    input logic        mice_ce_req,
    input logic        ce_int,
    input logic [ 5:0] mie,
    input logic        mstatus_mie_ns,
    input logic        take_ce_int,
    input logic [31:0] mcause
);

  // Extract 5-bit threshold exponent [31:27] and 27-bit counter [26:0] for each CSR
  logic [ 4:0] dccm_thresh_exp;
  logic [26:0] dccm_count;
  logic [26:0] dccm_thresh_val;

  logic [ 4:0] iccm_thresh_exp;
  logic [26:0] iccm_count;
  logic [26:0] iccm_thresh_val;

  logic [ 4:0] icache_thresh_exp;
  logic [26:0] icache_count;
  logic [26:0] icache_thresh_val;

  assign dccm_thresh_exp   = mdccmect[31:27];
  assign dccm_count        = mdccmect[26:0];
  assign dccm_thresh_val   = 27'd1 << mdccmect[31:27];

  assign iccm_thresh_exp   = miccmect[31:27];
  assign iccm_count        = miccmect[26:0];
  assign iccm_thresh_val   = 27'd1 << miccmect[31:27];

  assign icache_thresh_exp = micect[31:27];
  assign icache_count      = micect[26:0];
  assign icache_thresh_val = 27'd1 << micect[31:27];

  // Single-bit error counter increment events (excluding simultaneous CSR overwrite)
  logic dccm_sbe_incr;
  logic iccm_fetch_sbe_incr;
  logic iccm_dma_sbe_incr;
  logic icache_sbe_incr;

  assign dccm_sbe_incr       = lsu_single_ecc_error_r_d1 & ~wr_mdccmect_r;
  assign iccm_fetch_sbe_incr = iccm_sbecc_r & ~wr_miccmect_r;
  assign iccm_dma_sbe_incr   = iccm_dma_sb_error & ~wr_miccmect_r;
  assign icache_sbe_incr     = ic_perr_r & ~wr_micect_r;

  logic [1:0] iccm_incr_type;
  always_comb begin
    if (iccm_fetch_sbe_incr) begin
      iccm_incr_type = 2'd1;
    end else if (iccm_dma_sbe_incr) begin
      iccm_incr_type = 2'd2;
    end else begin
      iccm_incr_type = 2'd0;
    end
  end

  // Counter comparison encodings:
  // 2'd0 = idle (count == 0 and no alert)
  // 2'd1 = count_below_thresh: (count > 0) && (count < (1 << thresh)) && !ce_req
  // 2'd2 = count_at_thresh:    (count == (1 << thresh)) && ce_req
  // 2'd3 = count_above_thresh: (count > (1 << thresh)) && ce_req
  logic [1:0] dccm_cmp_state;
  logic [1:0] iccm_cmp_state;
  logic [1:0] icache_cmp_state;

  always_comb begin
    if (mdccme_ce_req && (dccm_count == dccm_thresh_val)) begin
      dccm_cmp_state = 2'd2;
    end else if (mdccme_ce_req && (dccm_count > dccm_thresh_val)) begin
      dccm_cmp_state = 2'd3;
    end else if (!mdccme_ce_req && (dccm_count > 27'd0) && (dccm_count < dccm_thresh_val)) begin
      dccm_cmp_state = 2'd1;
    end else begin
      dccm_cmp_state = 2'd0;
    end
  end

  always_comb begin
    if (miccme_ce_req && (iccm_count == iccm_thresh_val)) begin
      iccm_cmp_state = 2'd2;
    end else if (miccme_ce_req && (iccm_count > iccm_thresh_val)) begin
      iccm_cmp_state = 2'd3;
    end else if (!miccme_ce_req && (iccm_count > 27'd0) && (iccm_count < iccm_thresh_val)) begin
      iccm_cmp_state = 2'd1;
    end else begin
      iccm_cmp_state = 2'd0;
    end
  end

  always_comb begin
    if (mice_ce_req && (icache_count == icache_thresh_val)) begin
      icache_cmp_state = 2'd2;
    end else if (mice_ce_req && (icache_count > icache_thresh_val)) begin
      icache_cmp_state = 2'd3;
    end else if (!mice_ce_req && (icache_count > 27'd0) && (icache_count < icache_thresh_val)) begin
      icache_cmp_state = 2'd1;
    end else begin
      icache_cmp_state = 2'd0;
    end
  end

  // Core ECC interrupt generation bitmask (`mie[5]` is `MIE_MCEIE`, corresponding to `mie[30]`):
  // Bit 0: `interrupt_masked` (`ce_int` asserted while `mie[30] == 0` or `mstatus.MIE == 0`)
  // Bit 1: `interrupt_taken` (`take_ce_int` trap taken and `mcause` updated to `0x8000001e`)
  logic       ce_int_masked;
  logic       ce_int_taken;
  logic       take_ce_int_q;
  logic [1:0] ce_int_gen_vec;

  always_ff @(posedge free_clk or negedge rst_l) begin
    if (!rst_l) begin
      take_ce_int_q <= 1'b0;
    end else begin
      take_ce_int_q <= take_ce_int;
    end
  end

  assign ce_int_masked  = ce_int & (~mie[5] | ~mstatus_mie_ns);
  assign ce_int_taken   = take_ce_int_q & (mcause == 32'h8000_001e);
  assign ce_int_gen_vec = {ce_int_taken, ce_int_masked};

`ifndef VERILATOR
  // ---------------------------------------------------------------------------
  // Synopsys VCS / IEEE 1800 Covergroup: Multi-Memory Core RAS ECC Thresholds
  // ---------------------------------------------------------------------------
  covergroup el2_core_ecc_threshold_cov @(posedge free_clk iff rst_l);
    type_option.merge_instances = 1;

    // 1. MDCCMECT (CSR 0x7F2 - DCCM) Coverpoints
    dccm_threshold_values_cp: coverpoint dccm_thresh_exp {
      bins thresh_0  = {5'd0};
      bins thresh_1  = {5'd1};
      bins thresh_2  = {5'd2};
      bins thresh_4  = {5'd4};
      bins thresh_8  = {5'd8};
      bins thresh_16 = {5'd16};
      bins thresh_26 = {5'd26};
    }

    dccm_counter_increment_cp: coverpoint dccm_sbe_incr {
      bins sbe_incr = {1'b1};
    }

    dccm_counter_comparison_cp: coverpoint dccm_cmp_state {
      bins count_below_thresh = {2'd1};
      bins count_at_thresh    = {2'd2};
      bins count_above_thresh = {2'd3};
    }

    // 2. MICCMECT (CSR 0x7F1 - ICCM) Coverpoints
    iccm_threshold_values_cp: coverpoint iccm_thresh_exp {
      bins thresh_0  = {5'd0};
      bins thresh_1  = {5'd1};
      bins thresh_2  = {5'd2};
      bins thresh_4  = {5'd4};
      bins thresh_8  = {5'd8};
      bins thresh_16 = {5'd16};
      bins thresh_26 = {5'd26};
    }

    iccm_counter_increment_cp: coverpoint iccm_incr_type {
      bins fetch_sbe_incr = {2'd1};
      bins dma_sbe_incr   = {2'd2};
    }

    iccm_threshold_trigger_cp: coverpoint iccm_cmp_state {
      bins count_below_thresh = {2'd1};
      bins count_at_thresh    = {2'd2};
      bins count_above_thresh = {2'd3};
    }

    // 3. MICECT (CSR 0x7F0 - ICache) Coverpoints
    icache_threshold_values_cp: coverpoint icache_thresh_exp {
      bins thresh_0  = {5'd0};
      bins thresh_1  = {5'd1};
      bins thresh_2  = {5'd2};
      bins thresh_4  = {5'd4};
      bins thresh_8  = {5'd8};
      bins thresh_16 = {5'd16};
      bins thresh_26 = {5'd26};
    }

    icache_counter_increment_cp: coverpoint icache_sbe_incr {
      bins sbe_incr = {1'b1};
    }

    icache_threshold_trigger_cp: coverpoint icache_cmp_state {
      bins count_below_thresh = {2'd1};
      bins count_at_thresh    = {2'd2};
      bins count_above_thresh = {2'd3};
    }

    // 4. Core ECC Interrupt Generation (CSR mie[30] / internal mie[5] & mcause == 0x8000001e)
    core_ecc_interrupt_generation_cp: coverpoint ce_int_gen_vec {
      wildcard bins interrupt_masked = {2'b?1};
      wildcard bins interrupt_taken  = {2'b1?};
    }
  endgroup

  initial begin
    el2_core_ecc_threshold_cov cov_inst = new();
  end
`else
  // ---------------------------------------------------------------------------
  // Functional Coverage for Verilator via SVA `cover property`
  // ---------------------------------------------------------------------------

  // 1. MDCCMECT (0x7F2 - DCCM)
  cov_dccm_thresh_0: cover property (@(posedge free_clk) disable iff (!rst_l)
      dccm_thresh_exp == 5'd0);
  cov_dccm_thresh_1: cover property (@(posedge free_clk) disable iff (!rst_l)
      dccm_thresh_exp == 5'd1);
  cov_dccm_thresh_2: cover property (@(posedge free_clk) disable iff (!rst_l)
      dccm_thresh_exp == 5'd2);
  cov_dccm_thresh_4: cover property (@(posedge free_clk) disable iff (!rst_l)
      dccm_thresh_exp == 5'd4);
  cov_dccm_thresh_8: cover property (@(posedge free_clk) disable iff (!rst_l)
      dccm_thresh_exp == 5'd8);
  cov_dccm_thresh_16: cover property (@(posedge free_clk) disable iff (!rst_l)
      dccm_thresh_exp == 5'd16);
  cov_dccm_thresh_26: cover property (@(posedge free_clk) disable iff (!rst_l)
      dccm_thresh_exp == 5'd26);

  cov_dccm_counter_sbe_incr: cover property (@(posedge free_clk) disable iff (!rst_l)
      dccm_sbe_incr);
  cov_dccm_count_below_thresh: cover property (@(posedge free_clk) disable iff (!rst_l)
      dccm_cmp_state == 2'd1);
  cov_dccm_count_at_thresh: cover property (@(posedge free_clk) disable iff (!rst_l)
      dccm_cmp_state == 2'd2);
  cov_dccm_count_above_thresh: cover property (@(posedge free_clk) disable iff (!rst_l)
      dccm_cmp_state == 2'd3);

  // 2. MICCMECT (0x7F1 - ICCM)
  cov_iccm_thresh_0: cover property (@(posedge free_clk) disable iff (!rst_l)
      iccm_thresh_exp == 5'd0);
  cov_iccm_thresh_1: cover property (@(posedge free_clk) disable iff (!rst_l)
      iccm_thresh_exp == 5'd1);
  cov_iccm_thresh_2: cover property (@(posedge free_clk) disable iff (!rst_l)
      iccm_thresh_exp == 5'd2);
  cov_iccm_thresh_4: cover property (@(posedge free_clk) disable iff (!rst_l)
      iccm_thresh_exp == 5'd4);
  cov_iccm_thresh_8: cover property (@(posedge free_clk) disable iff (!rst_l)
      iccm_thresh_exp == 5'd8);
  cov_iccm_thresh_16: cover property (@(posedge free_clk) disable iff (!rst_l)
      iccm_thresh_exp == 5'd16);
  cov_iccm_thresh_26: cover property (@(posedge free_clk) disable iff (!rst_l)
      iccm_thresh_exp == 5'd26);

  cov_iccm_counter_fetch_sbe_incr: cover property (@(posedge free_clk) disable iff (!rst_l)
      iccm_fetch_sbe_incr);
  cov_iccm_counter_dma_sbe_incr: cover property (@(posedge free_clk) disable iff (!rst_l)
      iccm_dma_sbe_incr);
  cov_iccm_count_below_thresh: cover property (@(posedge free_clk) disable iff (!rst_l)
      iccm_cmp_state == 2'd1);
  cov_iccm_count_at_thresh: cover property (@(posedge free_clk) disable iff (!rst_l)
      iccm_cmp_state == 2'd2);
  cov_iccm_count_above_thresh: cover property (@(posedge free_clk) disable iff (!rst_l)
      iccm_cmp_state == 2'd3);

  // 3. MICECT (0x7F0 - ICache)
  cov_icache_thresh_0: cover property (@(posedge free_clk) disable iff (!rst_l)
      icache_thresh_exp == 5'd0);
  cov_icache_thresh_1: cover property (@(posedge free_clk) disable iff (!rst_l)
      icache_thresh_exp == 5'd1);
  cov_icache_thresh_2: cover property (@(posedge free_clk) disable iff (!rst_l)
      icache_thresh_exp == 5'd2);
  cov_icache_thresh_4: cover property (@(posedge free_clk) disable iff (!rst_l)
      icache_thresh_exp == 5'd4);
  cov_icache_thresh_8: cover property (@(posedge free_clk) disable iff (!rst_l)
      icache_thresh_exp == 5'd8);
  cov_icache_thresh_16: cover property (@(posedge free_clk) disable iff (!rst_l)
      icache_thresh_exp == 5'd16);
  cov_icache_thresh_26: cover property (@(posedge free_clk) disable iff (!rst_l)
      icache_thresh_exp == 5'd26);

  cov_icache_counter_sbe_incr: cover property (@(posedge free_clk) disable iff (!rst_l)
      icache_sbe_incr);
  cov_icache_count_below_thresh: cover property (@(posedge free_clk) disable iff (!rst_l)
      icache_cmp_state == 2'd1);
  cov_icache_count_at_thresh: cover property (@(posedge free_clk) disable iff (!rst_l)
      icache_cmp_state == 2'd2);
  cov_icache_count_above_thresh: cover property (@(posedge free_clk) disable iff (!rst_l)
      icache_cmp_state == 2'd3);

  // 4. Core ECC Interrupt Generation
  cov_core_ecc_interrupt_masked: cover property (@(posedge free_clk) disable iff (!rst_l)
      ce_int_masked);
  cov_core_ecc_interrupt_taken: cover property (@(posedge free_clk) disable iff (!rst_l)
      ce_int_taken);
`endif

endinterface
