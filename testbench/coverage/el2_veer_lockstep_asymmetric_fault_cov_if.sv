/* SPDX-License-Identifier: Apache-2.0
 * Copyright 2026 Google LLC
 *
 * DCLS Asymmetric Shadow Core Fault Divergence Functional Coverage Interface (Task 8)
 * Author: Samip Modi (samipmodi@google.com)
 *
 * Description:
 * Dual-simulator functional coverage interface bound into `el2_veer_wrapper` for
 * Synopsys VCS (`covergroup`) and Verilator (SVA `cover property`).
 *
 * Covers:
 * 1. `asymmetric_fault_source_cp`:
 *    - `dccm_asymmetric`: Asymmetric DCCM threshold alert active (`mdccmect` mismatch, Case 203).
 *    - `iccm_asymmetric`: Asymmetric ICCM threshold alert active (`miccmect` mismatch, Case 204).
 *    - `icache_asymmetric`: Asymmetric ICache threshold alert active (`micect` mismatch, Case 205).
 * 2. `asymmetric_lockstep_response_cp`:
 *    - `comparator_mismatch`: Subordinate alert causes execution/regfile divergence and asserts
 *      `corruption_detected_o == El2MuBiTrue`.
 *    - `external_interrupt_fired`: Lockstep mismatch interrupt signals to PIC (`extintsrc_req[2]`).
 * 3. `lockstep_delay_cp`:
 *    - Configured lockstep pipeline delay (`delay_0` through `delay_4`) during asymmetric fault detection.
 * 4. `asymmetric_source_x_delay_cross`:
 *    - Crosses `asymmetric_fault_source_cp` with `lockstep_delay_cp` (Delays 0 to 4).
 */

interface el2_veer_lockstep_asymmetric_fault_cov_if
  import el2_mubi_pkg::*;
#(
    `include "el2_param.vh"
) (
    input logic                           clk,
    input logic                           rst_n,
`ifdef RV_LOCKSTEP_REGFILE_ENABLE
    input logic                           regfile_corrupted,
`endif
    input logic                           outputs_corrupted,
    input el2_mubi_t                      corruption_detected_o,
    input logic [pt.PIC_TOTAL_INT:1]      extintsrc_req,
    input logic                           main_mdccme_ce_req,
    input logic                           main_miccme_ce_req,
    input logic                           main_mice_ce_req,
    input logic                           shadow_mdccme_ce_req,
    input logic                           shadow_miccme_ce_req,
    input logic                           shadow_mice_ce_req
);

  localparam int unsigned LockstepDelay = 32'(pt.LOCKSTEP_DELAY);
  logic delayed_main_mdccme_ce_req;
  logic delayed_main_miccme_ce_req;
  logic delayed_main_mice_ce_req;

  generate
    if (LockstepDelay == 0) begin : gen_no_ce_delay
      assign delayed_main_mdccme_ce_req = main_mdccme_ce_req;
      assign delayed_main_miccme_ce_req = main_miccme_ce_req;
      assign delayed_main_mice_ce_req   = main_mice_ce_req;
    end else if (LockstepDelay == 1) begin : gen_ce_delay_1
      always_ff @(posedge clk) begin
        if (!rst_n) begin
          delayed_main_mdccme_ce_req <= 1'b0;
          delayed_main_miccme_ce_req <= 1'b0;
          delayed_main_mice_ce_req   <= 1'b0;
        end else begin
          delayed_main_mdccme_ce_req <= main_mdccme_ce_req;
          delayed_main_miccme_ce_req <= main_miccme_ce_req;
          delayed_main_mice_ce_req   <= main_mice_ce_req;
        end
      end
    end else begin : gen_ce_delay_n
      logic [LockstepDelay-1:0] mdccme_sr, miccme_sr, mice_sr;
      always_ff @(posedge clk) begin
        if (!rst_n) begin
          mdccme_sr <= '0;
          miccme_sr <= '0;
          mice_sr   <= '0;
        end else begin
          mdccme_sr <= {mdccme_sr[LockstepDelay-2:0], main_mdccme_ce_req};
          miccme_sr <= {miccme_sr[LockstepDelay-2:0], main_miccme_ce_req};
          mice_sr   <= {mice_sr[LockstepDelay-2:0],   main_mice_ce_req};
        end
      end
      assign delayed_main_mdccme_ce_req = mdccme_sr[LockstepDelay-1];
      assign delayed_main_miccme_ce_req = miccme_sr[LockstepDelay-1];
      assign delayed_main_mice_ce_req   = mice_sr[LockstepDelay-1];
    end
  endgenerate

  logic datapath_divergence;
  assign datapath_divergence = outputs_corrupted
`ifdef RV_LOCKSTEP_REGFILE_ENABLE
                             | regfile_corrupted
`endif
                             ;

  // Encode asymmetric core ECC threshold alert source (shadow vs delay-aligned main):
  // 2'd0 = none / symmetric
  // 2'd1 = dccm_asymmetric   (`shadow_mdccme_ce_req ^ delayed_main_mdccme_ce_req`)
  // 2'd2 = iccm_asymmetric   (`shadow_miccme_ce_req ^ delayed_main_miccme_ce_req`)
  // 2'd3 = icache_asymmetric (`shadow_mice_ce_req   ^ delayed_main_mice_ce_req`)
  logic [1:0] asym_fault_source;
  always_comb begin
    if (shadow_mdccme_ce_req ^ delayed_main_mdccme_ce_req) begin
      asym_fault_source = 2'd1;
    end else if (shadow_miccme_ce_req ^ delayed_main_miccme_ce_req) begin
      asym_fault_source = 2'd2;
    end else if (shadow_mice_ce_req ^ delayed_main_mice_ce_req) begin
      asym_fault_source = 2'd3;
    end else begin
      asym_fault_source = 2'd0;
    end
  end

  logic asym_fault_active;
  assign asym_fault_active = (asym_fault_source != 2'd0) & datapath_divergence;

  // Track DCLS lockstep response while an asymmetric shadow core fault is active:
  // Bit 0: `comparator_mismatch` (`datapath_divergence` and `corruption_detected_o == El2MuBiTrue`)
  // Bit 1: `external_interrupt_fired` (PIC lockstep mismatch interrupt `extintsrc_req[2]` asserted)
  logic       comparator_mismatch_evt;
  logic       comparator_mismatch_q;
  logic [1:0] asym_fault_source_q;
  logic       ext_interrupt_fired_evt;
  logic       lockstep_ext_int_req;

  logic unused_extintsrc_req;
  assign unused_extintsrc_req = |extintsrc_req;

  generate
    if (pt.PIC_TOTAL_INT >= 2) begin : gen_pic_ext_int
      assign lockstep_ext_int_req = extintsrc_req[2];
    end else begin : gen_no_pic_ext_int
      assign lockstep_ext_int_req = 1'b0;
    end
  endgenerate

  assign comparator_mismatch_evt = asym_fault_active & datapath_divergence &
                                   mubi_check_true(corruption_detected_o);

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      comparator_mismatch_q <= 1'b0;
      asym_fault_source_q   <= 2'd0;
    end else begin
      comparator_mismatch_q <= comparator_mismatch_evt;
      asym_fault_source_q   <= asym_fault_source;
    end
  end

  assign ext_interrupt_fired_evt = (comparator_mismatch_evt | comparator_mismatch_q) &
                                   lockstep_ext_int_req;

`ifndef VERILATOR
  logic [1:0] asym_response_vec;
  logic [1:0] cov_asym_fault_source;
  logic       cov_sample_en;

  assign asym_response_vec     = {ext_interrupt_fired_evt, comparator_mismatch_evt};
  assign cov_asym_fault_source = comparator_mismatch_evt ? asym_fault_source : asym_fault_source_q;
  assign cov_sample_en         = comparator_mismatch_evt | ext_interrupt_fired_evt;

  // ---------------------------------------------------------------------------
  // Synopsys VCS / IEEE 1800 Covergroup: DCLS Asymmetric Shadow Core Faults
  // ---------------------------------------------------------------------------
  covergroup el2_veer_lockstep_asymmetric_fault_cov @(
      posedge clk iff (rst_n & cov_sample_en)
  );
    type_option.merge_instances = 1;

    // 1. Asymmetric fault source on shadow core
    asymmetric_fault_source_cp: coverpoint cov_asym_fault_source {
      bins dccm_asymmetric   = {2'd1};
      bins iccm_asymmetric   = {2'd2};
      bins icache_asymmetric = {2'd3};
    }

    // 2. DCLS comparator mismatch and PIC external interrupt response
    asymmetric_lockstep_response_cp: coverpoint asym_response_vec {
      wildcard bins comparator_mismatch      = {2'b?1};
      wildcard bins external_interrupt_fired = {2'b1?};
    }

    // 3. Configured lockstep pipeline delay (0 to 4)
    lockstep_delay_cp: coverpoint int'(pt.LOCKSTEP_DELAY) {
      bins delay_0 = {0};
      bins delay_1 = {1};
      bins delay_2 = {2};
      bins delay_3 = {3};
      bins delay_4 = {4};
    }

    // 4. Cross: Asymmetric fault source x Lockstep delay (0 to 4)
    asymmetric_source_x_delay_cross: cross asymmetric_fault_source_cp, lockstep_delay_cp;
  endgroup

  initial begin
    el2_veer_lockstep_asymmetric_fault_cov cov_inst = new();
  end
`else
  // ---------------------------------------------------------------------------
  // Functional Coverage for Verilator via SVA `cover property`
  // ---------------------------------------------------------------------------

  // 1. Asymmetric fault source coverpoints (asymmetric_fault_source_cp)
  cov_asym_source_dccm: cover property (@(posedge clk) disable iff (!rst_n)
      asym_fault_active && (asym_fault_source == 2'd1) && mubi_check_true(corruption_detected_o));
  cov_asym_source_iccm: cover property (@(posedge clk) disable iff (!rst_n)
      asym_fault_active && (asym_fault_source == 2'd2) && mubi_check_true(corruption_detected_o));
  cov_asym_source_icache: cover property (@(posedge clk) disable iff (!rst_n)
      asym_fault_active && (asym_fault_source == 2'd3) && mubi_check_true(corruption_detected_o));

  // 2. Asymmetric lockstep response coverpoints (asymmetric_lockstep_response_cp)
  cov_asym_resp_comparator_mismatch: cover property (@(posedge clk) disable iff (!rst_n)
      comparator_mismatch_evt);
  cov_asym_resp_external_interrupt_fired: cover property (@(posedge clk) disable iff (!rst_n)
      ext_interrupt_fired_evt);

  // 3. Configured lockstep pipeline delay (lockstep_delay_cp)
  cov_asym_lockstep_delay_0: cover property (@(posedge clk) disable iff (!rst_n)
      asym_fault_active && (pt.LOCKSTEP_DELAY == 0) && mubi_check_true(corruption_detected_o));
  cov_asym_lockstep_delay_1: cover property (@(posedge clk) disable iff (!rst_n)
      asym_fault_active && (pt.LOCKSTEP_DELAY == 1) && mubi_check_true(corruption_detected_o));
  cov_asym_lockstep_delay_2: cover property (@(posedge clk) disable iff (!rst_n)
      asym_fault_active && (pt.LOCKSTEP_DELAY == 2) && mubi_check_true(corruption_detected_o));
  cov_asym_lockstep_delay_3: cover property (@(posedge clk) disable iff (!rst_n)
      asym_fault_active && (pt.LOCKSTEP_DELAY == 3) && mubi_check_true(corruption_detected_o));
  cov_asym_lockstep_delay_4: cover property (@(posedge clk) disable iff (!rst_n)
      asym_fault_active && (pt.LOCKSTEP_DELAY == 4) && mubi_check_true(corruption_detected_o));

  // 4. Cross: asymmetric_fault_source_cp x lockstep_delay_cp (Delays 0 to 4)
  cov_asym_dccm_x_delay_0: cover property (@(posedge clk) disable iff (!rst_n)
      asym_fault_active && (asym_fault_source == 2'd1) && (pt.LOCKSTEP_DELAY == 0) && mubi_check_true(corruption_detected_o));
  cov_asym_dccm_x_delay_1: cover property (@(posedge clk) disable iff (!rst_n)
      asym_fault_active && (asym_fault_source == 2'd1) && (pt.LOCKSTEP_DELAY == 1) && mubi_check_true(corruption_detected_o));
  cov_asym_dccm_x_delay_2: cover property (@(posedge clk) disable iff (!rst_n)
      asym_fault_active && (asym_fault_source == 2'd1) && (pt.LOCKSTEP_DELAY == 2) && mubi_check_true(corruption_detected_o));
  cov_asym_dccm_x_delay_3: cover property (@(posedge clk) disable iff (!rst_n)
      asym_fault_active && (asym_fault_source == 2'd1) && (pt.LOCKSTEP_DELAY == 3) && mubi_check_true(corruption_detected_o));
  cov_asym_dccm_x_delay_4: cover property (@(posedge clk) disable iff (!rst_n)
      asym_fault_active && (asym_fault_source == 2'd1) && (pt.LOCKSTEP_DELAY == 4) && mubi_check_true(corruption_detected_o));

  cov_asym_iccm_x_delay_0: cover property (@(posedge clk) disable iff (!rst_n)
      asym_fault_active && (asym_fault_source == 2'd2) && (pt.LOCKSTEP_DELAY == 0) && mubi_check_true(corruption_detected_o));
  cov_asym_iccm_x_delay_1: cover property (@(posedge clk) disable iff (!rst_n)
      asym_fault_active && (asym_fault_source == 2'd2) && (pt.LOCKSTEP_DELAY == 1) && mubi_check_true(corruption_detected_o));
  cov_asym_iccm_x_delay_2: cover property (@(posedge clk) disable iff (!rst_n)
      asym_fault_active && (asym_fault_source == 2'd2) && (pt.LOCKSTEP_DELAY == 2) && mubi_check_true(corruption_detected_o));
  cov_asym_iccm_x_delay_3: cover property (@(posedge clk) disable iff (!rst_n)
      asym_fault_active && (asym_fault_source == 2'd2) && (pt.LOCKSTEP_DELAY == 3) && mubi_check_true(corruption_detected_o));
  cov_asym_iccm_x_delay_4: cover property (@(posedge clk) disable iff (!rst_n)
      asym_fault_active && (asym_fault_source == 2'd2) && (pt.LOCKSTEP_DELAY == 4) && mubi_check_true(corruption_detected_o));

  cov_asym_icache_x_delay_0: cover property (@(posedge clk) disable iff (!rst_n)
      asym_fault_active && (asym_fault_source == 2'd3) && (pt.LOCKSTEP_DELAY == 0) && mubi_check_true(corruption_detected_o));
  cov_asym_icache_x_delay_1: cover property (@(posedge clk) disable iff (!rst_n)
      asym_fault_active && (asym_fault_source == 2'd3) && (pt.LOCKSTEP_DELAY == 1) && mubi_check_true(corruption_detected_o));
  cov_asym_icache_x_delay_2: cover property (@(posedge clk) disable iff (!rst_n)
      asym_fault_active && (asym_fault_source == 2'd3) && (pt.LOCKSTEP_DELAY == 2) && mubi_check_true(corruption_detected_o));
  cov_asym_icache_x_delay_3: cover property (@(posedge clk) disable iff (!rst_n)
      asym_fault_active && (asym_fault_source == 2'd3) && (pt.LOCKSTEP_DELAY == 3) && mubi_check_true(corruption_detected_o));
  cov_asym_icache_x_delay_4: cover property (@(posedge clk) disable iff (!rst_n)
      asym_fault_active && (asym_fault_source == 2'd3) && (pt.LOCKSTEP_DELAY == 4) && mubi_check_true(corruption_detected_o));
`endif

endinterface
