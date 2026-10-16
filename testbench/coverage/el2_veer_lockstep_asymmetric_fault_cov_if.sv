/* SPDX-License-Identifier: Apache-2.0
 * Copyright 2026 Google LLC
 *
 * DCLS Asymmetric Shadow Core Fault Divergence Functional Coverage Interface (Task 8)
 * Author: Samip Modi (samipmodi@google.com)
 *
 * Description:
 * Dual-simulator functional coverage interface bound into `el2_veer_lockstep` for
 * Synopsys VCS (`covergroup`) and Verilator (SVA `cover property`).
 *
 * Covers:
 * 1. `asymmetric_fault_source_cp`:
 *    - `dccm_asymmetric`: Shadow core DCCM threshold alert active (`mdccmect` mismatch, Case 203).
 *    - `iccm_asymmetric`: Shadow core ICCM threshold alert active (`miccmect` mismatch, Case 204).
 *    - `icache_asymmetric`: Shadow core ICache threshold alert active (`micect` mismatch, Case 205).
 * 2. `asymmetric_lockstep_response_cp`:
 *    - `comparator_mismatch`: Subordinate alert causes execution/regfile divergence and asserts
 *      `corruption_detected_o == El2MuBiTrue`.
 *    - `external_interrupt_fired`: Lockstep mismatch interrupt signals to PIC (`extintsrc_req[2]`).
 * 3. `asymmetric_source_x_delay_cross`:
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
    input logic                           shadow_mdccme_ce_req,
    input logic                           shadow_miccme_ce_req,
    input logic                           shadow_mice_ce_req
);

  logic datapath_divergence;
  assign datapath_divergence = outputs_corrupted
`ifdef RV_LOCKSTEP_REGFILE_ENABLE
                             | regfile_corrupted
`endif
                             ;

  // Encode asymmetric shadow core ECC threshold alert source:
  // 2'd0 = none
  // 2'd1 = dccm_asymmetric (`shadow_mdccme_ce_req`)
  // 2'd2 = iccm_asymmetric (`shadow_miccme_ce_req`)
  // 2'd3 = icache_asymmetric (`shadow_mice_ce_req`)
  logic [1:0] asym_fault_source;
  always_comb begin
    if (shadow_mdccme_ce_req) begin
      asym_fault_source = 2'd1;
    end else if (shadow_miccme_ce_req) begin
      asym_fault_source = 2'd2;
    end else if (shadow_mice_ce_req) begin
      asym_fault_source = 2'd3;
    end else begin
      asym_fault_source = 2'd0;
    end
  end

  logic asym_fault_active;
  assign asym_fault_active = (asym_fault_source != 2'd0);

  // Track DCLS lockstep response while an asymmetric shadow core fault is active:
  // Bit 0: `comparator_mismatch` (`datapath_divergence` and `corruption_detected_o == El2MuBiTrue`)
  // Bit 1: `external_interrupt_fired` (PIC lockstep mismatch interrupt `extintsrc_req[2]` asserted)
  logic       comparator_mismatch_evt;
  logic       ext_interrupt_fired_evt;
  logic [1:0] asym_response_vec;

  assign comparator_mismatch_evt = asym_fault_active & datapath_divergence &
                                   mubi_check_true(corruption_detected_o);
  assign ext_interrupt_fired_evt = asym_fault_active &
                                   mubi_check_true(corruption_detected_o) &
                                   ((pt.PIC_TOTAL_INT >= 2) ? extintsrc_req[2] : 1'b0);
  assign asym_response_vec       = {ext_interrupt_fired_evt, comparator_mismatch_evt};

`ifndef VERILATOR
  // ---------------------------------------------------------------------------
  // Synopsys VCS / IEEE 1800 Covergroup: DCLS Asymmetric Shadow Core Faults
  // ---------------------------------------------------------------------------
  covergroup el2_veer_lockstep_asymmetric_fault_cov @(
      posedge clk iff (rst_n & asym_fault_active & mubi_check_true(corruption_detected_o))
  );
    type_option.merge_instances = 1;

    // 1. Asymmetric fault source on shadow core
    asymmetric_fault_source_cp: coverpoint asym_fault_source {
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
      (asym_fault_source == 2'd1) && mubi_check_true(corruption_detected_o));
  cov_asym_source_iccm: cover property (@(posedge clk) disable iff (!rst_n)
      (asym_fault_source == 2'd2) && mubi_check_true(corruption_detected_o));
  cov_asym_source_icache: cover property (@(posedge clk) disable iff (!rst_n)
      (asym_fault_source == 2'd3) && mubi_check_true(corruption_detected_o));

  // 2. Asymmetric lockstep response coverpoints (asymmetric_lockstep_response_cp)
  cov_asym_resp_comparator_mismatch: cover property (@(posedge clk) disable iff (!rst_n)
      comparator_mismatch_evt);
  cov_asym_resp_external_interrupt_fired: cover property (@(posedge clk) disable iff (!rst_n)
      ext_interrupt_fired_evt);

  // 3. Cross: asymmetric_fault_source_cp x lockstep_delay_cp (Delays 0 to 4)
  cov_asym_dccm_x_delay_0: cover property (@(posedge clk) disable iff (!rst_n)
      (asym_fault_source == 2'd1) && (pt.LOCKSTEP_DELAY == 0) && mubi_check_true(corruption_detected_o));
  cov_asym_dccm_x_delay_1: cover property (@(posedge clk) disable iff (!rst_n)
      (asym_fault_source == 2'd1) && (pt.LOCKSTEP_DELAY == 1) && mubi_check_true(corruption_detected_o));
  cov_asym_dccm_x_delay_2: cover property (@(posedge clk) disable iff (!rst_n)
      (asym_fault_source == 2'd1) && (pt.LOCKSTEP_DELAY == 2) && mubi_check_true(corruption_detected_o));
  cov_asym_dccm_x_delay_3: cover property (@(posedge clk) disable iff (!rst_n)
      (asym_fault_source == 2'd1) && (pt.LOCKSTEP_DELAY == 3) && mubi_check_true(corruption_detected_o));
  cov_asym_dccm_x_delay_4: cover property (@(posedge clk) disable iff (!rst_n)
      (asym_fault_source == 2'd1) && (pt.LOCKSTEP_DELAY == 4) && mubi_check_true(corruption_detected_o));

  cov_asym_iccm_x_delay_0: cover property (@(posedge clk) disable iff (!rst_n)
      (asym_fault_source == 2'd2) && (pt.LOCKSTEP_DELAY == 0) && mubi_check_true(corruption_detected_o));
  cov_asym_iccm_x_delay_1: cover property (@(posedge clk) disable iff (!rst_n)
      (asym_fault_source == 2'd2) && (pt.LOCKSTEP_DELAY == 1) && mubi_check_true(corruption_detected_o));
  cov_asym_iccm_x_delay_2: cover property (@(posedge clk) disable iff (!rst_n)
      (asym_fault_source == 2'd2) && (pt.LOCKSTEP_DELAY == 2) && mubi_check_true(corruption_detected_o));
  cov_asym_iccm_x_delay_3: cover property (@(posedge clk) disable iff (!rst_n)
      (asym_fault_source == 2'd2) && (pt.LOCKSTEP_DELAY == 3) && mubi_check_true(corruption_detected_o));
  cov_asym_iccm_x_delay_4: cover property (@(posedge clk) disable iff (!rst_n)
      (asym_fault_source == 2'd2) && (pt.LOCKSTEP_DELAY == 4) && mubi_check_true(corruption_detected_o));

  cov_asym_icache_x_delay_0: cover property (@(posedge clk) disable iff (!rst_n)
      (asym_fault_source == 2'd3) && (pt.LOCKSTEP_DELAY == 0) && mubi_check_true(corruption_detected_o));
  cov_asym_icache_x_delay_1: cover property (@(posedge clk) disable iff (!rst_n)
      (asym_fault_source == 2'd3) && (pt.LOCKSTEP_DELAY == 1) && mubi_check_true(corruption_detected_o));
  cov_asym_icache_x_delay_2: cover property (@(posedge clk) disable iff (!rst_n)
      (asym_fault_source == 2'd3) && (pt.LOCKSTEP_DELAY == 2) && mubi_check_true(corruption_detected_o));
  cov_asym_icache_x_delay_3: cover property (@(posedge clk) disable iff (!rst_n)
      (asym_fault_source == 2'd3) && (pt.LOCKSTEP_DELAY == 3) && mubi_check_true(corruption_detected_o));
  cov_asym_icache_x_delay_4: cover property (@(posedge clk) disable iff (!rst_n)
      (asym_fault_source == 2'd3) && (pt.LOCKSTEP_DELAY == 4) && mubi_check_true(corruption_detected_o));
`endif

endinterface
