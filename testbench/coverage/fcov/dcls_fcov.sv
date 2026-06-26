// Copyright 2024 Antmicro <www.antmicro.com>
//
// SPDX-License-Identifier: Apache-2.0

`ifndef VERILATOR
module dcls_fcov (
    input logic clk,
    input logic rst_l,
    input logic dbg_rst_l,
    input logic core_rst_l,
    input el2_mubi_pkg::el2_mubi_t lockstep_err_injection_en_i,
    input el2_mubi_pkg::el2_mubi_t disable_corruption_detection_i,
    input el2_mubi_pkg::el2_mubi_t corruption_detected_o,
    input logic rst_shadow,
    input logic rst_dbg_shadow,
    input logic rst_n,
    input logic outputs_corrupted,
    input el2_mubi_pkg::el2_mubi_t corruption_detected,
    input logic regfile_corrupted
);

// Boolean normalization for legacy 1-bit coverpoint compatibility
logic inj_bool, dis_bool, alarm_bool, corr_bool;
assign inj_bool   = (lockstep_err_injection_en_i != el2_mubi_pkg::El2MuBiFalse);
assign dis_bool   = (disable_corruption_detection_i != el2_mubi_pkg::El2MuBiFalse);
assign alarm_bool = (corruption_detected_o != el2_mubi_pkg::El2MuBiFalse);
assign corr_bool  = (corruption_detected != el2_mubi_pkg::El2MuBiFalse);

// Lockstep functional coverage for delay/reset/equivalence paths
covergroup lockstep_fcov @(posedge clk);

  // Reset and delayed shadow core release
  reset_delayed_shadow: coverpoint {rst_l, dbg_rst_l, rst_shadow, rst_dbg_shadow} {
    bins all_reset = {4'b0000};
    bins main_reset_only = {4'b1000};
    bins dbg_reset_only = {4'b0100};
    bins shadow_released = {4'b0011};
    bins debug_shadow_released = {4'b0001};
    bins all_released = {4'b1111};
    bins partial_release = {[1:14]};
  }

  shadow_release_sequence: coverpoint {rst_shadow, rst_dbg_shadow} {
    bins both_in_reset = {2'b00};
    bins main_released_shadow_reset = {2'b10};
    bins main_reset_shadow_released = {2'b01};
    bins both_released = {2'b11};
  }

  delayed_reset_n: coverpoint rst_n {
    bins reset_active = {1'b0};
    bins reset_complete = {1'b1};
  }

  // Error injection and corruption enable path (Legacy Boolean Normalized)
  err_injection_vs_detection: coverpoint {inj_bool, dis_bool, alarm_bool} {
    bins inject_detected = {3'b111};
    bins inject_blocked = {3'b101};
    bins inject_no_corruption = {3'b110};
    bins detection_disabled = {3'b100};
    bins no_injection_no_corruption = {3'b000};
  }

  // Equivalence check outputs and regfile comparison
  equivalence_outputs: coverpoint outputs_corrupted {
    bins outputs_match = {1'b0};
    bins outputs_mismatch = {1'b1};
  }

  equivalence_regfile: coverpoint regfile_corrupted {
    bins regfile_match = {1'b0};
    bins regfile_mismatch = {1'b1};
  }

  equivalence_corruption: coverpoint corr_bool {
    bins no_corruption = {1'b0};
    bins corruption_detected = {1'b1};
  }

  equivalence_cross: cross outputs_corrupted, regfile_corrupted, equivalence_corruption;

  // Corruption output gating through equivalence and detection disable (Legacy Boolean Normalized)
  corruption_output: coverpoint {corr_bool, inj_bool, dis_bool, alarm_bool} {
    bins detected_via_equivalence = {4'b1001};
    bins injected_but_not_detected = {4'b1010};
    bins disabled_detection = {4'b1000};
    bins normal_operation = {4'b0000};
  }

  // Delay-related coverage naming for visibility
  delayed_equivalence_check: coverpoint {outputs_corrupted, rst_n} {
    bins delayed_mismatch_after_reset = {2'b11};
    bins delayed_match_after_reset = {2'b01};
    bins mismatch_while_reset = {2'b10};
    bins match_while_reset = {2'b00};
  }

  // ==========================================================================
  // DCLS MULTI-BIT (MUBI) EXHAUSTIVE FUNCTIONAL COVERAGE
  // ==========================================================================

  // 1. Independent MUBI Tamper State Classifications
  mubi_inj_state: coverpoint lockstep_err_injection_en_i {
    bins inj_true  = {el2_mubi_pkg::El2MuBiTrue};
    bins inj_false = {el2_mubi_pkg::El2MuBiFalse};
    bins inj_inv   = default;
  }

  mubi_dis_state: coverpoint disable_corruption_detection_i {
    bins dis_true  = {el2_mubi_pkg::El2MuBiTrue};
    bins dis_false = {el2_mubi_pkg::El2MuBiFalse};
    bins dis_inv   = default;
  }

  mubi_alarm_state: coverpoint corruption_detected_o {
    bins alarm_true  = {el2_mubi_pkg::El2MuBiTrue};
    bins alarm_false = {el2_mubi_pkg::El2MuBiFalse};
  }

  // 2. MUBI 2D Matrix Cross Coverage (Verifies all 9 logical INJ x DIS tamper combinations)
  mubi_inj_cross_dis: cross mubi_inj_state, mubi_dis_state;

  // 3. Cross of MUBI Threat Matrix with Physical HW Equivalence Alarms
  mubi_threat_matrix_cross: cross mubi_inj_state, mubi_dis_state, equivalence_outputs;

endgroup

// ============================================================================
// DCLS MULTI-BIT (MUBI) COMPREHENSIVE MATRIX COVERAGE AT SOFTWARE LEVEL
// ============================================================================
covergroup dcls_mubi_matrix @(posedge clk iff rst_n);
  option.per_instance = 1;
  inj_cp: coverpoint lockstep_err_injection_en_i {
    bins t   = {el2_mubi_pkg::El2MuBiTrue};
    bins f   = {el2_mubi_pkg::El2MuBiFalse};
    bins inv = default;
  }
  dis_cp: coverpoint disable_corruption_detection_i {
    bins t   = {el2_mubi_pkg::El2MuBiTrue};
    bins f   = {el2_mubi_pkg::El2MuBiFalse};
    bins inv = default;
  }
  alarm_cp: coverpoint corruption_detected_o {
    bins t   = {el2_mubi_pkg::El2MuBiTrue};
    bins f   = {el2_mubi_pkg::El2MuBiFalse};
  }
  out_cp: coverpoint outputs_corrupted {
    bins match = {1'b0};
    bins diff  = {1'b1};
  }
  // Cross matrix of INJ x DIS tamper commands
  inj_cross_dis: cross inj_cp, dis_cp;
  // Cross of MUBI threat controls with physical HW equivalence alarms
  threat_matrix_cross: cross inj_cp, dis_cp, out_cp;
endgroup

lockstep_fcov lockstep_fcov_inst = new();
dcls_mubi_matrix dcls_mubi_matrix_inst = new();

endmodule
`endif
