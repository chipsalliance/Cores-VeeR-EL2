// Copyright 2024 Antmicro <www.antmicro.com>
//
// SPDX-License-Identifier: Apache-2.0

`ifndef VERILATOR
module dcls_fcov (
    input logic clk,
    input logic rst_l,
    input logic dbg_rst_l,
    input logic core_rst_l,
    input logic lockstep_err_injection_en_i,
    input logic disable_corruption_detection_i,
    input logic corruption_detected_o,
    input logic rst_shadow,
    input logic rst_dbg_shadow,
    input logic rst_n,
    input logic outputs_corrupted,
    input logic corruption_detected,
    input logic regfile_corrupted
);

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

  // Error injection and corruption enable path
  err_injection_vs_detection: coverpoint {lockstep_err_injection_en_i, disable_corruption_detection_i, corruption_detected_o} {
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

  equivalence_corruption: coverpoint corruption_detected {
    bins no_corruption = {1'b0};
    bins corruption_detected = {1'b1};
  }

  equivalence_cross: cross outputs_corrupted, regfile_corrupted, corruption_detected;

  // Corruption output gating through equivalence and detection disable
  corruption_output: coverpoint {corruption_detected, lockstep_err_injection_en_i, disable_corruption_detection_i, corruption_detected_o} {
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

endgroup

lockstep_fcov lockstep_fcov_inst = new();

endmodule
`endif
