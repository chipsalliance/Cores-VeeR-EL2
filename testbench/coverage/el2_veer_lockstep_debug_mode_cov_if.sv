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
// IEEE 1800 functional coverage interface for VCS and Verilator
// Target: Task 2 - DCLS Core Debug Mode Suppression and Transition Coverage
// ----------------------------------------------------------------------------

interface el2_veer_lockstep_debug_mode_cov_if
  import el2_mubi_pkg::*;
#(
  `include "el2_param.vh"
) (
  input logic      clk,
  input logic      rst_n,
`ifdef RV_LOCKSTEP_REGFILE_ENABLE
  input logic      regfile_corrupted,
`endif
  input logic      outputs_corrupted,
  input logic      o_debug_mode_status,
  input el2_mubi_t dbg_detected,
  input el2_mubi_t corruption_detected_o,
  input el2_mubi_t lockstep_err_injection_en_i,
  input el2_mubi_t disable_corruption_detection_i
);

  // Core debug state and DCLS debug suppression tracking signals
  logic       dec_tlu_debug_mode;
  logic       debug_suppression_active;
  logic       ctrl_fault_inject;
  logic       datapath_divergence;
  logic       fault_or_divergence;
  logic       debug_x_corr_qual;
  logic [1:0] debug_state_qual;
  int         suppression_behavior;

  // o_debug_mode_status is driven directly by the main core's dec_tlu_debug_mode
  assign dec_tlu_debug_mode = o_debug_mode_status;

  // In el2_veer_lockstep, corruption reporting suppression is gated solely by the
  // registered dbg_detected (debug_mode_status_latch) until core reset.
  assign debug_suppression_active = mubi_check_true(dbg_detected);

  // Control-based error injection detection
  assign ctrl_fault_inject = mubi_check_true(lockstep_err_injection_en_i) ||
                             mubi_check_true(mubi_check_invalid(lockstep_err_injection_en_i));

  // Core datapath / regfile mismatch after LockstepDelay pipeline alignment
  assign datapath_divergence = outputs_corrupted
`ifdef RV_LOCKSTEP_REGFILE_ENABLE
                             || regfile_corrupted
`endif
                             ;

  // Combined core divergence or error injection indicator (matches any_corruption in RTL)
  assign fault_or_divergence = datapath_divergence || ctrl_fault_inject;

  // Qualifies expected corruption_detected_o response when disable control is El2MuBiFalse:
  // - Debug halt: corruption_detected_o remains El2MuBiFalse regardless of fault_or_divergence
  // - Normal run: corruption_detected_o asserts El2MuBiTrue iff fault_or_divergence is active
  assign debug_x_corr_qual =
      mubi_check_false(disable_corruption_detection_i) && (
          debug_suppression_active ? mubi_check_false(corruption_detected_o) :
          (fault_or_divergence ? mubi_check_true(corruption_detected_o) :
                                 mubi_check_false(corruption_detected_o))
      );

  assign debug_state_qual = {debug_x_corr_qual, debug_suppression_active};

  // Combinational determination of DCLS debug suppression vs. active error reporting:
  // - 1 (debug_active_error_suppressed): Debug mode suppression is active and a core
  //   divergence or error injection is present, while corruption_detected_o stays El2MuBiFalse.
  // - 0 (run_active_error_reported): Normal run mode is active and a core divergence or
  //   error injection is present, and corruption_detected_o asserts El2MuBiTrue.
  always_comb begin
    if (fault_or_divergence && mubi_check_false(disable_corruption_detection_i)) begin
      if (debug_suppression_active && mubi_check_false(corruption_detected_o)) begin
        suppression_behavior = 1;
      end else if (!debug_suppression_active && mubi_check_true(corruption_detected_o)) begin
        suppression_behavior = 0;
      end else begin
        suppression_behavior = -1;
      end
    end else begin
      suppression_behavior = -1;
    end
  end

  // -------------------------------------------------------------------------
  // IEEE 1800 Covergroup: DCLS Core Debug Mode Suppression & Transition
  // -------------------------------------------------------------------------
  covergroup el2_veer_lockstep_debug_mode_cov @(posedge clk iff rst_n);
    option.per_instance = 1;

    // Coverpoint core_debug_state_cp:
    // Tracks normal execution vs. latched DCLS debug suppression state (dbg_detected)
    core_debug_state_cp: coverpoint debug_suppression_active {
      bins normal_run = {1'b0};
      bins debug_halt = {1'b1};
    }

    // Coverpoint debug_transition_cp:
    // Tracks entry into (0 => 1) and exit from (1 => 0) core debug halt mode
    debug_transition_cp: coverpoint dec_tlu_debug_mode {
      bins enter_debug = (1'b0 => 1'b1);
      bins exit_debug  = (1'b1 => 1'b0);
    }

    // Coverpoint debug_suppression_behavior_cp:
    // Verifies that corruption_detected_o is suppressed (El2MuBiFalse) during debug mode
    // and reported (El2MuBiTrue) during normal run mode when divergence/fault is present
    debug_suppression_behavior_cp: coverpoint suppression_behavior {
      bins debug_active_error_suppressed = {1};
      bins run_active_error_reported     = {0};
    }

    // Coverpoint outputs_corrupted_cp:
    // Tracks presence of core output divergence / fault injection
    outputs_corrupted_cp: coverpoint fault_or_divergence {
      bins no_corruption = {1'b0};
      bins corrupted     = {1'b1};
    }

    // Coverpoint corruption_detected_cp:
    // Tracks DCLS corruption_detected_o output state
    corruption_detected_cp: coverpoint mubi_check_true(corruption_detected_o) {
      bins not_detected = {1'b0};
      bins detected     = {1'b1};
    }

    // Helper coverpoint debug_state_qual_cp:
    // Embeds disable_corruption_detection_i == El2MuBiFalse and expected corruption_detected_o
    // response directly into the coverpoint expression for portable automatic cross generation
    debug_state_qual_cp: coverpoint debug_state_qual {
      bins        normal_run  = {2'b10};
      bins        debug_halt  = {2'b11};
      ignore_bins unqualified = {2'b00, 2'b01};
    }

    // Cross Coverage:
    // Cross debug_state_qual_cp with outputs_corrupted_cp to verify DCLS suppression
    // during debug halt and active error reporting during normal execution
    debug_state_x_corruption: cross debug_state_qual_cp, outputs_corrupted_cp;
  endgroup

  initial begin
    el2_veer_lockstep_debug_mode_cov el2_veer_lockstep_debug_mode_cov_cg = new();
    $display("Lockstep debug mode coverage interface created");
  end

endinterface : el2_veer_lockstep_debug_mode_cov_if
