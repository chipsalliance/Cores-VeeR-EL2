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
// Target: Task 3 - Multi-Bit Integrity (MUBI) Encoding and Fail-Secure Coverage
// ----------------------------------------------------------------------------

interface el2_veer_lockstep_mubi_sweep_cov_if
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
  input el2_mubi_t corruption_detected_o,
  input el2_mubi_t lockstep_err_injection_en_i,
  input el2_mubi_t disable_corruption_detection_i
);

  // -------------------------------------------------------------------------
  // MUBI Encoding Classification & Fail-Secure Tamper Detection Signals
  // -------------------------------------------------------------------------

  // 1. Error injection control (lockstep_err_injection_en_i) encoding flags
  logic       inj_is_true;
  logic       inj_is_false;
  logic       inj_is_invalid;
  logic       inj_hd1_true;
  logic       inj_hd1_false;
  logic       inj_all_zeros;
  logic       inj_all_ones;
  logic [5:0] inj_encoding_cats;

  assign inj_is_true    = mubi_check_true(lockstep_err_injection_en_i);
  assign inj_is_false   = mubi_check_false(lockstep_err_injection_en_i);
  assign inj_is_invalid = mubi_check_true(mubi_check_invalid(lockstep_err_injection_en_i));
  assign inj_hd1_true   = inj_is_invalid &&
                          ($countones(lockstep_err_injection_en_i ^ El2MuBiTrue) == 1);
  assign inj_hd1_false  = inj_is_invalid &&
                          ($countones(lockstep_err_injection_en_i ^ El2MuBiFalse) == 1);
  assign inj_all_zeros  = inj_is_invalid && (lockstep_err_injection_en_i == '0);
  assign inj_all_ones   = inj_is_invalid && (lockstep_err_injection_en_i == '1);

  // Bitmask encoding allows wildcard bins to simultaneously credit overlapping
  // invalid categories (e.g., for 2-bit MUBI where 2'b00 is both all-zeros and HD=1)
  // while keeping covergroup bin widths constant across all MUBI_WIDTH configs.
  assign inj_encoding_cats = {
      inj_all_ones,
      inj_all_zeros,
      inj_hd1_false,
      inj_hd1_true,
      inj_is_false,
      inj_is_true
  };

  // 2. Disable corruption detection control (disable_corruption_detection_i) encoding flags
  logic       disable_is_true;
  logic       disable_is_false;
  logic       disable_is_invalid;
  logic       disable_hd1_true;
  logic       disable_hd1_false;
  logic       disable_all_zeros;
  logic       disable_all_ones;
  logic [5:0] disable_encoding_cats;

  assign disable_is_true    = mubi_check_true(disable_corruption_detection_i);
  assign disable_is_false   = mubi_check_false(disable_corruption_detection_i);
  assign disable_is_invalid = mubi_check_true(mubi_check_invalid(disable_corruption_detection_i));
  assign disable_hd1_true   = disable_is_invalid &&
                              ($countones(disable_corruption_detection_i ^ El2MuBiTrue) == 1);
  assign disable_hd1_false  = disable_is_invalid &&
                              ($countones(disable_corruption_detection_i ^ El2MuBiFalse) == 1);
  assign disable_all_zeros  = disable_is_invalid && (disable_corruption_detection_i == '0);
  assign disable_all_ones   = disable_is_invalid && (disable_corruption_detection_i == '1);

  assign disable_encoding_cats = {
      disable_all_ones,
      disable_all_zeros,
      disable_hd1_false,
      disable_hd1_true,
      disable_is_false,
      disable_is_true
  };

  // 3. Fail-secure tamper detection (corrupted disable control + active fault/divergence)
  logic       ctrl_fault_inject;
  logic       datapath_divergence;
  logic       fault_injected;
  logic [1:0] fault_source_cats;
  logic       fail_secure_tamper_detected;
  logic [1:0] disable_mode_resp;

  assign ctrl_fault_inject   = inj_is_true || inj_is_invalid;
  assign datapath_divergence = outputs_corrupted
`ifdef RV_LOCKSTEP_REGFILE_ENABLE
                             || regfile_corrupted
`endif
                             ;
  assign fault_injected      = ctrl_fault_inject || datapath_divergence;
  assign fault_source_cats   = {datapath_divergence, ctrl_fault_inject};

  // When disable_corruption_detection_i has an invalid pattern AND a fault is active,
  // corruption_detected_o must assert El2MuBiTrue (fail-secure protection).
  assign fail_secure_tamper_detected = disable_is_invalid &&
                                       fault_injected &&
                                       mubi_check_true(corruption_detected_o);

  // Encodes disable_corruption_detection_i mode qualified by expected corruption_detected_o
  // response for portable automatic cross generation across VCS and Verilator:
  // - 2'd1: disable_true with corruption_detected_o == El2MuBiFalse
  // - 2'd2: disable_false with corruption_detected_o matching fault_injected
  // - 2'd3: disable_invalid with corruption_detected_o == El2MuBiTrue (fail-secure)
  // - 2'd0: unqualified (e.g., debug-mode suppression when disable_false)
  always_comb begin
    if (disable_is_true && mubi_check_false(corruption_detected_o)) begin
      disable_mode_resp = 2'd1;
    end else if (disable_is_false &&
                 (fault_injected ? mubi_check_true(corruption_detected_o) :
                                   mubi_check_false(corruption_detected_o))) begin
      disable_mode_resp = 2'd2;
    end else if (disable_is_invalid && mubi_check_true(corruption_detected_o)) begin
      disable_mode_resp = 2'd3;
    end else begin
      disable_mode_resp = 2'd0;
    end
  end

  // -------------------------------------------------------------------------
  // IEEE 1800 Covergroup: MUBI Comprehensive Encoding & Fail-Secure
  // -------------------------------------------------------------------------
  covergroup el2_veer_lockstep_mubi_sweep_cov @(posedge clk iff rst_n);
    option.per_instance = 1;

    // 1. Coverpoint mubi_width_config_cp:
    // Bins for configured MUBI widths sampled on an active corruption_detected_o event
    mubi_width_config_cp: coverpoint int'(El2MuBiWidth)
        iff (mubi_check_true(corruption_detected_o)) {
      bins width_2  = {2};
      bins width_4  = {4};
      bins width_8  = {8};
      bins width_16 = {16};
      bins width_32 = {32};
    }

    // 2. Coverpoint mubi_error_injection_control_cp:
    // Tracks El2MuBiTrue, El2MuBiFalse, and corrupted patterns on lockstep_err_injection_en_i
    mubi_error_injection_control_cp: coverpoint inj_encoding_cats {
      wildcard bins inj_true              = {6'b????_?1};
      wildcard bins inj_false             = {6'b????_10};
      wildcard bins inj_invalid_hd1_true  = {6'b???1_00};
      wildcard bins inj_invalid_hd1_false = {6'b??1?_00};
      wildcard bins inj_invalid_all_zeros = {6'b?1??_00};
      wildcard bins inj_invalid_all_ones  = {6'b1???_00};
    }

    // 3. Coverpoint mubi_disable_detection_control_cp:
    // Tracks El2MuBiTrue, El2MuBiFalse, and corrupted patterns on disable_corruption_detection_i
    mubi_disable_detection_control_cp: coverpoint disable_encoding_cats {
      wildcard bins disable_true              = {6'b????_?1};
      wildcard bins disable_false             = {6'b????_10};
      wildcard bins disable_invalid_hd1_true  = {6'b???1_00};
      wildcard bins disable_invalid_hd1_false = {6'b??1?_00};
      wildcard bins disable_invalid_all_zeros = {6'b?1??_00};
      wildcard bins disable_invalid_all_ones  = {6'b1???_00};
    }

    // 4. Coverpoint fail_secure_tamper_cp:
    // Verifies fail-secure assertion of corruption_detected_o when disable control is tampered
    // while a fault is active
    fail_secure_tamper_cp: coverpoint fail_secure_tamper_detected {
      bins corrupted_disable_with_fault = {1'b1};
    }

    // Helper coverpoint outputs_corrupted_cp (includes outputs_corrupted || regfile_corrupted)
    outputs_corrupted_cp: coverpoint datapath_divergence {
      bins no_mismatch = {1'b0};
      bins mismatch    = {1'b1};
    }

    // Helper coverpoint fault_source_cp partitioning {datapath_divergence, ctrl_fault_inject}
    fault_source_cp: coverpoint fault_source_cats {
      bins          no_fault          = {2'b00};
      bins          ctrl_fault        = {2'b01};
      wildcard bins datapath_mismatch = {2'b1?};
    }

    // Helper coverpoint corruption_detected_cp
    corruption_detected_cp: coverpoint mubi_check_true(corruption_detected_o) {
      bins corr_false = {1'b0};
      bins corr_true  = {1'b1};
    }

    // Helper coverpoint disable_mode_resp_cp across [True, False, Invalid] qualified by
    // expected corruption_detected_o response
    disable_mode_resp_cp: coverpoint disable_mode_resp {
      bins        disable_true    = {2'd1};
      bins        disable_false   = {2'd2};
      bins        disable_invalid = {2'd3};
      ignore_bins unqualified     = {2'd0};
    }

    // Helper coverpoint valid_disable_resp_cp across valid [True, False] modes
    valid_disable_resp_cp: coverpoint disable_mode_resp {
      bins        disable_true             = {2'd1};
      bins        disable_false            = {2'd2};
      ignore_bins non_valid_or_unqualified = {2'd0, 2'd3};
    }

    // Helper coverpoint fault_present_cp tracking presence of any active fault or mismatch
    fault_present_cp: coverpoint fault_injected {
      bins no_fault     = {1'b0};
      bins fault_active = {1'b1};
    }

    // 5a. Cross Coverage across all disable modes [True, False, Invalid] and fault presence:
    // Verifies suppression under True, normal reporting under False, and fail-secure
    // reporting under Invalid both with and without an active fault
    disable_ctrl_x_corruption: cross disable_mode_resp_cp, fault_present_cp;

    // 5b. Cross Coverage across valid disable modes [True, False] and granular fault source:
    // Verifies both ctrl_fault and datapath_mismatch suppression under True and detection
    // under False
    valid_disable_x_fault_source: cross valid_disable_resp_cp, fault_source_cp;
  endgroup

  initial begin
    el2_veer_lockstep_mubi_sweep_cov el2_veer_lockstep_mubi_sweep_cov_cg = new();
    $display("Lockstep MUBI sweep coverage interface created");
  end

endinterface : el2_veer_lockstep_mubi_sweep_cov_if
