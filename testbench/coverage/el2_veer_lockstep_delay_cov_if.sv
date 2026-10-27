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

//-----------------------------------------------------------------------------------------
// Functional coverage interface for Synopsys VCS and Verilator (IEEE 1800 covergroup)
//-----------------------------------------------------------------------------------------

interface el2_veer_lockstep_delay_cov_if
  import el2_pkg::*;
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

  // Fault trigger path classification signals
  logic ctrl_fault_inject;
  logic datapath_divergence;

  // Control-port error injection or invalid multi-bit control encoding
  assign ctrl_fault_inject = mubi_check_true(lockstep_err_injection_en_i) |
                             mubi_check_true(mubi_check_invalid(lockstep_err_injection_en_i)) |
                             mubi_check_true(mubi_check_invalid(disable_corruption_detection_i));

  // Core datapath / regfile mismatch after LockstepDelay pipeline alignment
  assign datapath_divergence = outputs_corrupted
`ifdef RV_LOCKSTEP_REGFILE_ENABLE
                             | regfile_corrupted
`endif
                             ;

  // -------------------------------------------------------------------------
  // IEEE 1800 Covergroup: DCLS Delay Configuration and Error Path Coverage
  // -------------------------------------------------------------------------
  covergroup el2_veer_lockstep_delay_cov @(
      posedge clk iff (rst_n & (corruption_detected_o == El2MuBiTrue))
  );
    option.per_instance = 1;

    // Coverpoint lockstep_delay_cp:
    // Covers all supported LOCKSTEP_DELAY parameter values (0..4)
    lockstep_delay_cp: coverpoint int'(pt.LOCKSTEP_DELAY) {
      // delay_0: LOCKSTEP_DELAY == 0 (combinational bypass mode without delay flip-flops)
      bins delay_0 = {0};
      // delay_1..4: LOCKSTEP_DELAY pipeline stages
      bins delay_1 = {1};
      bins delay_2 = {2};
      bins delay_3 = {3};
      bins delay_4 = {4};
    }

    // Coverpoint error_path_cp:
    // Covers fault trigger path (control-port fault vs. core datapath/regfile divergence)
    error_path_cp: coverpoint {datapath_divergence, ctrl_fault_inject} {
      wildcard bins ctrl_fault     = {2'b?1};
      wildcard bins datapath_fault = {2'b1?};
    }

    // Cross Coverage:
    // Cross lockstep_delay_cp with error_path_cp to verify that both control-port faults
    // and core datapath/regfile divergences are detected across every supported delay stage
    lockstep_delay_x_error_path: cross lockstep_delay_cp, error_path_cp;
  endgroup

  el2_veer_lockstep_delay_cov el2_veer_lockstep_delay_cov_cg;

  initial begin
    el2_veer_lockstep_delay_cov_cg = new();
    $display("Lockstep delay coverage interface created");
  end

endinterface : el2_veer_lockstep_delay_cov_if
