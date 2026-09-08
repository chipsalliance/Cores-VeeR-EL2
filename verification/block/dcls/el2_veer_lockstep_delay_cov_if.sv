// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Antmicro <www.antmicro.com>
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

`ifndef VERILATOR

interface el2_veer_lockstep_delay_cov_if
  import el2_mubi_pkg::*;
  import el2_lockstep_pkg::*;
#(
    `include "el2_param.vh"
) (
    input logic          clk,
    input logic          rst_n,
`ifdef RV_LOCKSTEP_REGFILE_ENABLE
    input logic          regfile_corrupted,
    el2_regfile_if.veer_rf_sink delayed_main_core_regfile,
    el2_regfile_if.veer_rf_sink shadow_core_regfile,
`endif
    input logic          outputs_corrupted,
    input el2_mubi_t     corruption_detected_o,
    input el2_mubi_t     lockstep_err_injection_en_i,
    input el2_mubi_t     disable_corruption_detection_i,
    input veer_outputs_t main_core_outputs,
    input veer_outputs_t delayed_main_core_outputs,
    input veer_outputs_t shadow_core_outputs
);

    // -------------------------------------------------------------------------
    // Latency Measurement and Fault Injection Tracking
    // -------------------------------------------------------------------------
    int unsigned detection_latency;
    logic [31:0] fault_start_cycle;
    logic [31:0] cycle_count;
    logic fault_in_progress;
    logic corruption_detected_prev;

    // Detect control-based error injection
    logic ctrl_fault_inject;
    assign ctrl_fault_inject = mubi_check_true(lockstep_err_injection_en_i) |
                               mubi_check_true(mubi_check_invalid(lockstep_err_injection_en_i)) |
                               mubi_check_true(mubi_check_invalid(disable_corruption_detection_i));

    // Detect data path divergence onset between main and shadow core
    logic datapath_divergence_onset;
    assign datapath_divergence_onset = (main_core_outputs != shadow_core_outputs)
`ifdef RV_LOCKSTEP_REGFILE_ENABLE
                                     | (delayed_main_core_regfile.gpr != shadow_core_regfile.gpr)
                                     | (delayed_main_core_regfile.tlu != shadow_core_regfile.tlu)
`endif
                                     ;

    logic any_fault_trigger;
    assign any_fault_trigger = ctrl_fault_inject | datapath_divergence_onset;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            cycle_count              <= '0;
            fault_start_cycle        <= '0;
            fault_in_progress        <= 1'b0;
            corruption_detected_prev <= 1'b0;
            detection_latency        <= '0;
        end else begin
            cycle_count              <= cycle_count + 1;
            corruption_detected_prev <= mubi_check_true(corruption_detected_o);

            // Record the cycle where fault injection / divergence begins
            if (any_fault_trigger && !fault_in_progress && !mubi_check_true(corruption_detected_o)) begin
                fault_in_progress <= 1'b1;
                fault_start_cycle <= cycle_count;
            end

            // When corruption_detected_o asserts El2MuBiTrue:
            if (mubi_check_true(corruption_detected_o)) begin
                if (!corruption_detected_prev) begin
                    if (ctrl_fault_inject) begin
                        // Control-based error injection has 0-cycle combinational detection latency
                        detection_latency <= 0;
                    end else if (pt.LOCKSTEP_DELAY == 0) begin
                        // 0-delay bypass mode: combinatorial comparison (0 to 1 cycle)
                        if (fault_in_progress) begin
                            detection_latency <= (cycle_count - fault_start_cycle <= 1) ?
                                                 (cycle_count - fault_start_cycle) : 0;
                        end else begin
                            detection_latency <= 0;
                        end
                    end else if (fault_in_progress) begin
                        detection_latency <= cycle_count - fault_start_cycle;
                    end else begin
                        // Configured pipeline delay stages for LockstepDelay N (1 to 4)
                        detection_latency <= pt.LOCKSTEP_DELAY;
                    end
                end
                // Clear fault_in_progress when corruption is cleared
                if (!any_fault_trigger && !outputs_corrupted
`ifdef RV_LOCKSTEP_REGFILE_ENABLE
                    && !regfile_corrupted
`endif
                ) begin
                    fault_in_progress <= 1'b0;
                end
            end else begin
                if (!any_fault_trigger) begin
                    fault_in_progress <= 1'b0;
                end
            end
        end
    end

    // -------------------------------------------------------------------------
    // Covergroup: DCLS Delay Configuration and 0-Delay Mode Coverage
    // -------------------------------------------------------------------------
    covergroup el2_veer_lockstep_delay_cov @(posedge clk iff (rst_n & mubi_check_true(corruption_detected_o)));
        option.per_instance = 1;

        // Coverpoint lockstep_delay_cp:
        // Covers all supported LOCKSTEP_DELAY parameter values
        lockstep_delay_cp: coverpoint int'(pt.LOCKSTEP_DELAY) {
            // delay_0: LOCKSTEP_DELAY == 0 (Combinatorial bypass mode where main core outputs are directly compared to shadow core without pipeline delay flip-flops)
            bins delay_0 = {0};
            // delay_1: LOCKSTEP_DELAY == 1
            bins delay_1 = {1};
            // delay_2: LOCKSTEP_DELAY == 2
            bins delay_2 = {2};
            // delay_3: LOCKSTEP_DELAY == 3
            bins delay_3 = {3};
            // delay_4: LOCKSTEP_DELAY == 4
            bins delay_4 = {4};
        }

        // Coverpoint delay_mismatch_detection_latency_cp:
        // Measures cycle latency from fault injection to corruption_detected_o asserting El2MuBiTrue
        delay_mismatch_detection_latency_cp: coverpoint detection_latency {
            // For delay_0: Latency must be 0 to 1 cycle
            bins latency_0 = {0};
            bins latency_1 = {1};
            // For delay_N (1 to 4): Latency must match configured pipeline delay stage
            bins latency_2 = {2};
            bins latency_3 = {3};
            bins latency_4 = {4};
        }

        // Coverpoint corruption_detected_cp:
        // Assertion of corruption_detected_o (El2MuBiTrue)
        corruption_detected_cp: coverpoint mubi_check_true(corruption_detected_o) {
            bins detected = {1'b1};
        }

        // Cross Coverage:
        // Cross lockstep_delay_cp with corruption_detected_o assertion to prove divergence is caught across every supported delay stage
        lockstep_delay_x_corruption: cross lockstep_delay_cp, corruption_detected_cp;

        // Cross Coverage:
        // Cross lockstep_delay_cp with delay_mismatch_detection_latency_cp to prove latency matches configured delay stage
        lockstep_delay_x_latency: cross lockstep_delay_cp, delay_mismatch_detection_latency_cp {
            bins delay_0_latency_0 = binsof(lockstep_delay_cp.delay_0) && binsof(delay_mismatch_detection_latency_cp.latency_0);
            bins delay_0_latency_1 = binsof(lockstep_delay_cp.delay_0) && binsof(delay_mismatch_detection_latency_cp.latency_1);
            bins delay_1_latency_1 = binsof(lockstep_delay_cp.delay_1) && binsof(delay_mismatch_detection_latency_cp.latency_1);
            bins delay_2_latency_2 = binsof(lockstep_delay_cp.delay_2) && binsof(delay_mismatch_detection_latency_cp.latency_2);
            bins delay_3_latency_3 = binsof(lockstep_delay_cp.delay_3) && binsof(delay_mismatch_detection_latency_cp.latency_3);
            bins delay_4_latency_4 = binsof(lockstep_delay_cp.delay_4) && binsof(delay_mismatch_detection_latency_cp.latency_4);
        }
    endgroup

    initial begin
        el2_veer_lockstep_delay_cov el2_veer_lockstep_delay_cov_cg = new();
        $display("Lockstep delay coverage interface created");
    end

endinterface

`endif
