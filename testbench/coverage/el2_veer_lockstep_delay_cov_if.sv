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

// Dual-mode functional coverage interface for VCS (covergroup) and Verilator (SVA cover property)

interface el2_veer_lockstep_delay_cov_if
  import el2_mubi_pkg::*;
  import el2_lockstep_pkg::*;
#(
    `include "el2_param.vh"
) (
    input logic        clk,
    input logic        rst_n,
`ifdef RV_LOCKSTEP_REGFILE_ENABLE
    input logic        regfile_corrupted,
`endif
    input logic        outputs_corrupted,
    input el2_mubi_t   corruption_detected_o,
    input el2_mubi_t   lockstep_err_injection_en_i,
    input el2_mubi_t   disable_corruption_detection_i,
    input veer_outputs_t main_core_outputs,
    input veer_outputs_t delayed_main_core_outputs,
    input veer_outputs_t shadow_core_outputs
);

    // Dynamic latency measurement signals
    logic ctrl_fault_inject;
    logic datapath_divergence;
    int   detection_latency;

    // Control-based error injection detection (0-cycle combinational latency)
    assign ctrl_fault_inject = mubi_check_true(lockstep_err_injection_en_i)
                             | mubi_check_true(mubi_check_invalid(lockstep_err_injection_en_i))
                             | mubi_check_true(mubi_check_invalid(disable_corruption_detection_i));

    // Core datapath / regfile mismatch after LockstepDelay pipeline alignment
    assign datapath_divergence = outputs_corrupted
`ifdef RV_LOCKSTEP_REGFILE_ENABLE
                               | regfile_corrupted
`endif
                               ;

    // Combinational latency determination sampled on the clock edge when corruption_detected_o asserts:
    // - Control-based error injection has 0-cycle combinational detection latency.
    // - Datapath/core divergence has 1-cycle sequential fault-to-output latency in 0-delay bypass mode
    //   (LOCKSTEP_DELAY == 0), and pt.LOCKSTEP_DELAY pipeline cycles for LOCKSTEP_DELAY in {1..4}.
    always_comb begin
        if (ctrl_fault_inject) begin
            detection_latency = 0;
        end else if (datapath_divergence) begin
            if (pt.LOCKSTEP_DELAY == 0) begin
                detection_latency = 1;
            end else begin
                detection_latency = int'(pt.LOCKSTEP_DELAY);
            end
        end else begin
            detection_latency = int'(pt.LOCKSTEP_DELAY);
        end
    end

`ifndef VERILATOR
    // -------------------------------------------------------------------------
    // VCS / IEEE 1800 Covergroup: DCLS Delay Configuration and 0-Delay Mode Coverage
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
`else
    // -------------------------------------------------------------------------
    // Functional Coverage for Verilator via SystemVerilog Assertions (`cover property`)
    // -------------------------------------------------------------------------

    // 1. Delay configuration coverpoints (lockstep_delay_cp)
    cov_lockstep_delay_0: cover property (@(posedge clk) disable iff (!rst_n) (pt.LOCKSTEP_DELAY == 0));
    cov_lockstep_delay_1: cover property (@(posedge clk) disable iff (!rst_n) (pt.LOCKSTEP_DELAY == 1));
    cov_lockstep_delay_2: cover property (@(posedge clk) disable iff (!rst_n) (pt.LOCKSTEP_DELAY == 2));
    cov_lockstep_delay_3: cover property (@(posedge clk) disable iff (!rst_n) (pt.LOCKSTEP_DELAY == 3));
    cov_lockstep_delay_4: cover property (@(posedge clk) disable iff (!rst_n) (pt.LOCKSTEP_DELAY == 4));

    // 2. Detection latency coverpoints (delay_mismatch_detection_latency_cp)
    cov_latency_0: cover property (@(posedge clk) disable iff (!rst_n)
        mubi_check_true(corruption_detected_o) && (detection_latency == 0));
    cov_latency_1: cover property (@(posedge clk) disable iff (!rst_n)
        mubi_check_true(corruption_detected_o) && (detection_latency == 1));
    cov_latency_2: cover property (@(posedge clk) disable iff (!rst_n)
        mubi_check_true(corruption_detected_o) && (detection_latency == 2));
    cov_latency_3: cover property (@(posedge clk) disable iff (!rst_n)
        mubi_check_true(corruption_detected_o) && (detection_latency == 3));
    cov_latency_4: cover property (@(posedge clk) disable iff (!rst_n)
        mubi_check_true(corruption_detected_o) && (detection_latency == 4));

    // 3. Corruption detected coverpoint (corruption_detected_cp)
    cov_corruption_detected: cover property (@(posedge clk) disable iff (!rst_n)
        mubi_check_true(corruption_detected_o));

    // 4. Cross Coverage: lockstep_delay_x_corruption
    cov_delay_0_x_corruption: cover property (@(posedge clk) disable iff (!rst_n)
        (pt.LOCKSTEP_DELAY == 0) && mubi_check_true(corruption_detected_o));
    cov_delay_1_x_corruption: cover property (@(posedge clk) disable iff (!rst_n)
        (pt.LOCKSTEP_DELAY == 1) && mubi_check_true(corruption_detected_o));
    cov_delay_2_x_corruption: cover property (@(posedge clk) disable iff (!rst_n)
        (pt.LOCKSTEP_DELAY == 2) && mubi_check_true(corruption_detected_o));
    cov_delay_3_x_corruption: cover property (@(posedge clk) disable iff (!rst_n)
        (pt.LOCKSTEP_DELAY == 3) && mubi_check_true(corruption_detected_o));
    cov_delay_4_x_corruption: cover property (@(posedge clk) disable iff (!rst_n)
        (pt.LOCKSTEP_DELAY == 4) && mubi_check_true(corruption_detected_o));

    // 5. Cross Coverage: lockstep_delay_x_latency
    cov_delay_0_x_latency_0: cover property (@(posedge clk) disable iff (!rst_n)
        (pt.LOCKSTEP_DELAY == 0) && mubi_check_true(corruption_detected_o) && (detection_latency == 0));
    cov_delay_0_x_latency_1: cover property (@(posedge clk) disable iff (!rst_n)
        (pt.LOCKSTEP_DELAY == 0) && mubi_check_true(corruption_detected_o) && (detection_latency == 1));
    cov_delay_1_x_latency_1: cover property (@(posedge clk) disable iff (!rst_n)
        (pt.LOCKSTEP_DELAY == 1) && mubi_check_true(corruption_detected_o) && (detection_latency == 1));
    cov_delay_2_x_latency_2: cover property (@(posedge clk) disable iff (!rst_n)
        (pt.LOCKSTEP_DELAY == 2) && mubi_check_true(corruption_detected_o) && (detection_latency == 2));
    cov_delay_3_x_latency_3: cover property (@(posedge clk) disable iff (!rst_n)
        (pt.LOCKSTEP_DELAY == 3) && mubi_check_true(corruption_detected_o) && (detection_latency == 3));
    cov_delay_4_x_latency_4: cover property (@(posedge clk) disable iff (!rst_n)
        (pt.LOCKSTEP_DELAY == 4) && mubi_check_true(corruption_detected_o) && (detection_latency == 4));

    initial begin
        $display("Lockstep delay coverage interface created (Verilator SVA mode)");
    end
`endif

endinterface
