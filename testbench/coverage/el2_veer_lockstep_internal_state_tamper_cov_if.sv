/* SPDX-License-Identifier: Apache-2.0
 * Copyright 2026 Google LLC
 *
 * DCLS Internal Core Architectural State Tamper Functional Coverage Interface (Task 10)
 * Author: Samip Modi (samipmodi@google.com)
 *
 * Description:
 * Functional coverage interface bound into `el2_veer_wrapper` for
 * Synopsys VCS and Verilator (`covergroup`).
 *
 * Covers:
 * 1. `internal_tamper_target_cp`:
 *    - `gpr_tamper` (Bit-flip in general purpose register `a5` / `x15`, Case 200)
 *    - `pc_tamper`  (Bit-flip in program counter flop `q0pcff`, Case 201)
 *    - `csr_tamper` (Bit-flip in architectural CSR flop `mtvec_ff`, Case 202)
 * 2. `internal_tamper_detection_cp`:
 *    - `trapped_and_recovered` (Divergence detected, trap taken, forces cleared,
 *      and warm-reset resynchronization succeeds)
 * 3. `lockstep_delay_cp`:
 *    - `delay_0` through `delay_4` (`pt.LOCKSTEP_DELAY` == 0..4)
 * 4. `internal_tamper_x_delay_cross`:
 *    - Cross of `internal_tamper_target_cp` x `lockstep_delay_cp` (Delays 0 to 4)
 */

interface el2_veer_lockstep_internal_state_tamper_cov_if
  import el2_pkg::*;
  import el2_mubi_pkg::*;
#(
    `include "el2_param.vh"
) (
    input logic        clk,
    input logic        rst_l,
    input logic        dbg_rst_l,
    input logic        rst_n,
    input logic [31:0] main_gpr_a5,
    input logic [31:1] main_q0pc,
    input logic [30:0] main_mtvec,
    input logic [31:0]               shadow_gpr_a5,
    input logic [31:1]               shadow_q0pc,
    input logic [30:0]               shadow_mtvec,
    input el2_mubi_t                 corruption_detected_o,
    input logic [pt.PIC_TOTAL_INT:1] extintsrc_req
);

  localparam int unsigned LockstepDelay = 32'(pt.LOCKSTEP_DELAY);

  // Align main-core internal architectural state with `LockstepDelay` (0..4 cycles)
  // to match the subordinate shadow core pipeline timing. Reset with `rst_l` (matching
  // `el2_veer_lockstep`) so the delay pipeline fills before `rst_n` deasserts.
  logic [3:0][31:0] main_gpr_a5_q;
  logic [3:0][31:1] main_q0pc_q;
  logic [3:0][30:0] main_mtvec_q;

  logic [31:0]      main_gpr_a5_d;
  logic [31:1]      main_q0pc_d;
  logic [30:0]      main_mtvec_d;

  always_ff @(posedge clk or negedge rst_l) begin
    if (!rst_l) begin
      main_gpr_a5_q <= '0;
      main_q0pc_q   <= '0;
      main_mtvec_q  <= '0;
    end else begin
      main_gpr_a5_q <= {main_gpr_a5_q[2:0], main_gpr_a5};
      main_q0pc_q   <= {main_q0pc_q[2:0], main_q0pc};
      main_mtvec_q  <= {main_mtvec_q[2:0], main_mtvec};
    end
  end

  always_comb begin
    case (LockstepDelay)
      0: begin
        main_gpr_a5_d = main_gpr_a5;
        main_q0pc_d   = main_q0pc;
        main_mtvec_d  = main_mtvec;
      end
      1: begin
        main_gpr_a5_d = main_gpr_a5_q[0];
        main_q0pc_d   = main_q0pc_q[0];
        main_mtvec_d  = main_mtvec_q[0];
      end
      2: begin
        main_gpr_a5_d = main_gpr_a5_q[1];
        main_q0pc_d   = main_q0pc_q[1];
        main_mtvec_d  = main_mtvec_q[1];
      end
      3: begin
        main_gpr_a5_d = main_gpr_a5_q[2];
        main_q0pc_d   = main_q0pc_q[2];
        main_mtvec_d  = main_mtvec_q[2];
      end
      default: begin
        main_gpr_a5_d = main_gpr_a5_q[3];
        main_q0pc_d   = main_q0pc_q[3];
        main_mtvec_d  = main_mtvec_q[3];
      end
    endcase
  end

  // Raw internal architectural state divergence between delay-aligned main and shadow cores
  logic gpr_mismatch;
  logic pc_mismatch;
  logic csr_mismatch;
  logic any_raw_mismatch;

  assign gpr_mismatch     = (main_gpr_a5_d != shadow_gpr_a5);
  assign pc_mismatch      = (main_q0pc_d != shadow_q0pc);
  assign csr_mismatch     = (main_mtvec_d != shadow_mtvec);
  assign any_raw_mismatch = gpr_mismatch | pc_mismatch | csr_mismatch;

  // Root-cause tamper target classification (first-fault-wins per tamper cycle so downstream
  // PC/GPR divergence after trap redirection does not mask the injected root-cause target):
  // 2'd0 = none
  // 2'd1 = gpr_tamper (Case 200: `a5` / `x15` tamper)
  // 2'd2 = pc_tamper  (Case 201: `q0pcff` tamper)
  // 2'd3 = csr_tamper (Case 202: `mtvec_ff` tamper)
  logic [1:0] latched_tamper_type_q;
  logic [1:0] active_tamper_type;
  logic       gpr_tamper;
  logic       pc_tamper;
  logic       csr_tamper;
  logic       any_internal_tamper;
  logic       tamper_detected;

  always_comb begin
    if (latched_tamper_type_q != 2'd0) begin
      active_tamper_type = latched_tamper_type_q;
    end else if (gpr_mismatch) begin
      active_tamper_type = 2'd1;
    end else if (csr_mismatch) begin
      active_tamper_type = 2'd3;
    end else if (pc_mismatch) begin
      active_tamper_type = 2'd2;
    end else begin
      active_tamper_type = 2'd0;
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      latched_tamper_type_q <= 2'd0;
    end else if (!any_raw_mismatch && !mubi_check_true(corruption_detected_o)) begin
      latched_tamper_type_q <= 2'd0;
    end else if (latched_tamper_type_q == 2'd0) begin
      latched_tamper_type_q <= active_tamper_type;
    end
  end

  assign gpr_tamper          = (active_tamper_type == 2'd1);
  assign pc_tamper           = (active_tamper_type == 2'd2);
  assign csr_tamper          = (active_tamper_type == 2'd3);
  assign any_internal_tamper = (active_tamper_type != 2'd0);
  assign tamper_detected     = any_internal_tamper & mubi_check_true(corruption_detected_o);

  // End-to-end tamper trap and warm-reset recovery tracker (`trapped_and_recovered`):
  // 1. `tamper_trap_seen_q` latches when an internal state tamper triggers lockstep
  //    `corruption_detected_o` and asserts `extintsrc_req[2]`.
  // 2. `warm_reset_seen_q` latches when the trap handler releases forces (`0x95`) and
  //    triggers warm reset (`0x96`, pulling `rst_n` low while power-on `dbg_rst_l` stays high).
  // 3. `trapped_and_recovered_pulse` asserts on the cycle after warm reset completes when
  //    both cores resume synchronized execution (`rst_n && !any_raw_mismatch && !corruption_detected_o`).
  logic lockstep_ext_int_req;
  logic unused_extintsrc_req;
  assign unused_extintsrc_req = |extintsrc_req;

  generate
    if (pt.PIC_TOTAL_INT >= 2) begin : gen_pic_ext_int
      assign lockstep_ext_int_req = extintsrc_req[2];
    end else begin : gen_no_pic_ext_int
      assign lockstep_ext_int_req = 1'b0;
    end
  endgenerate

  logic tamper_trap_seen_q;
  logic warm_reset_seen_q;
  logic trapped_and_recovered_pulse;

  assign trapped_and_recovered_pulse = rst_n & tamper_trap_seen_q & warm_reset_seen_q &
                                       ~any_raw_mismatch & ~mubi_check_true(corruption_detected_o);

  always_ff @(posedge clk or negedge dbg_rst_l) begin
    if (!dbg_rst_l) begin
      tamper_trap_seen_q <= 1'b0;
      warm_reset_seen_q  <= 1'b0;
    end else if (trapped_and_recovered_pulse) begin
      tamper_trap_seen_q <= 1'b0;
      warm_reset_seen_q  <= 1'b0;
    end else begin
      if (rst_n && tamper_detected && lockstep_ext_int_req) begin
        tamper_trap_seen_q <= 1'b1;
      end
      if (!rst_n && tamper_trap_seen_q) begin
        warm_reset_seen_q <= 1'b1;
      end
    end
  end

  // =========================================================================
  // IEEE 1800 Covergroup Implementation
  // =========================================================================
  covergroup el2_veer_lockstep_internal_state_tamper_cov @(
      posedge clk iff (rst_n & (tamper_detected | trapped_and_recovered_pulse))
  );
    option.per_instance = 1;
    type_option.merge_instances = 1;

    // 1. Internal Core Architectural State Tamper Target (Cases 200, 201, 202)
    internal_tamper_target_cp: coverpoint active_tamper_type iff (tamper_detected) {
      bins gpr_tamper = {2'd1};
      bins pc_tamper  = {2'd2};
      bins csr_tamper = {2'd3};
    }

    // 2. End-to-End Tamper Detection, Trap Handling, Force Release, and Warm-Reset Recovery
    internal_tamper_detection_cp: coverpoint trapped_and_recovered_pulse {
      bins trapped_and_recovered = {1'b1};
    }

    // 3. Configured Lockstep Pipeline Delay (0..4 cycles)
    lockstep_delay_cp: coverpoint int'(pt.LOCKSTEP_DELAY) iff (tamper_detected) {
      bins delay_0 = {0};
      bins delay_1 = {1};
      bins delay_2 = {2};
      bins delay_3 = {3};
      bins delay_4 = {4};
    }

    // 4. Cross Coverage: Internal State Tamper Target x Lockstep Pipeline Delay (0..4)
    internal_tamper_x_delay_cross: cross internal_tamper_target_cp, lockstep_delay_cp;
  endgroup

  el2_veer_lockstep_internal_state_tamper_cov cg;

  initial begin
    cg = new();
    $display("Lockstep internal state tamper coverage interface created");
  end

endinterface : el2_veer_lockstep_internal_state_tamper_cov_if
