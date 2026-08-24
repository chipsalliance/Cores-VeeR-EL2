// Copyright 2026 Antmicro <www.antmicro.com>
// //
// // SPDX-License-Identifier: Apache-2.0
//
`ifdef RV_TRIPLE_MODULAR_REDUNDANCY_ENABLE
module el2_tmr_exec_ctrl
  import el2_pkg::*;
  import el2_mubi_pkg::*;
(
    input  logic clk,
    input  logic rst_l,

    // EXEC CTRL
    input  logic i_cpu_halt_req,
    output logic o_cpu_halt_ack,
    input  logic i_cpu_run_req,
    output logic o_cpu_run_ack,
    output logic o_cpu_halt_status,
    output logic o_debug_mode_status,

    input  logic mpc_debug_halt_req,
    output logic mpc_debug_halt_ack,
    input  logic mpc_debug_run_req,
    output logic mpc_debug_run_ack,
    input  logic mpc_reset_run_req,
    output logic debug_brkpt_status,
    // EXEC CTRL TMR
    output logic i_cpu_halt_req_veer[3],
    input  logic o_cpu_halt_ack_veer[3],
    output logic i_cpu_run_req_veer[3],
    input  logic o_cpu_run_ack_veer[3],
    input  logic o_cpu_halt_status_veer[3],
    input  logic o_debug_mode_status_veer[3],

    output logic mpc_debug_halt_req_veer[3],
    input  logic mpc_debug_halt_ack_veer[3],
    output logic mpc_debug_run_req_veer[3],
    input  logic mpc_debug_run_ack_veer[3],
    output logic mpc_reset_run_req_veer[3],
    input  logic debug_brkpt_status_veer[3],

    // Fault inputs
    input  el2_mubi_pkg::el2_mubi_t exec_fault_d[3],
    // Fault outputs
    output el2_mubi_pkg::el2_mubi_t exec_fault_q[3],
    // Fault clear inputs
    input  el2_mubi_pkg::el2_mubi_t exec_fault_clr[3]
);

  // ......................................................

  el2_mubi_t enable[3];
  el2_mubi_t exec_fault[3];
  el2_mubi_t crit_nc;

  logic [6:0] exec_ctrl_veer[3];
  logic [6:0] exec_ctrl_int;

  for (genvar i=0; i<3; i=i+1) begin
    assign exec_ctrl_veer[i] = {
      o_cpu_halt_ack_veer[i],
      o_cpu_run_ack_veer[i],
      o_cpu_halt_status_veer[i],
      o_debug_mode_status_veer[i],
      mpc_debug_halt_ack_veer[i],
      mpc_debug_run_ack_veer[i],
      debug_brkpt_status_veer[i]
    };
  end

  assign o_cpu_halt_ack      = exec_ctrl_int[6];
  assign o_cpu_run_ack       = exec_ctrl_int[5];
  assign o_cpu_halt_status   = exec_ctrl_int[4];
  assign o_debug_mode_status = exec_ctrl_int[3];
  assign mpc_debug_halt_ack  = exec_ctrl_int[2];
  assign mpc_debug_run_ack   = exec_ctrl_int[1];
  assign debug_brkpt_status  = exec_ctrl_int[0];

  el2_tmr_voter #(.Width($bits(exec_ctrl_int))) u_voter_exec_ctl (
    .in_a     (exec_ctrl_veer[0]),
    .in_b     (exec_ctrl_veer[1]),
    .in_c     (exec_ctrl_veer[2]),

    .en_a     (enable[0]),
    .en_b     (enable[1]),
    .en_c     (enable[2]),

    .out      (exec_ctrl_int),

    .fault_a  (exec_fault[0]),
    .fault_b  (exec_fault[1]),
    .fault_c  (exec_fault[2]),

    .critical (crit_nc)
  );

  // ......................................................

  // Fault aggregation and registers
  for (genvar i=0; i<3; i=i+1) begin : fault
    always_ff @(posedge clk or negedge rst_l) begin
      if (!rst_l) begin
        exec_fault_q[i] <= El2MuBiFalse;
      end else begin
        if (mubi_check_true(exec_fault_clr[i])) begin
          exec_fault_q[i] <= El2MuBiFalse;
        end else begin
          exec_fault_q[i] <= mubi_or3(exec_fault_q[i], exec_fault_d[i], exec_fault[i]);
        end
      end
    end

    assign enable[i] = mubi_not(exec_fault_q[i]);

  end

  // ......................................................

  // Propagate response to Cores
  for (genvar i=0; i < 3; i+=1) begin : resp
    assign i_cpu_halt_req_veer[i] = i_cpu_halt_req;
    assign i_cpu_run_req_veer[i] = i_cpu_run_req;

    assign mpc_debug_halt_req_veer[i] = mpc_debug_halt_req;
    assign mpc_debug_run_req_veer[i] = mpc_debug_run_req;
    assign mpc_reset_run_req_veer[i] = mpc_reset_run_req;
   end

endmodule
`endif
