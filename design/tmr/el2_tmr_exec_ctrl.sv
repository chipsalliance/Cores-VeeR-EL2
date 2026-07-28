// Copyright 2026 Antmicro <www.antmicro.com>
// //
// // SPDX-License-Identifier: Apache-2.0
//
`ifdef RV_TRIPLE_MODULAR_REDUNDANCY_ENABLE
module el2_tmr_exec_ctrl
  import el2_pkg::*;
  import el2_mubi_pkg::*;
  import el2_lockstep_pkg::*;
#(
    `include "el2_param.vh"
) (
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
    input  logic debug_brkpt_status_veer[3]
);

//TODO: Change it to use voters
  always_comb begin
    // Propagate response to Cores
    for (int i=0;i < 3; i+=1) begin
      i_cpu_halt_req_veer[i] = i_cpu_halt_req;
      i_cpu_run_req_veer[i] = i_cpu_run_req;

      mpc_debug_halt_req_veer[i] = mpc_debug_halt_req;
      mpc_debug_run_req_veer[i] = mpc_debug_run_req;
      mpc_reset_run_req_veer[i] = mpc_reset_run_req;
    end
    // Get value from Core 0 for the time being
    o_cpu_halt_ack = o_cpu_halt_ack_veer[0];
    o_cpu_halt_status = o_cpu_halt_status_veer[0];
    o_cpu_run_ack = o_cpu_run_ack_veer[0];
    o_debug_mode_status = o_debug_mode_status_veer[0];

    mpc_debug_halt_ack = mpc_debug_halt_ack_veer[0];
    mpc_debug_run_ack = mpc_debug_run_ack_veer[0];
    debug_brkpt_status = debug_brkpt_status_veer[0];
  end

endmodule
`endif
