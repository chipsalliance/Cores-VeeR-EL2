//
// Copyright (c) 2026 Antmicro
// SPDX-License-Identifier: Apache-2.0

module el2_tmr_axi_rdy (

  input  logic  clk_i,
  input  logic  rst_ni,

  // Ready inputs
  input  logic  ready_a_i,
  input  logic  ready_b_i,
  input  logic  ready_c_i,

  // Channel fault output
  output el2_mubi_pkg::el2_mubi_t  fault_a_o,
  output el2_mubi_pkg::el2_mubi_t  fault_b_o,
  output el2_mubi_pkg::el2_mubi_t  fault_c_o,

  // External fault input
  input  el2_mubi_pkg::el2_mubi_t  fault_a_i,
  input  el2_mubi_pkg::el2_mubi_t  fault_b_i,
  input  el2_mubi_pkg::el2_mubi_t  fault_c_i,

  // Fault clear
  input  el2_mubi_pkg::el2_mubi_t  fault_clr_a_i,
  input  el2_mubi_pkg::el2_mubi_t  fault_clr_b_i,
  input  el2_mubi_pkg::el2_mubi_t  fault_clr_c_i,

  // Ready output
  output logic  ready_o
);
  import el2_mubi_pkg::*;

  el2_mubi_t enable_a;
  el2_mubi_t enable_b;
  el2_mubi_t enable_c;

  el2_mubi_t fault     [3];
  el2_mubi_t fault_d   [3];
  el2_mubi_t fault_q   [3];
  el2_mubi_t fault_clr [3];

  el2_mubi_t crit_nc; // Unused

  // ......................................................
  // Voter

  el2_tmr_voter #(.Width(1)) x_voter (
    .in_a     (ready_a_i),
    .in_b     (ready_b_i),
    .in_c     (ready_c_i),

    .en_a     (enable_a),
    .en_b     (enable_b),
    .en_c     (enable_c),

    .out      (ready_o),

    .fault_a  (fault[0]),
    .fault_b  (fault[1]),
    .fault_c  (fault[2]),

    .critical (crit_nc)
  );

  // ......................................................
  // Local and external fault OR gates

  assign fault_d[0] = mubi_or(fault_a_i, fault[0]);
  assign fault_d[1] = mubi_or(fault_b_i, fault[1]);
  assign fault_d[2] = mubi_or(fault_c_i, fault[2]);

  // ......................................................
  // Fault state register

  assign fault_clr[0] = fault_clr_a_i;
  assign fault_clr[1] = fault_clr_b_i;
  assign fault_clr[2] = fault_clr_c_i;

  generate for (genvar i=0; i<3; i=i+1) begin : fault_ff
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        fault_q[i] <= El2MuBiFalse;
      end else begin
        if (mubi_check_true(fault_clr[i])) begin
          fault_q[i] <= El2MuBiFalse;
        end else begin
          fault_q[i] <= mubi_or(fault_q[i], fault_d[i]);
        end
      end
    end
  end endgenerate

  // Fault outputs (registered)
  assign fault_a_o = fault_q[0];
  assign fault_b_o = fault_q[1];
  assign fault_c_o = fault_q[2];

  // Voter input enable
  assign enable_a = mubi_not(fault_q[0]);
  assign enable_b = mubi_not(fault_q[1]);
  assign enable_c = mubi_not(fault_q[2]);

endmodule
