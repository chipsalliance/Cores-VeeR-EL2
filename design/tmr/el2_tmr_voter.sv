//
// Copyright (c) 2026 Antmicro
// SPDX-License-Identifier: Apache-2.0

`ifdef RV_TRIPLE_MODULAR_REDUNDANCY_ENABLE

module el2_tmr_voter # (
  parameter unsigned Width = 1  // Signal width
) (
  // Inputs to the voter
  input  logic [Width-1:0] in_a,
  input  logic [Width-1:0] in_b,
  input  logic [Width-1:0] in_c,

  // Input enable
  input  el2_mubi_pkg::el2_mubi_t en_a,
  input  el2_mubi_pkg::el2_mubi_t en_b,
  input  el2_mubi_pkg::el2_mubi_t en_c,

  // Majority voter output
  output logic [Width-1:0] out,

  // Fault indicators
  output el2_mubi_pkg::el2_mubi_t fault_a,
  output el2_mubi_pkg::el2_mubi_t fault_b,
  output el2_mubi_pkg::el2_mubi_t fault_c,

  // Critical (unrecoverable) fault inidicator
  output el2_mubi_pkg::el2_mubi_t critical

);
  import el2_mubi_pkg::*;

  logic [Width-1:0] in[3];
  el2_mubi_t        en[3];

  assign in = '{in_a, in_b, in_c}; 
  assign en = '{en_a, en_b, en_c}; 

  // Majority voting
  rvtmr #(.WIDTH(Width)) voter (
    .I (in),
    .O (out)
  );

  // Fault detection
  el2_mubi_t fault[3];
  for (genvar i=0; i<3; ++i) begin : fault_detection

    // Compare bit-by-bit and OR reduce
    el2_mubi_t neq_any;
    always_comb begin
      neq_any = El2MuBiFalse;
      for (int j=0; j<Width; ++j) begin
        neq_any = mubi_or(neq_any, mubi_from_bool(in[i][j] ^ out[j]));
      end
    end

    // Gate with enable
    assign fault[i] = mubi_or(neq_any, mubi_not(en[i]));
  end  

  // Map outputs
  assign fault_a = fault[0];
  assign fault_b = fault[1];
  assign fault_c = fault[2];

  // Critical output
  rvtmr #(.WIDTH($bits(el2_mubi_t))) critical_tmr (
    .I (fault),
    .O (critical)
  );

endmodule

`endif
