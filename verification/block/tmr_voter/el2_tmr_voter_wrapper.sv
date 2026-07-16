//
// Copyright (c) 2026 Antmicro
// SPDX-License-Identifier: Apache-2.0

module el2_tmr_voter_wrapper # (
  parameter unsigned Width = 1  // Signal width
) (

  // Clock
  //
  // The clock isn't needed for the wrapped module. But it is there in the
  // wrapper for the conveniance. After all the DUT will operate in a
  // syncrhonous environment
  input  logic clk_i,

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
  output el2_mubi_pkg::el2_mubi_t fault_c
);

  el2_rmt_voter #(.Width(Width)) dut (.*);

endmodule
