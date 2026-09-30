//
// Copyright (c) 2026 Antmicro
// SPDX-License-Identifier: Apache-2.0

/*
  This module implements a fault state storage element. Internally, there are
  3 FFs which output is majority voted. The output is connected back to their
  inputs creating a self-correcting TMR storage. To control what's stored each
  FF input is ANDed with the clear signal and ORed with external fault
  detection signal. All signals use multi-bit logic
*/
`ifdef RV_TRIPLE_MODULAR_REDUNDANCY_ENABLE
module el2_tmr_fault_storage (
  input  logic  clk,
  input  logic  rst_l,

  input  el2_mubi_pkg::el2_mubi_t fault_i,  // Fault detection input
  output el2_mubi_pkg::el2_mubi_t fault_o,  // Fault state output
  input  el2_mubi_pkg::el2_mubi_t clr_i     // Fault clear input
);
  import el2_mubi_pkg::*;

  // Storage elements
  el2_mubi_pkg::el2_mubi_t fault[3];
  for (genvar i=0; i<3; i++) begin : storage
      rvmubidff dff (.*, .din(mubi_and(mubi_not(clr_i), mubi_or(fault_o, fault_i))), .dout(fault[i]));
  end

  // Majority voting
  rvtmr #(.WIDTH($bits(el2_mubi_t))) voter (.I(fault), .O(fault_o));

endmodule
`endif
