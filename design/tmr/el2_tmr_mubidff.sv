//
// Copyright (c) 2026 Antmicro
// SPDX-License-Identifier: Apache-2.0

/*
   The module is used to store a el2_mubi_t value. It resets to El2MuBiFalse.
   The implementation uses a regular rvdff plus inverters (via static XOR)
*/
`ifdef RV_TRIPLE_MODULAR_REDUNDANCY_ENABLE
module el2_tmr_mubidff # (
   localparam unsigned WIDTH = $bits(el2_mubi_pkg::el2_mubi_t)
)(
   input  logic              clk,
   input  logic              rst_l,
   input  logic [WIDTH-1:0]  din,
   output logic [WIDTH-1:0]  dout
);

   logic [WIDTH-1:0] dff_d;
   logic [WIDTH-1:0] dff_q;

   assign dff_d = din ^ el2_mubi_pkg::El2MuBiFalse;
   rvdff #(WIDTH) dff (.*, .din(dff_d), .dout(dff_q));
   assign dout = dff_q ^ el2_mubi_pkg::El2MuBiFalse;

endmodule
`endif
