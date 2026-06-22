// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Standalone default. Integrators (e.g. Caliptra) redirect this to their own
// barrier primitive by defining RV_PRIM_BUF_IMPL (same Width/in_i/out_o interface).
`ifndef RV_PRIM_BUF_IMPL
  `define RV_PRIM_BUF_IMPL el2_prim_generic_buf
`endif

module el2_prim_buf #(
  parameter int Width = 1
) (
  input        [Width-1:0] in_i,
  output logic [Width-1:0] out_o
);
  `RV_PRIM_BUF_IMPL #(.Width(Width)) u_impl (.in_i(in_i), .out_o(out_o));
endmodule
