// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Generic optimization-barrier buffer that is the default implementation
// behind el2_prim_buf.
//
// WARNING: This is a plain functional buffer. It is NOT constrained for
// synthesis - it carries no keep / size_only / dont_touch attribute. As
// shipped, a synthesis tool MAY optimize this buffer away.
//
// Integrators targeting silicon (or FI/safety hardening) MUST either:
//   * constrain this module in their synthesis flow or
//   * override RV_PRIM_BUF_IMPL with an already-constrained primitive
//     (e.g. caliptra_prim_buf).

module el2_prim_generic_buf #(
  parameter int Width = 1
) (
  input        [Width-1:0] in_i,
  output logic [Width-1:0] out_o
);

  logic [Width-1:0] inv;
  assign inv = ~in_i;
  assign out_o = ~inv;

endmodule
