// Copyright 2026 Antmicro <www.antmicro.com>
// //
// // SPDX-License-Identifier: Apache-2.0
//
//
module el2_tmr_3way_fatal_check_mubi
#(
  parameter unsigned Width=1
)
(
  input  logic [Width-1:0] in[3],
  output el2_mubi_pkg::el2_mubi_t fatal
);

  logic cmp_t[3], cmp_c[3];
  assign cmp_t[0] = in[0] == in[1];
  assign cmp_t[1] = in[1] == in[2];
  assign cmp_t[2] = in[0] == in[2];
  assign cmp_c[0] = in[0] != in[1];
  assign cmp_c[1] = in[1] != in[2];
  assign cmp_c[2] = in[0] != in[2];

  for (genvar i=0; i < el2_mubi_pkg::El2MuBiWidth; ++i) begin : per_bit_voter
    if (!el2_mubi_pkg::El2MuBiTrue[i])
      rvtmr fatal_t_tmr(.I(cmp_t), .O(fatal[i]));
    else
      rvtmr fatal_c_tmr(.I(cmp_c), .O(fatal[i]));
  end
endmodule
