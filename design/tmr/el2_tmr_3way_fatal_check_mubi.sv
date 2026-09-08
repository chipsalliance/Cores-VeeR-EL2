// Copyright 2026 Antmicro <www.antmicro.com>
// //
// // SPDX-License-Identifier: Apache-2.0
//

// Compare 2 out of 3 inputs 'in' based on the 'faulty_core' value.
// Sets 'fatal' to El2MuBiTrue when at least one of the inputs is marked as
// faulty and remaining 2 differ.

module el2_tmr_3way_fatal_check_mubi
#(
  parameter unsigned Width=1
)
(
  input  logic [Width-1:0] in[3],
  input  el2_mubi_pkg::el2_mubi_t faulty_core[3],
  output el2_mubi_pkg::el2_mubi_t fatal
);

  logic cmp_t[3], cmp_c[3];
  assign cmp_t[0] = in[0] == in[1] & el2_mubi_pkg::mubi_check_true(faulty_core[2]);
  assign cmp_t[1] = in[1] == in[2] & el2_mubi_pkg::mubi_check_true(faulty_core[0]);
  assign cmp_t[2] = in[0] == in[2] & el2_mubi_pkg::mubi_check_true(faulty_core[1]);
  assign cmp_c[0] = in[0] != in[1] | el2_mubi_pkg::mubi_check_false(faulty_core[2]);
  assign cmp_c[1] = in[1] != in[2] | el2_mubi_pkg::mubi_check_false(faulty_core[0]);
  assign cmp_c[2] = in[0] != in[2] | el2_mubi_pkg::mubi_check_false(faulty_core[1]);
  el2_mubi_pkg::el2_mubi_t internal[3];

  for (genvar j=0; j < 3; ++j) begin : internal_mubi
    for (genvar i=0; i < el2_mubi_pkg::El2MuBiWidth; ++i) begin : per_bit_voter
      if (el2_mubi_pkg::El2MuBiFalse[i])
        assign internal[j][i] = cmp_t[j];
      else
        assign internal[j][i] = cmp_c[j];
    end
  end
  assign fatal = el2_mubi_pkg::mubi_and(
    el2_mubi_pkg::mubi_and3(internal[0], internal[1], internal[2]),
    el2_mubi_pkg::mubi_or3(faulty_core[0], faulty_core[1], faulty_core[2])
  );
endmodule
