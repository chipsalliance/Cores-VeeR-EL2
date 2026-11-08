// Copyright 2026 Antmicro <www.antmicro.com>
// //
// // SPDX-License-Identifier: Apache-2.0
//
`ifdef RV_TRIPLE_MODULAR_REDUNDANCY_ENABLE
module el2_tmr_complex_clk
  import el2_pkg::*;
  import el2_mubi_pkg::*;
(
    input  logic clk,
    output logic clk_veer[3],

    output logic active_l2clk,
    output logic free_l2clk,
    output logic free_clk,

    input  logic active_state_veer[3],

    input  logic dec_tlu_bus_clk_override_veer[3],
    input  logic pic_clk_override_veer[3],
    input  logic pic_io_clk_override_veer[3],

    output logic dec_tlu_bus_clk_override_int,
    output logic pic_clk_override_int,
    output logic pic_io_clk_override_int,

    input  el2_mubi_pkg::el2_mubi_t core_active[3],

    input  logic scan_mode
);

  logic  active_state;
  assign active_state =
    (mubi_check_true(core_active[0]) & active_state_veer[0]) |
    (mubi_check_true(core_active[1]) & active_state_veer[1]) |
    (mubi_check_true(core_active[2]) & active_state_veer[2]);

  rvoclkhdr free_cg2   (.clk(clk),        .en(1'b1),         .l1clk(free_l2clk),   .* );
  rvoclkhdr free_cg1   (.clk(free_l2clk), .en(1'b1),         .l1clk(free_clk),     .* );
  rvoclkhdr active_cg2 (.clk(clk),        .en(active_state), .l1clk(active_l2clk), .* );

  // Per-core clock gate. Controlled by the boot configuration
  for (genvar i=0; i<3; i++) begin: pre_core_cg
    rvoclkhdr core_cg (.clk(clk), .en(mubi_check_true(core_active[i])), .l1clk(clk_veer[i]), .*);
  end

  // DEC TLU bus clock gate
  assign dec_tlu_bus_clk_override_int =
    (mubi_check_true(core_active[0]) & dec_tlu_bus_clk_override_veer[0]) |
    (mubi_check_true(core_active[1]) & dec_tlu_bus_clk_override_veer[1]) |
    (mubi_check_true(core_active[2]) & dec_tlu_bus_clk_override_veer[2]);

  // PIC clock gates
  assign pic_io_clk_override_int =
    (mubi_check_true(core_active[0]) & pic_io_clk_override_veer[0]) |
    (mubi_check_true(core_active[1]) & pic_io_clk_override_veer[1]) |
    (mubi_check_true(core_active[2]) & pic_io_clk_override_veer[2]);

  assign pic_clk_override_int =
    (mubi_check_true(core_active[0]) & pic_clk_override_veer[0]) |
    (mubi_check_true(core_active[1]) & pic_clk_override_veer[1]) |
    (mubi_check_true(core_active[2]) & pic_clk_override_veer[2]);

endmodule
`endif
