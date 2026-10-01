// Copyright (c) 2026 Antmicro
// SPDX-License-Identifier: Apache-2.

`ifdef RV_TRIPLE_MODULAR_REDUNDANCY_ENABLE
module el2_tmr_boot_configuration
  import el2_mubi_pkg::*;
(
  input  logic rst_l,
  input  logic clk,

  input  el2_mubi_t activate_core[3],

  output logic      mux_select_true[3],
  output logic      mux_select_false[3],

  input  logic scan_mode
);

  // Boot configuration can only be loaded after reset
  // Add redundant logic that will detect reset and allow configuration in the
  // first cycle after it.
  logic reset_observed [2];

  for (genvar i=0; i<2; i++) begin : reset_observed_logic
    logic [1:0] reset_ff;
    rvdff #(.WIDTH(2)) reset_observed_ff (
      .din({reset_ff[0], 1'b1}),
      .dout(reset_ff),
      .*);
    assign reset_observed[i] = ~|reset_ff;
  end

  logic [2:0] update_ff;
  logic clk_en;
  logic clk_reg;

  assign clk_en = reset_observed[0]|(|update_ff);

  // Gate clock
  rvoclkhdr clock_gate (.en(clk_en), .clk(clk), .scan_mode(scan_mode), .l1clk(clk_reg));

  for (genvar i=0; i<3; i++) begin : active_core_logic
    el2_mubi_t activate_core_r[3];
    el2_mubi_t activate_core_ns[3];
    el2_mubi_t activate_core_int[3];
    logic [2:0] state_differ;
    for (genvar j=0; j<3; j++) begin : redundant_logic
      rvdff #(.WIDTH(El2MuBiWidth)) active_core_ff (
        .din(activate_core_ns[j]),
        .dout(activate_core_r[j]),
        .clk(clk_reg),
        .*
      );
      rvtmr #(.WIDTH(El2MuBiWidth)) active_core_tmr (.I(activate_core_r), .O(activate_core_int[j]));
      assign activate_core_ns[j] = reset_observed[1] ? activate_core[i] : activate_core_int[j];
      assign state_differ[j] = activate_core_r[j] != activate_core_int[j];
    end
    assign update_ff[i] = |state_differ;
    assign mux_select_true[i]  = mubi_check_true(activate_core_int[0]);
    assign mux_select_false[i] = mubi_check_false(activate_core_int[0]);
  end
endmodule
`endif
