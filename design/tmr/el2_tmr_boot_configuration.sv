// Copyright (c) 2026 Antmicro
// SPDX-License-Identifier: Apache-2.

`ifdef RV_TRIPLE_MODULAR_REDUNDANCY_ENABLE
module el2_tmr_boot_configuration
  import el2_mubi_pkg::*;
(
  input  logic rst_l,
  input  logic clk,

  // Input active core selection from outside VeeR TMR complex
  input  el2_mubi_t core_active_i[3],
  // Output latched active core selection
  output el2_mubi_t core_active_o[3],

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
    el2_mubi_t  core_active_r[3];
    el2_mubi_t  core_active_ns;
    el2_mubi_t  core_active_int;
    logic [2:0] state_differ;

    for (genvar j=0; j<3; j++) begin : redundant_logic
      rvmubidff active_core_ff (
        .din(core_active_ns),
        .dout(core_active_r[j]),
        .clk(clk_reg),
        .*
      );
      assign state_differ[j] = core_active_r[j] != core_active_int;
    end

    rvtmr #(.WIDTH(El2MuBiWidth)) active_core_tmr (.I(core_active_r), .O(core_active_int));
    assign core_active_ns = reset_observed[1] ? core_active_i[i] : core_active_int;
    assign update_ff[i] = |state_differ;

    // Output
    assign core_active_o[i] = core_active_int;
  end

endmodule
`endif
