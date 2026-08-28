// Copyright 2026 Antmicro <www.antmicro.com>
// //
// // SPDX-License-Identifier: Apache-2.0
//
`ifdef RV_TRIPLE_MODULAR_REDUNDANCY_ENABLE
module el2_tmr_complex_clk
  import el2_pkg::*;
  import el2_mubi_pkg::*;
  import el2_lockstep_pkg::*;
#(
    `include "el2_param.vh"
) (
    input  logic clk,
    input  logic active_state_veer[3],
    output logic active_l2clk_veer[3],
    output logic free_l2clk_veer[3],
    output logic active_clk_veer[3],
    output logic free_clk_veer[3],
    output logic active_l2clk,
    output logic free_l2clk,
    output logic free_clk_int,

    input  logic lsu_bus_clk_en,
    input  logic ifu_bus_clk_en,
    input  logic dbg_bus_clk_en,
    input  logic dma_bus_clk_en,
    output logic lsu_bus_clk_en_veer[3],
    output logic ifu_bus_clk_en_veer[3],
    output logic dbg_bus_clk_en_veer[3],
    output logic dma_bus_clk_en_veer[3],

    input  logic dec_tlu_bus_clk_override_veer[3],
    input  logic pic_clk_override_veer[3],
    input  logic pic_io_clk_override_veer[3],
    output logic dec_tlu_bus_clk_override_int,
    output logic pic_clk_override_int,
    output logic pic_io_clk_override_int,
    // TODO: Add configuration signals
    input  logic scan_mode
);

  logic active_state_voted;

  // TODO: Add logic to correctly handle different configurations
  rvtmr #(.WIDTH(1)) active_state_voter (
    .I(active_state_veer),
    .O(active_state_voted)
  );

  // Active clock will only cost extra power
  // TODO: Add logic to correctly handle different configurations
  rvtmr  #(.WIDTH(1)) dec_tlu_bus_clk_override_voter (
    .I(dec_tlu_bus_clk_override_veer),
    .O(dec_tlu_bus_clk_override_int)
  );
  // TODO: Add logic to correctly handle different configurations
  rvtmr  #(.WIDTH(1)) pic_clk_override_voter (
    .I(pic_clk_override_veer),
    .O(pic_clk_override_int)
  );
  // TODO: Add logic to correctly handle different configurations
  rvtmr  #(.WIDTH(1)) pic_io_clk_override_voter (
    .I(pic_io_clk_override_veer),
    .O(pic_io_clk_override_int)
  );

  // Global CG
  rvoclkhdr free_cg2   ( .clk(clk), .en(1'b1),         .l1clk(free_l2clk), .* );
  rvoclkhdr active_cg2 ( .clk(clk), .en(active_state_voted), .l1clk(active_l2clk), .* );
  rvoclkhdr free_cg1   ( .clk(free_l2clk),     .en(1'b1), .l1clk(free_clk_int), .* );

  for (genvar i=0; i<3; i++) begin: pre_core_CG
    rvoclkhdr free_cg2   ( .clk(clk), .en(1'b1 /*Change to use config*/),         .l1clk(free_l2clk_veer[i]), .* );
    rvoclkhdr active_cg2 ( .clk(clk), .en(active_state_veer[i] /* Add core configuration*/), .l1clk(active_l2clk_veer[i]), .* );
    rvoclkhdr free_cg1   ( .clk(free_l2clk),     .en(1'b1), .l1clk(free_clk_veer[i]), .* );
    rvoclkhdr active_cg1 ( .clk(active_l2clk),   .en(1'b1), .l1clk(active_clk_veer[i]), .* );

    // Use control signals to gate clock
    assign lsu_bus_clk_en_veer[i] = lsu_bus_clk_en;
    assign ifu_bus_clk_en_veer[i] = ifu_bus_clk_en;
    assign dbg_bus_clk_en_veer[i] = dbg_bus_clk_en;
    assign dma_bus_clk_en_veer[i] = dma_bus_clk_en;
  end
endmodule
`endif
