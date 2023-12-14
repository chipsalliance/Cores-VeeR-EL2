// Copyright (c) 2023 Antmicro <www.antmicro.com>
// SPDX-License-Identifier: Apache-2.0

module el2_lsu_dccm_mem_wrapper
  import el2_pkg::*;
#(
    `include "el2_param.vh"
) (
    input logic clk,
    input logic active_clk,
    input logic rst_l,
    input logic clk_override,

    input logic dccm_wren,
    input logic dccm_rden,
    input logic [pt.DCCM_BITS-1:0] dccm_wr_addr_lo,
    input logic [pt.DCCM_BITS-1:0] dccm_wr_addr_hi,
    input logic [pt.DCCM_BITS-1:0] dccm_rd_addr_lo,
    input logic [pt.DCCM_BITS-1:0] dccm_rd_addr_hi,
    input logic [pt.DCCM_FDATA_WIDTH-1:0] dccm_wr_data_lo,
    input logic [pt.DCCM_FDATA_WIDTH-1:0] dccm_wr_data_hi,

    // el2_dccm_ext_in_pkt_t
    input logic dccm_ext_in_pkt_TEST1,
    input logic dccm_ext_in_pkt_RME,
    input logic [3:0] dccm_ext_in_pkt_RM,
    input logic dccm_ext_in_pkt_LS,
    input logic dccm_ext_in_pkt_DS,
    input logic dccm_ext_in_pkt_SD,
    input logic dccm_ext_in_pkt_TEST_RNM,
    input logic dccm_ext_in_pkt_BC1,
    input logic dccm_ext_in_pkt_BC2,

    output logic [pt.DCCM_FDATA_WIDTH-1:0] dccm_rd_data_lo,
    output logic [pt.DCCM_FDATA_WIDTH-1:0] dccm_rd_data_hi,

    input logic scan_mode
);

  localparam DCCM_ECC_WIDTH = pt.DCCM_FDATA_WIDTH - pt.DCCM_DATA_WIDTH;

  logic [pt.DCCM_NUM_BANKS-1:0]                                       dccm_clken;
  logic [pt.DCCM_NUM_BANKS-1:0]                                       dccm_wren_bank;
  logic [pt.DCCM_NUM_BANKS-1:0][pt.DCCM_BITS-1:(pt.DCCM_BANK_BITS+2)] dccm_addr_bank;
  logic [pt.DCCM_NUM_BANKS-1:0][              pt.DCCM_DATA_WIDTH-1:0] dccm_wr_data_bank;
  logic [pt.DCCM_NUM_BANKS-1:0][                  DCCM_ECC_WIDTH-1:0] dccm_wr_ecc_bank;
  logic [pt.DCCM_NUM_BANKS-1:0][              pt.DCCM_DATA_WIDTH-1:0] dccm_bank_dout;
  logic [pt.DCCM_NUM_BANKS-1:0][                  DCCM_ECC_WIDTH-1:0] dccm_bank_ecc;

  logic [pt.DCCM_NUM_BANKS-1:0][             pt.DCCM_FDATA_WIDTH-1:0] dccm_wr_fdata_bank;
  logic [pt.DCCM_NUM_BANKS-1:0][             pt.DCCM_FDATA_WIDTH-1:0] dccm_bank_fdout;

  el2_mem_if mem_export ();
  assign dccm_clken                = mem_export.dccm_clken;
  assign dccm_wren_bank            = mem_export.dccm_wren_bank;
  assign dccm_addr_bank            = mem_export.dccm_addr_bank;
  assign dccm_wr_data_bank         = mem_export.dccm_wr_data_bank;
  assign dccm_wr_ecc_bank          = mem_export.dccm_wr_ecc_bank;
  assign mem_export.dccm_bank_dout = dccm_bank_dout;
  assign mem_export.dccm_bank_ecc  = dccm_bank_ecc;

  // Pack dccm_ext_in_pkt
  el2_dccm_ext_in_pkt_t [pt.DCCM_NUM_BANKS-1:0] dccm_ext_in_pkt;

  for (genvar i = 0; i < pt.DCCM_NUM_BANKS; i++) begin : gen_dccm_ext_pkt
    assign dccm_ext_in_pkt[i].TEST1    = dccm_ext_in_pkt_TEST1;
    assign dccm_ext_in_pkt[i].RME      = dccm_ext_in_pkt_RME;
    assign dccm_ext_in_pkt[i].RM       = dccm_ext_in_pkt_RM;
    assign dccm_ext_in_pkt[i].LS       = dccm_ext_in_pkt_LS;
    assign dccm_ext_in_pkt[i].DS       = dccm_ext_in_pkt_DS;
    assign dccm_ext_in_pkt[i].SD       = dccm_ext_in_pkt_SD;
    assign dccm_ext_in_pkt[i].TEST_RNM = dccm_ext_in_pkt_TEST_RNM;
    assign dccm_ext_in_pkt[i].BC1      = dccm_ext_in_pkt_BC1;
    assign dccm_ext_in_pkt[i].BC2      = dccm_ext_in_pkt_BC2;
  end : gen_dccm_ext_pkt

  localparam DCCM_INDEX_DEPTH = ((pt.DCCM_SIZE)*1024)/((pt.DCCM_BYTE_WIDTH)*(pt.DCCM_NUM_BANKS));  // Depth of memory bank

  // 8 Banks, 16KB each (2048 x 72)
  for (genvar i = 0; i < pt.DCCM_NUM_BANKS; i++) begin : gen_dccm_mem
    assign dccm_wr_fdata_bank[i] = {
      mem_export.dccm_wr_ecc_bank[i], mem_export.dccm_wr_data_bank[i]
    };
    assign mem_export.dccm_bank_dout[i] = dccm_bank_fdout[i][pt.DCCM_DATA_WIDTH-1:0];
    assign mem_export.dccm_bank_ecc[i] = dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:pt.DCCM_DATA_WIDTH];

    el2_ram #(DCCM_INDEX_DEPTH, 39) ram (
        // Primary ports
        .ME(dccm_clken[i]),
        .CLK(clk),
        .WE(dccm_wren_bank[i]),
        .ADR(dccm_addr_bank[i]),
        .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
        .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
        .ROP(),
        // These are used by SoC
        .TEST1(dccm_ext_in_pkt[i].TEST1),
        .RME(dccm_ext_in_pkt[i].RME),
        .RM(dccm_ext_in_pkt[i].RM),
        .LS(dccm_ext_in_pkt[i].LS),
        .DS(dccm_ext_in_pkt[i].DS),
        .SD(dccm_ext_in_pkt[i].SD),
        .TEST_RNM(dccm_ext_in_pkt[i].TEST_RNM),
        .BC1(dccm_ext_in_pkt[i].BC1),
        .BC2(dccm_ext_in_pkt[i].BC2),
        .*
    );
  end : gen_dccm_mem

  el2_lsu_dccm_mem mem (
      .dccm_mem_export(mem_export.veer_dccm),
      .*
  );

endmodule
