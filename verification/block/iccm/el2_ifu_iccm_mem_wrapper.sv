// Copyright (c) 2023 Antmicro <www.antmicro.com>
// SPDX-License-Identifier: Apache-2.0

module el2_ifu_iccm_mem_wrapper
  import el2_pkg::*;
#(
    `include "el2_param.vh"
) (
    input logic clk,
    input logic active_clk,
    input logic rst_l,
    input logic clk_override,

    input logic iccm_wren,
    input logic iccm_rden,
    input logic [pt.ICCM_BITS-1:1] iccm_rw_addr,
    input logic iccm_buf_correct_ecc,
    input logic iccm_correction_state,
    input logic [2:0] iccm_wr_size,
    input logic [77:0] iccm_wr_data,

    // Unwrapped iccm_ext_in_pkt
    input logic iccm_ext_in_pkt_TEST1,
    input logic iccm_ext_in_pkt_RME,
    input logic [3:0] iccm_ext_in_pkt_RM,
    input logic iccm_ext_in_pkt_LS,
    input logic iccm_ext_in_pkt_DS,
    input logic iccm_ext_in_pkt_SD,
    input logic iccm_ext_in_pkt_TEST_RNM,
    input logic iccm_ext_in_pkt_BC1,
    input logic iccm_ext_in_pkt_BC2,

    output logic [63:0] iccm_rd_data,
    output logic [77:0] iccm_rd_data_ecc,
    input logic scan_mode
);

  logic [pt.ICCM_NUM_BANKS-1:0]                                       iccm_clken;
  logic [pt.ICCM_NUM_BANKS-1:0]                                       iccm_wren_bank;
  logic [pt.ICCM_NUM_BANKS-1:0][pt.ICCM_BITS-1:pt.ICCM_BANK_INDEX_LO] iccm_addr_bank;
  logic [pt.ICCM_NUM_BANKS-1:0][                                31:0] iccm_bank_wr_data;
  logic [pt.ICCM_NUM_BANKS-1:0][                                 6:0] iccm_bank_wr_ecc;
  logic [pt.ICCM_NUM_BANKS-1:0][                                31:0] iccm_bank_dout;
  logic [pt.ICCM_NUM_BANKS-1:0][                                 6:0] iccm_bank_ecc;

  logic [pt.ICCM_NUM_BANKS-1:0][                                38:0] iccm_bank_wr_fdata;
  logic [pt.ICCM_NUM_BANKS-1:0][                                38:0] iccm_bank_fdout;

  el2_mem_if mem_export ();
  assign iccm_clken                = mem_export.iccm_clken;
  assign iccm_wren_bank            = mem_export.iccm_wren_bank;
  assign iccm_addr_bank            = mem_export.iccm_addr_bank;
  assign iccm_bank_wr_data         = mem_export.iccm_bank_wr_data;
  assign iccm_bank_wr_ecc          = mem_export.iccm_bank_wr_ecc;
  assign mem_export.iccm_bank_dout = iccm_bank_dout;
  assign mem_export.iccm_bank_ecc  = iccm_bank_ecc;

  // Pack el2_ccm_ext_in_pkt_t
  el2_ccm_ext_in_pkt_t [pt.ICCM_NUM_BANKS-1:0] iccm_ext_in_pkt;

  for (genvar i = 0; i < pt.ICCM_NUM_BANKS; i++) begin : gen_iccm_ext_pkt
    assign iccm_ext_in_pkt[i].TEST1 = iccm_ext_in_pkt_TEST1;
    assign iccm_ext_in_pkt[i].RME = iccm_ext_in_pkt_RME;
    assign iccm_ext_in_pkt[i].RM = iccm_ext_in_pkt_RM;
    assign iccm_ext_in_pkt[i].LS = iccm_ext_in_pkt_LS;
    assign iccm_ext_in_pkt[i].DS = iccm_ext_in_pkt_DS;
    assign iccm_ext_in_pkt[i].SD = iccm_ext_in_pkt_SD;
    assign iccm_ext_in_pkt[i].TEST_RNM = iccm_ext_in_pkt_TEST_RNM;
    assign iccm_ext_in_pkt[i].BC1 = iccm_ext_in_pkt_BC1;
    assign iccm_ext_in_pkt[i].BC2 = iccm_ext_in_pkt_BC2;
  end : gen_iccm_ext_pkt

  // The ICCM module
  for (genvar i = 0; i < pt.ICCM_NUM_BANKS; i++) begin : gen_iccm_mem
    assign iccm_bank_wr_fdata[i] = {
      mem_export.iccm_bank_wr_ecc[i], mem_export.iccm_bank_wr_data[i]
    };
    assign mem_export.iccm_bank_dout[i] = iccm_bank_fdout[i][31:0];
    assign mem_export.iccm_bank_ecc[i] = iccm_bank_fdout[i][38:32];

    el2_ram #(
        .depth(1 << pt.ICCM_INDEX_BITS),
        .width(39)
    ) iccm_bank (
        // Primary ports
        .ME(iccm_clken[i]),
        .CLK(clk),
        .WE(iccm_wren_bank[i]),
        .ADR(iccm_addr_bank[i]),
        .D(iccm_bank_wr_fdata[i][38:0]),
        .Q(iccm_bank_fdout[i][38:0]),
        .ROP(),
        // These are used by SoC
        .TEST1(iccm_ext_in_pkt[i].TEST1),
        .RME(iccm_ext_in_pkt[i].RME),
        .RM(iccm_ext_in_pkt[i].RM),
        .LS(iccm_ext_in_pkt[i].LS),
        .DS(iccm_ext_in_pkt[i].DS),
        .SD(iccm_ext_in_pkt[i].SD),
        .TEST_RNM(iccm_ext_in_pkt[i].TEST_RNM),
        .BC1(iccm_ext_in_pkt[i].BC1),
        .BC2(iccm_ext_in_pkt[i].BC2)
    );
  end : gen_iccm_mem

  el2_ifu_iccm_mem mem (
      .iccm_mem_export(mem_export.veer_iccm),
      .*
  );

endmodule
