// Copyright 2026 Antmicro <www.antmicro.com>
//
// SPDX-License-Identifier: Apache-2.0
//
module tmr_iccm_wrapper
  import el2_pkg::*;
  import el2_mubi_pkg::*;
#(
    `include "el2_param.vh"
) (
    input logic clk,
    input  logic rst_l,

    // DCCM Memory
    output logic [pt.ICCM_NUM_BANKS-1:0]                                       iccm_clken,
    output logic [pt.ICCM_NUM_BANKS-1:0]                                       iccm_wren_bank,
    output logic [pt.ICCM_NUM_BANKS-1:0][pt.ICCM_BITS-1:pt.ICCM_BANK_INDEX_LO] iccm_addr_bank,
    output logic [pt.ICCM_NUM_BANKS-1:0][                                31:0] iccm_bank_wr_data,
    output logic [pt.ICCM_NUM_BANKS-1:0][               pt.ICCM_ECC_WIDTH-1:0] iccm_bank_wr_ecc,
    input  logic [pt.ICCM_NUM_BANKS-1:0][                                31:0] iccm_bank_dout,
    input  logic [pt.ICCM_NUM_BANKS-1:0][               pt.ICCM_ECC_WIDTH-1:0] iccm_bank_ecc,

    // DCCM TMR
    input  logic [pt.ICCM_NUM_BANKS-1:0]                                       iccm_clken_veer[3],
    input  logic [pt.ICCM_NUM_BANKS-1:0]                                       iccm_wren_bank_veer[3],
    input  logic [pt.ICCM_NUM_BANKS-1:0][pt.ICCM_BITS-1:pt.ICCM_BANK_INDEX_LO] iccm_addr_bank_veer[3],
    input  logic [pt.ICCM_NUM_BANKS-1:0][                                31:0] iccm_bank_wr_data_veer[3],
    input  logic [pt.ICCM_NUM_BANKS-1:0][               pt.ICCM_ECC_WIDTH-1:0] iccm_bank_wr_ecc_veer[3],
    output logic [pt.ICCM_NUM_BANKS-1:0][                                31:0] iccm_bank_dout_veer[3],
    output logic [pt.ICCM_NUM_BANKS-1:0][               pt.ICCM_ECC_WIDTH-1:0] iccm_bank_ecc_veer[3],

    // Fault inputs
    input  el2_mubi_pkg::el2_mubi_t iccm_fault_d[3],
    // Fault outputs
    output el2_mubi_pkg::el2_mubi_t iccm_fault_q[3],
    // Fault clear inputs
    input  el2_mubi_pkg::el2_mubi_t iccm_fault_clr[3]
);

  el2_mem_if local_mem_export();
  el2_mem_if local_mem_export_veer[3]();

  // DCCM Memory
  assign iccm_clken         = local_mem_export.iccm_clken;
  assign iccm_wren_bank     = local_mem_export.iccm_wren_bank;
  assign iccm_addr_bank     = local_mem_export.iccm_addr_bank;
  assign iccm_bank_wr_data  = local_mem_export.iccm_bank_wr_data;
  assign iccm_bank_wr_ecc   = local_mem_export.iccm_bank_wr_ecc;
  assign local_mem_export.iccm_bank_dout = iccm_bank_dout;
  assign local_mem_export.iccm_bank_ecc  = iccm_bank_ecc;

  // DCCM TMR
  for(genvar i = 0; i < 3; i++) begin
    assign local_mem_export_veer[i].iccm_clken         = iccm_clken_veer[i];
    assign local_mem_export_veer[i].iccm_wren_bank     = iccm_wren_bank_veer[i];
    assign local_mem_export_veer[i].iccm_addr_bank     = iccm_addr_bank_veer[i];
    assign local_mem_export_veer[i].iccm_bank_wr_data  = iccm_bank_wr_data_veer[i];
    assign local_mem_export_veer[i].iccm_bank_wr_ecc   = iccm_bank_wr_ecc_veer[i];
    assign iccm_bank_dout_veer[i] = local_mem_export_veer[i].iccm_bank_dout;
    assign iccm_bank_ecc_veer[i]  = local_mem_export_veer[i].iccm_bank_ecc;
  end

  el2_tmr_iccm #(.pt(pt)) el2_tmr_iccm_u (
    .iccm_export(local_mem_export.veer_iccm),
    .iccm_export_veer(local_mem_export_veer.veer_iccm_sink),
    .*
  );
endmodule
