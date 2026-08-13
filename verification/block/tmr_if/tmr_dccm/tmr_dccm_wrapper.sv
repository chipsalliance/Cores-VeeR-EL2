// Copyright 2026 Antmicro <www.antmicro.com>
//
// SPDX-License-Identifier: Apache-2.0
//
module tmr_dccm_wrapper
  import el2_pkg::*;
  import el2_mubi_pkg::*;
#(
    `include "el2_param.vh"
) (
    input logic clk,
    input  logic rst_l,

    // DCCM Memory
    output logic [pt.DCCM_NUM_BANKS-1:0]                                       dccm_clken,
    output logic [pt.DCCM_NUM_BANKS-1:0]                                       dccm_wren_bank,
    output logic [pt.DCCM_NUM_BANKS-1:0][pt.DCCM_BITS-1:(pt.DCCM_BANK_BITS+2)] dccm_addr_bank,
    output logic [pt.DCCM_NUM_BANKS-1:0][              pt.DCCM_DATA_WIDTH-1:0] dccm_wr_data_bank,
    output logic [pt.DCCM_NUM_BANKS-1:0][               pt.DCCM_ECC_WIDTH-1:0] dccm_wr_ecc_bank,

    input logic [pt.DCCM_NUM_BANKS-1:0][              pt.DCCM_DATA_WIDTH-1:0] dccm_bank_dout,
    input logic [pt.DCCM_NUM_BANKS-1:0][               pt.DCCM_ECC_WIDTH-1:0] dccm_bank_ecc,

    // DCCM TMR
    input logic [pt.DCCM_NUM_BANKS-1:0]                                       dccm_clken_veer[3],
    input logic [pt.DCCM_NUM_BANKS-1:0]                                       dccm_wren_bank_veer[3],
    input logic [pt.DCCM_NUM_BANKS-1:0][pt.DCCM_BITS-1:(pt.DCCM_BANK_BITS+2)] dccm_addr_bank_veer[3],
    input logic [pt.DCCM_NUM_BANKS-1:0][              pt.DCCM_DATA_WIDTH-1:0] dccm_wr_data_bank_veer[3],
    input logic [pt.DCCM_NUM_BANKS-1:0][               pt.DCCM_ECC_WIDTH-1:0] dccm_wr_ecc_bank_veer[3],

    output logic [pt.DCCM_NUM_BANKS-1:0][              pt.DCCM_DATA_WIDTH-1:0] dccm_bank_dout_veer[3],
    output logic [pt.DCCM_NUM_BANKS-1:0][               pt.DCCM_ECC_WIDTH-1:0] dccm_bank_ecc_veer[3],

    // Fault inputs
    input  el2_mubi_pkg::el2_mubi_t dccm_fault_d[3],
    // Fault outputs
    output el2_mubi_pkg::el2_mubi_t dccm_fault_q[3],
    // Fault clear inputs
    input  el2_mubi_pkg::el2_mubi_t dccm_fault_clr[3]
);

  el2_mem_if local_mem_export();
  el2_mem_if local_mem_export_veer[3]();

  // DCCM Memory
  assign dccm_clken        = local_mem_export.dccm_clken;
  assign dccm_wren_bank    = local_mem_export.dccm_wren_bank;
  assign dccm_addr_bank    = local_mem_export.dccm_addr_bank;
  assign dccm_wr_data_bank = local_mem_export.dccm_wr_data_bank;
  assign dccm_wr_ecc_bank  = local_mem_export.dccm_wr_ecc_bank;
  assign local_mem_export.dccm_bank_dout = dccm_bank_dout;
  assign local_mem_export.dccm_bank_ecc  = dccm_bank_ecc;

  // DCCM TMR
  for(genvar i = 0; i < 3; i++) begin
    assign local_mem_export_veer[i].dccm_clken         = dccm_clken_veer[i];
    assign local_mem_export_veer[i].dccm_wren_bank     = dccm_wren_bank_veer[i];
    assign local_mem_export_veer[i].dccm_addr_bank     = dccm_addr_bank_veer[i];
    assign local_mem_export_veer[i].dccm_wr_data_bank  = dccm_wr_data_bank_veer[i];
    assign local_mem_export_veer[i].dccm_wr_ecc_bank   = dccm_wr_ecc_bank_veer[i];
    assign dccm_bank_dout_veer[i] = local_mem_export_veer[i].dccm_bank_dout;
    assign dccm_bank_ecc_veer[i]  = local_mem_export_veer[i].dccm_bank_ecc;
  end

  el2_tmr_dccm #(.pt(pt)) el2_tmr_dccm_u (
    .dccm_export(local_mem_export.veer_dccm),
    .dccm_export_veer(local_mem_export_veer.veer_dccm_sink),
    .*
  );
endmodule
