// Copyright 2026 Antmicro <www.antmicro.com>
// //
// // SPDX-License-Identifier: Apache-2.0
//
//
module el2_tmr_dccm
  import el2_pkg::*;
  import el2_mubi_pkg::*;
  import el2_lockstep_pkg::*;
#(
    `include "el2_param.vh"
) (
    // DCCM
    output logic                            dccm_wren,
    output logic                            dccm_rden,
    output logic [pt.DCCM_BITS-1:0]         dccm_wr_addr_lo,
    output logic [pt.DCCM_BITS-1:0]         dccm_wr_addr_hi,
    output logic [pt.DCCM_BITS-1:0]         dccm_rd_addr_lo,
    output logic [pt.DCCM_BITS-1:0]         dccm_rd_addr_hi,
    output logic [pt.DCCM_FDATA_WIDTH-1:0]  dccm_wr_data_lo,
    output logic [pt.DCCM_FDATA_WIDTH-1:0]  dccm_wr_data_hi,

    input logic [pt.DCCM_FDATA_WIDTH-1:0]   dccm_rd_data_lo,
    input logic [pt.DCCM_FDATA_WIDTH-1:0]   dccm_rd_data_hi,

    // DCCM ECC status
    output logic                 dccm_ecc_single_error,
    output logic                 dccm_ecc_double_error,

    // DCCM TMR
    input  logic                           dccm_wren_veer[3],
    input  logic                           dccm_rden_veer[3],
    input  logic [pt.DCCM_BITS-1:0]        dccm_wr_addr_lo_veer[3],
    input  logic [pt.DCCM_BITS-1:0]        dccm_wr_addr_hi_veer[3],
    input  logic [pt.DCCM_BITS-1:0]        dccm_rd_addr_lo_veer[3],
    input  logic [pt.DCCM_BITS-1:0]        dccm_rd_addr_hi_veer[3],
    input  logic [pt.DCCM_FDATA_WIDTH-1:0] dccm_wr_data_lo_veer[3],
    input  logic [pt.DCCM_FDATA_WIDTH-1:0] dccm_wr_data_hi_veer[3],

    output logic [pt.DCCM_FDATA_WIDTH-1:0] dccm_rd_data_lo_veer[3],
    output logic [pt.DCCM_FDATA_WIDTH-1:0] dccm_rd_data_hi_veer[3],

    // DCCM ECC status
    output logic dccm_ecc_single_error_veer[3],
    output logic dccm_ecc_double_error_veer[3]
);

//TODO: Change it to use voters
  always_comb begin
    // Propagate response to Cores
    for (int i=0;i < 3; i+=1) begin
      dccm_rd_data_lo_veer[i] = dccm_rd_data_lo;
      dccm_rd_data_hi_veer[i] = dccm_rd_data_hi;
    end
    // Get value from Core 0 for the time being
    dccm_wren = dccm_wren_veer[0];
    dccm_rden = dccm_rden_veer[0];
    dccm_wr_addr_lo = dccm_wr_addr_lo_veer[0];
    dccm_wr_addr_hi = dccm_wr_addr_hi_veer[0];
    dccm_rd_addr_lo = dccm_rd_addr_lo_veer[0];
    dccm_rd_addr_hi = dccm_rd_addr_hi_veer[0];
    dccm_wr_data_lo = dccm_wr_data_lo_veer[0];
    dccm_wr_data_hi = dccm_wr_data_hi_veer[0];
    dccm_ecc_single_error = dccm_ecc_single_error_veer[0];
    dccm_ecc_double_error = dccm_ecc_double_error_veer[0];
  end


endmodule
