// Copyright 2026 Antmicro <www.antmicro.com>
// //
// // SPDX-License-Identifier: Apache-2.0
//
//
module el2_tmr_iccm
  import el2_pkg::*;
  import el2_mubi_pkg::*;
  import el2_lockstep_pkg::*;
#(
    `include "el2_param.vh"
) (
    // ICCM
    output logic [pt.ICCM_BITS-1:1]     iccm_rw_addr,
    output logic                        iccm_wren,
    output logic                        iccm_rden,
    output logic [2:0]                  iccm_wr_size,
    output logic [77:0]                 iccm_wr_data,
    output logic                        iccm_buf_correct_ecc,
    output logic                        iccm_correction_state,

    input  logic [63:0]                 iccm_rd_data,
    input  logic [77:0]                 iccm_rd_data_ecc,

    // ICCM ECC status
    output logic                 iccm_ecc_single_error,
    output logic                 iccm_ecc_double_error,

    // ICCM TMR
    input  logic [pt.ICCM_BITS-1:1] iccm_rw_addr_veer[3],
    input  logic                    iccm_wren_veer[3],
    input  logic                    iccm_rden_veer[3],
    input  logic [2:0]              iccm_wr_size_veer[3],
    input  logic [77:0]             iccm_wr_data_veer[3],
    input  logic                    iccm_buf_correct_ecc_veer[3],
    input  logic                    iccm_correction_state_veer[3],

    output logic [63:0]             iccm_rd_data_veer[3],
    output logic [77:0]             iccm_rd_data_ecc_veer[3],

    // ICCM ECC status
    input  logic                 iccm_ecc_single_error_veer[3],
    input  logic                 iccm_ecc_double_error_veer[3]
);

//TODO: Change it to use voters
  always_comb begin
    // Propagate response to Cores
    for (int i=0;i < 3; i+=1) begin
      iccm_rd_data_veer[i] = iccm_rd_data;
      iccm_rd_data_ecc_veer[i] = iccm_rd_data_ecc;
    end
    // Get value from Core 0 for the time being
    iccm_rw_addr = iccm_rw_addr_veer[0];
    iccm_wren = iccm_wren_veer[0];
    iccm_rden = iccm_rden_veer[0];
    iccm_wr_size = iccm_wr_size_veer[0];
    iccm_wr_data = iccm_wr_data_veer[0];
    iccm_buf_correct_ecc = iccm_buf_correct_ecc_veer[0];
    iccm_correction_state = iccm_correction_state_veer[0];
    iccm_ecc_single_error = iccm_ecc_single_error_veer[0];
    iccm_ecc_double_error = iccm_ecc_double_error_veer[0];
  end

endmodule
