// Copyright 2026 Antmicro <www.antmicro.com>
// //
// // SPDX-License-Identifier: Apache-2.0
//
//
`ifdef RV_TRIPLE_MODULAR_REDUNDANCY_ENABLE
module el2_tmr_pic
  import el2_pkg::*;
  import el2_mubi_pkg::*;
  import el2_lockstep_pkg::*;
#(
    `include "el2_param.vh"
) (
    // PIC
    input  logic [31:0] picm_rd_data_int,
    input  logic [ 7:0] pic_claimid_int,
    input  logic [ 3:0] pic_pl_int,
    input  logic        mexintpend_int,
    input  logic        mhwakeup_int,

    output logic        picm_wren_int,
    output logic        picm_rden_int,
    output logic        picm_mken_int,
    output logic [31:0] picm_rdaddr_int,
    output logic [31:0] picm_wraddr_int,
    output logic [31:0] picm_wr_data_int,
    output logic [ 3:0] meicurpl_int,
    output logic [ 3:0] meipt_int,

    // PIC TMR
    output logic [31:0] picm_rd_data_veer[3],
    output logic [ 7:0] pic_claimid_veer[3],
    output logic [ 3:0] pic_pl_veer[3],
    output logic        mexintpend_veer[3],
    output logic        mhwakeup_veer[3],

    input  logic        picm_wren_veer[3],
    input  logic        picm_rden_veer[3],
    input  logic        picm_mken_veer[3],
    input  logic [31:0] picm_rdaddr_veer[3],
    input  logic [31:0] picm_wraddr_veer[3],
    input  logic [31:0] picm_wr_data_veer[3],
    input  logic [ 3:0] meicurpl_veer[3],
    input  logic [ 3:0] meipt_veer[3]
);

  //TODO: Change it to use voters

  always_comb begin
    // Propagate response to Cores
    for (int i=0;i < 3; i+=1) begin
      picm_rd_data_veer[i] = picm_rd_data_int;
      pic_claimid_veer[i] = pic_claimid_int;
      pic_pl_veer[i] = pic_pl_int;
      mexintpend_veer[i] = mexintpend_int;
      mhwakeup_veer[i] = mhwakeup_int;
    end
    // Get value from Core 0 for the time being
    picm_wren_int    = picm_wren_veer[0];
    picm_rden_int    = picm_rden_veer[0];
    picm_mken_int    = picm_mken_veer[0];
    picm_rdaddr_int  = picm_rdaddr_veer[0];
    picm_wraddr_int  = picm_wraddr_veer[0];
    picm_wr_data_int = picm_wr_data_veer[0];
    meicurpl_int     = meicurpl_veer[0];
    meipt_int        = meipt_veer[0];
  end

endmodule
`endif
