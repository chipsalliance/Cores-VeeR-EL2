// Copyright 2026 Antmicro <www.antmicro.com>
// //
// // SPDX-License-Identifier: Apache-2.0
//
//
`ifdef RV_TRIPLE_MODULAR_REDUNDANCY_ENABLE
module el2_tmr_pic
  import el2_mubi_pkg::*;
(
    input  logic clk,
    input  logic rst_l,

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
    input  logic [ 3:0] meipt_veer[3],

    // Fault inputs
    input  el2_mubi_pkg::el2_mubi_t pic_fault_d[3],
    // Fault outputs
    output el2_mubi_pkg::el2_mubi_t pic_fault_q[3],
    // Fault clear inputs
    input  el2_mubi_pkg::el2_mubi_t pic_fault_clr[3]
);

  // ......................................................

  el2_mubi_t enable[3];

  el2_mubi_t fault_picm_ctrl[3];
  el2_mubi_t fault_picm_rdaddr[3];
  el2_mubi_t fault_picm_wraddr[3];
  el2_mubi_t fault_picm_wr_data[3];
  el2_mubi_t fault_meicurpl[3];
  el2_mubi_t fault_meipt[3];

  el2_mubi_t crit_picm_ctrl;
  el2_mubi_t crit_picm_rdaddr;
  el2_mubi_t crit_picm_wraddr;
  el2_mubi_t crit_picm_wr_data;
  el2_mubi_t crit_meicurpl;
  el2_mubi_t crit_meipt;

  el2_mubi_t crit_any;

  // ......................................................

  logic [2:0] picm_ctrl_veer[3];
  logic [2:0] picm_ctrl_int;

  for (genvar i=0; i<3; i=i+1) begin
    assign picm_ctrl_veer[i] = {picm_wren_veer[i], picm_rden_veer[i], picm_mken_veer[i]};
  end

  assign picm_wren_int = picm_ctrl_int[2] & mubi_check_false(crit_any);
  assign picm_rden_int = picm_ctrl_int[1] & mubi_check_false(crit_any);
  assign picm_mken_int = picm_ctrl_int[0] & mubi_check_false(crit_any);

  el2_tmr_voter #(.Width($bits(picm_ctrl_int))) x_voter_picm_ctl (
    .in_a     (picm_ctrl_veer[0]),
    .in_b     (picm_ctrl_veer[1]),
    .in_c     (picm_ctrl_veer[2]),

    .en_a     (enable[0]),
    .en_b     (enable[1]),
    .en_c     (enable[2]),

    .out      (picm_ctrl_int),

    .fault_a  (fault_picm_ctrl[0]),
    .fault_b  (fault_picm_ctrl[1]),
    .fault_c  (fault_picm_ctrl[2]),

    .critical (crit_picm_ctrl)
  );

  el2_tmr_voter #(.Width($bits(picm_rdaddr_int))) x_voter_picm_rdaddr (
    .in_a     (picm_rdaddr_veer[0]),
    .in_b     (picm_rdaddr_veer[1]),
    .in_c     (picm_rdaddr_veer[2]),

    .en_a     (enable[0]),
    .en_b     (enable[1]),
    .en_c     (enable[2]),

    .out      (picm_rdaddr_int),

    .fault_a  (fault_picm_rdaddr[0]),
    .fault_b  (fault_picm_rdaddr[1]),
    .fault_c  (fault_picm_rdaddr[2]),

    .critical (crit_picm_rdaddr)
  );

  el2_tmr_voter #(.Width($bits(picm_wraddr_int))) x_voter_picm_wraddr (
    .in_a     (picm_wraddr_veer[0]),
    .in_b     (picm_wraddr_veer[1]),
    .in_c     (picm_wraddr_veer[2]),

    .en_a     (enable[0]),
    .en_b     (enable[1]),
    .en_c     (enable[2]),

    .out      (picm_wraddr_int),

    .fault_a  (fault_picm_wraddr[0]),
    .fault_b  (fault_picm_wraddr[1]),
    .fault_c  (fault_picm_wraddr[2]),

    .critical (crit_picm_wraddr)
  );

  el2_tmr_voter #(.Width($bits(picm_wr_data_int))) x_voter_picm_wr_data (
    .in_a     (picm_wr_data_veer[0]),
    .in_b     (picm_wr_data_veer[1]),
    .in_c     (picm_wr_data_veer[2]),

    .en_a     (enable[0]),
    .en_b     (enable[1]),
    .en_c     (enable[2]),

    .out      (picm_wr_data_int),

    .fault_a  (fault_picm_wr_data[0]),
    .fault_b  (fault_picm_wr_data[1]),
    .fault_c  (fault_picm_wr_data[2]),

    .critical (crit_picm_wr_data)
  );

  el2_tmr_voter #(.Width($bits(meicurpl_int))) x_voter_meicurpl (
    .in_a     (meicurpl_veer[0]),
    .in_b     (meicurpl_veer[1]),
    .in_c     (meicurpl_veer[2]),

    .en_a     (enable[0]),
    .en_b     (enable[1]),
    .en_c     (enable[2]),

    .out      (meicurpl_int),

    .fault_a  (fault_meicurpl[0]),
    .fault_b  (fault_meicurpl[1]),
    .fault_c  (fault_meicurpl[2]),

    .critical (crit_meicurpl)
  );

  el2_tmr_voter #(.Width($bits(meipt_int))) x_voter_meipt (
    .in_a     (meipt_veer[0]),
    .in_b     (meipt_veer[1]),
    .in_c     (meipt_veer[2]),

    .en_a     (enable[0]),
    .en_b     (enable[1]),
    .en_c     (enable[2]),

    .out      (meipt_int),

    .fault_a  (fault_meipt[0]),
    .fault_b  (fault_meipt[1]),
    .fault_c  (fault_meipt[2]),

    .critical (crit_meipt)
  );

  // ......................................................

  // Fault aggregation and registers
  for (genvar i=0; i<3; i=i+1) begin : fault
    el2_mubi_t  fault_l0;
    el2_mubi_t  fault_l1;
    el2_mubi_t  fault_l2;
    el2_mubi_t  fault_any;

    assign fault_l0  = mubi_or(fault_picm_ctrl[i],   fault_picm_rdaddr[i]);
    assign fault_l1  = mubi_or(fault_picm_wraddr[i], fault_picm_wr_data[i]);
    assign fault_l2  = mubi_or3(fault_meicurpl[i],   fault_meipt[i], pic_fault_d[i]);
    assign fault_any = mubi_or3(fault_l0, fault_l1, fault_l2);

    always_ff @(posedge clk or negedge rst_l) begin
      if (!rst_l) begin
        pic_fault_q[i] <= El2MuBiFalse;
      end else begin
        if (mubi_check_true(pic_fault_clr[i])) begin
          pic_fault_q[i] <= El2MuBiFalse;
        end else begin
          pic_fault_q[i] <= mubi_or(pic_fault_q[i], fault_any);
        end
      end
    end

    assign enable[i] = mubi_not(pic_fault_q[i]);

  end

  el2_mubi_t crit_l0;
  el2_mubi_t crit_l1;
  el2_mubi_t crit_l2;

  assign crit_l0  = mubi_or(crit_picm_ctrl,   crit_picm_rdaddr);
  assign crit_l1  = mubi_or(crit_picm_wraddr, crit_picm_wr_data);
  assign crit_l2  = mubi_or(crit_meicurpl,    crit_meipt);
  assign crit_any = mubi_or3(crit_l0, crit_l1, crit_l2);

  // ......................................................

  // Propagate response to Cores
  for (genvar i=0; i < 3; i+=1) begin : resp
    assign picm_rd_data_veer[i] = picm_rd_data_int;
    assign pic_claimid_veer[i]  = pic_claimid_int;
    assign pic_pl_veer[i]       = pic_pl_int;
    assign mexintpend_veer[i]   = mexintpend_int;
    assign mhwakeup_veer[i]     = mhwakeup_int;
  end

endmodule
`endif
