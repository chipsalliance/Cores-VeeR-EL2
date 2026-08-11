// Copyright 2026 Antmicro <www.antmicro.com>
// //
// // SPDX-License-Identifier: Apache-2.0
//
`ifdef RV_TRIPLE_MODULAR_REDUNDANCY_ENABLE
module el2_tmr_iccm
  import el2_pkg::*;
  import el2_mubi_pkg::*;
#(
    `include "el2_param.vh"
) (
    input logic clk,
    input  logic rst_l,

    // ICCM Memory
    el2_mem_if.veer_iccm iccm_export,

    // ICCM TMR
    el2_mem_if.veer_iccm_sink iccm_export_veer[3],

    // Fault inputs
    input  el2_mubi_pkg::el2_mubi_t iccm_fault_d[3],
    // Fault outputs
    output el2_mubi_pkg::el2_mubi_t iccm_fault_q[3],
    // Fault clear inputs
    input  el2_mubi_pkg::el2_mubi_t iccm_fault_clr[3]
);

  // Create constant with casting to avoid width expansion warnings
  localparam ADDR_BANK_WIDTH = int'(pt.ICCM_BITS) - int'(pt.ICCM_BANK_INDEX_LO);

  // ......................................................

  el2_mubi_t enable[3];

  el2_mubi_t                         fault_iccm_clken[3];
  el2_mubi_t                         fault_iccm_wren_bank[3];
  el2_mubi_t [pt.ICCM_NUM_BANKS-1:0] fault_iccm_addr_bank[3];
  el2_mubi_t [pt.ICCM_NUM_BANKS-1:0] fault_iccm_bank_wr_data[3];
  el2_mubi_t [pt.ICCM_NUM_BANKS-1:0] fault_iccm_bank_wr_ecc[3];

  el2_mubi_t                         crit_iccm_clken;
  el2_mubi_t                         crit_iccm_wren_bank;
  el2_mubi_t [pt.ICCM_NUM_BANKS-1:0] crit_iccm_addr_bank;
  el2_mubi_t [pt.ICCM_NUM_BANKS-1:0] crit_iccm_bank_wr_data;
  el2_mubi_t [pt.ICCM_NUM_BANKS-1:0] crit_iccm_bank_wr_ecc;

  el2_mubi_t crit_any;

  // ......................................................

  logic [pt.ICCM_NUM_BANKS-1:0] iccm_clken;
  logic [pt.ICCM_NUM_BANKS-1:0] iccm_wren_bank;

  el2_tmr_voter #(.Width(pt.ICCM_NUM_BANKS)) u_voter_iccm_clken (
    .in_a     (iccm_export_veer[0].iccm_clken),
    .in_b     (iccm_export_veer[1].iccm_clken),
    .in_c     (iccm_export_veer[2].iccm_clken),

    .en_a     (enable[0]),
    .en_b     (enable[1]),
    .en_c     (enable[2]),

    .out      (iccm_clken),

    .fault_a  (fault_iccm_clken[0]),
    .fault_b  (fault_iccm_clken[1]),
    .fault_c  (fault_iccm_clken[2]),

    .critical (crit_iccm_clken)
  );

  el2_tmr_voter #(.Width(pt.ICCM_NUM_BANKS)) u_voter_iccm_wren_bank (
    .in_a     (iccm_export_veer[0].iccm_wren_bank),
    .in_b     (iccm_export_veer[1].iccm_wren_bank),
    .in_c     (iccm_export_veer[2].iccm_wren_bank),

    .en_a     (enable[0]),
    .en_b     (enable[1]),
    .en_c     (enable[2]),

    .out      (iccm_wren_bank),

    .fault_a  (fault_iccm_wren_bank[0]),
    .fault_b  (fault_iccm_wren_bank[1]),
    .fault_c  (fault_iccm_wren_bank[2]),

    .critical (crit_iccm_wren_bank)
  );

  for (genvar i = 0; i < pt.ICCM_NUM_BANKS; i++) begin : gen_iccm_voters
    el2_tmr_voter #(.Width(ADDR_BANK_WIDTH)) u_voter_iccm_addr_bank (
      .in_a     (iccm_export_veer[0].iccm_addr_bank[i]),
      .in_b     (iccm_export_veer[1].iccm_addr_bank[i]),
      .in_c     (iccm_export_veer[2].iccm_addr_bank[i]),

      .en_a     (enable[0]),
      .en_b     (enable[1]),
      .en_c     (enable[2]),

      .out      (iccm_export.iccm_addr_bank[i]),

      .fault_a  (fault_iccm_addr_bank[0][i]),
      .fault_b  (fault_iccm_addr_bank[1][i]),
      .fault_c  (fault_iccm_addr_bank[2][i]),

      .critical (crit_iccm_addr_bank[i])
    );

    el2_tmr_voter #(.Width(32)) u_voter_iccm_bank_wr_data (
      .in_a     (iccm_export_veer[0].iccm_bank_wr_data[i]),
      .in_b     (iccm_export_veer[1].iccm_bank_wr_data[i]),
      .in_c     (iccm_export_veer[2].iccm_bank_wr_data[i]),

      .en_a     (enable[0]),
      .en_b     (enable[1]),
      .en_c     (enable[2]),

      .out      (iccm_export.iccm_bank_wr_data[i]),

      .fault_a  (fault_iccm_bank_wr_data[0][i]),
      .fault_b  (fault_iccm_bank_wr_data[1][i]),
      .fault_c  (fault_iccm_bank_wr_data[2][i]),

      .critical (crit_iccm_bank_wr_data[i])
    );

    el2_tmr_voter #(.Width(pt.ICCM_ECC_WIDTH)) u_voter_iccm_bank_wr_ecc (
      .in_a     (iccm_export_veer[0].iccm_bank_wr_ecc[i]),
      .in_b     (iccm_export_veer[1].iccm_bank_wr_ecc[i]),
      .in_c     (iccm_export_veer[2].iccm_bank_wr_ecc[i]),

      .en_a     (enable[0]),
      .en_b     (enable[1]),
      .en_c     (enable[2]),

      .out      (iccm_export.iccm_bank_wr_ecc[i]),

      .fault_a  (fault_iccm_bank_wr_ecc[0][i]),
      .fault_b  (fault_iccm_bank_wr_ecc[1][i]),
      .fault_c  (fault_iccm_bank_wr_ecc[2][i]),

      .critical (crit_iccm_bank_wr_ecc[i])
    );
  end

  el2_mubi_t fault_iccm_addr_bank_aggr[3];
  el2_mubi_t fault_iccm_bank_wr_data_aggr[3];
  el2_mubi_t fault_iccm_bank_wr_ecc_aggr[3];

  el2_mubi_t crit_iccm_addr_bank_aggr;
  el2_mubi_t crit_iccm_bank_wr_data_aggr;
  el2_mubi_t crit_iccm_bank_wr_ecc_aggr;

  always_comb begin
    for (int i = 0; i < 3; i++) begin : gen_veer_iccm_faults
      fault_iccm_addr_bank_aggr[i]    = fault_iccm_addr_bank[i][0];
      fault_iccm_bank_wr_data_aggr[i] = fault_iccm_bank_wr_data[i][0];
      fault_iccm_bank_wr_ecc_aggr[i]  = fault_iccm_bank_wr_ecc[i][0];

      for (int j = 1; j < pt.ICCM_NUM_BANKS; j++) begin : gen_aggr_iccm_faults
        fault_iccm_addr_bank_aggr[i]    = mubi_or(fault_iccm_addr_bank_aggr[i],    fault_iccm_addr_bank[i][j]);
        fault_iccm_bank_wr_data_aggr[i] = mubi_or(fault_iccm_bank_wr_data_aggr[i], fault_iccm_bank_wr_data[i][j]);
        fault_iccm_bank_wr_ecc_aggr[i]  = mubi_or(fault_iccm_bank_wr_ecc_aggr[i],  fault_iccm_bank_wr_ecc[i][j]);
      end
    end
  end

  always_comb begin
    crit_iccm_addr_bank_aggr    = crit_iccm_addr_bank[0];
    crit_iccm_bank_wr_data_aggr = crit_iccm_bank_wr_data[0];
    crit_iccm_bank_wr_ecc_aggr  = crit_iccm_bank_wr_ecc[0];

    for (int i = 1; i < pt.ICCM_NUM_BANKS; i++) begin : gen_aggr_iccm_crits
      crit_iccm_addr_bank_aggr    = mubi_or(crit_iccm_addr_bank_aggr,    crit_iccm_addr_bank[i]);
      crit_iccm_bank_wr_data_aggr = mubi_or(crit_iccm_bank_wr_data_aggr, crit_iccm_bank_wr_data[i]);
      crit_iccm_bank_wr_ecc_aggr  = mubi_or(crit_iccm_bank_wr_ecc_aggr,  crit_iccm_bank_wr_ecc[i]);
    end
  end

  // ......................................................

  // Gate control signals with critical errors
  always_comb begin
    iccm_export.iccm_clken     = iccm_clken     & {pt.ICCM_NUM_BANKS{mubi_check_false(crit_any)}};
    iccm_export.iccm_wren_bank = iccm_wren_bank & {pt.ICCM_NUM_BANKS{mubi_check_false(crit_any)}};
  end

  // ......................................................

  // Fault aggregation and registers
  for (genvar i=0; i<3; i=i+1) begin : gen_iccm_faults
    el2_mubi_t  fault_l0;
    el2_mubi_t  fault_l1;
    el2_mubi_t  fault_any;

    assign fault_l0 = mubi_or(fault_iccm_clken[i], fault_iccm_wren_bank[i]);
    assign fault_l1 = mubi_or3(fault_iccm_addr_bank_aggr[i], fault_iccm_bank_wr_data_aggr[i], fault_iccm_bank_wr_ecc_aggr[i]);

    assign fault_any  = mubi_or3(fault_l0,  fault_l1, iccm_fault_d[i]);

    always_ff @(posedge clk or negedge rst_l) begin
      if (!rst_l) begin
        iccm_fault_q[i] <= El2MuBiFalse;
      end else begin
        if (mubi_check_true(iccm_fault_clr[i])) begin
          iccm_fault_q[i] <= El2MuBiFalse;
        end else begin
          iccm_fault_q[i] <= mubi_or(iccm_fault_q[i], fault_any);
        end
      end
    end

    assign enable[i] = mubi_not(iccm_fault_q[i]);
  end

  // ......................................................

  // Critical fault aggregation
  el2_mubi_t  crit_l0;
  el2_mubi_t  crit_l1;

  assign crit_l0 = mubi_or(crit_iccm_clken, crit_iccm_wren_bank);
  assign crit_l1 = mubi_or3(crit_iccm_addr_bank_aggr, crit_iccm_bank_wr_data_aggr, crit_iccm_bank_wr_ecc_aggr);

  assign crit_any  = mubi_or(crit_l0,  crit_l1);

  // ......................................................

  // Propagate response to cores
  for (genvar i=0; i<3; i=i+1) begin
    always_comb begin
      iccm_export_veer[i].iccm_bank_dout = iccm_export.iccm_bank_dout;
      iccm_export_veer[i].iccm_bank_ecc = iccm_export.iccm_bank_ecc;
    end
  end

endmodule
`endif
