// Copyright 2026 Antmicro <www.antmicro.com>
// //
// // SPDX-License-Identifier: Apache-2.0
//
`ifdef RV_TRIPLE_MODULAR_REDUNDANCY_ENABLE
module el2_tmr_dccm
  import el2_pkg::*;
  import el2_mubi_pkg::*;
#(
    `include "el2_param.vh"
) (
    input logic clk,
    input  logic rst_l,

    // DCCM Memory
    el2_mem_if.veer_dccm dccm_export,

    // DCCM TMR
    el2_mem_if.veer_dccm_sink dccm_export_veer[3],

    // Fault inputs
    input  el2_mubi_pkg::el2_mubi_t dccm_fault_d[3],
    // Fault outputs
    output el2_mubi_pkg::el2_mubi_t dccm_fault_q[3],
    // Fault clear inputs
    input  el2_mubi_pkg::el2_mubi_t dccm_fault_clr[3]
);

  // Create constant with casting to avoid width expansion warnings
  localparam ADDR_BANK_WIDTH = int'(pt.DCCM_BITS) - int'(pt.DCCM_BANK_BITS) - 2;

  // ......................................................

  el2_mubi_t enable[3];

  el2_mubi_t                         fault_dccm_clken[3];
  el2_mubi_t                         fault_dccm_wren_bank[3];
  el2_mubi_t [pt.DCCM_NUM_BANKS-1:0] fault_dccm_addr_bank[3];
  el2_mubi_t [pt.DCCM_NUM_BANKS-1:0] fault_dccm_wr_data_bank[3];
  el2_mubi_t [pt.DCCM_NUM_BANKS-1:0] fault_dccm_wr_ecc_bank[3];

  el2_mubi_t                         crit_dccm_clken;
  el2_mubi_t                         crit_dccm_wren_bank;
  el2_mubi_t [pt.DCCM_NUM_BANKS-1:0] crit_dccm_addr_bank;
  el2_mubi_t [pt.DCCM_NUM_BANKS-1:0] crit_dccm_wr_data_bank;
  el2_mubi_t [pt.DCCM_NUM_BANKS-1:0] crit_dccm_wr_ecc_bank;

  el2_mubi_t crit_any;

  // ......................................................

  logic [pt.DCCM_NUM_BANKS-1:0] dccm_clken;
  logic [pt.DCCM_NUM_BANKS-1:0] dccm_wren_bank;

  el2_tmr_voter #(.Width(pt.DCCM_NUM_BANKS)) u_voter_dccm_clken (
    .in_a     (dccm_export_veer[0].dccm_clken),
    .in_b     (dccm_export_veer[1].dccm_clken),
    .in_c     (dccm_export_veer[2].dccm_clken),

    .en_a     (enable[0]),
    .en_b     (enable[1]),
    .en_c     (enable[2]),

    .out      (dccm_clken),

    .fault_a  (fault_dccm_clken[0]),
    .fault_b  (fault_dccm_clken[1]),
    .fault_c  (fault_dccm_clken[2]),

    .critical (crit_dccm_clken)
  );

  el2_tmr_voter #(.Width(pt.DCCM_NUM_BANKS)) u_voter_dccm_wren_bank (
    .in_a     (dccm_export_veer[0].dccm_wren_bank),
    .in_b     (dccm_export_veer[1].dccm_wren_bank),
    .in_c     (dccm_export_veer[2].dccm_wren_bank),

    .en_a     (enable[0]),
    .en_b     (enable[1]),
    .en_c     (enable[2]),

    .out      (dccm_wren_bank),

    .fault_a  (fault_dccm_wren_bank[0]),
    .fault_b  (fault_dccm_wren_bank[1]),
    .fault_c  (fault_dccm_wren_bank[2]),

    .critical (crit_dccm_wren_bank)
  );

  for (genvar i = 0; i < pt.DCCM_NUM_BANKS; i++) begin : gen_dccm_voters
    el2_tmr_voter #(.Width(ADDR_BANK_WIDTH)) u_voter_dccm_addr_bank (
      .in_a     (dccm_export_veer[0].dccm_addr_bank[i]),
      .in_b     (dccm_export_veer[1].dccm_addr_bank[i]),
      .in_c     (dccm_export_veer[2].dccm_addr_bank[i]),

      .en_a     (enable[0]),
      .en_b     (enable[1]),
      .en_c     (enable[2]),

      .out      (dccm_export.dccm_addr_bank[i]),

      .fault_a  (fault_dccm_addr_bank[0][i]),
      .fault_b  (fault_dccm_addr_bank[1][i]),
      .fault_c  (fault_dccm_addr_bank[2][i]),

      .critical (crit_dccm_addr_bank[i])
    );

    el2_tmr_voter #(.Width(pt.DCCM_DATA_WIDTH)) u_voter_dccm_wr_data_bank (
      .in_a     (dccm_export_veer[0].dccm_wr_data_bank[i]),
      .in_b     (dccm_export_veer[1].dccm_wr_data_bank[i]),
      .in_c     (dccm_export_veer[2].dccm_wr_data_bank[i]),

      .en_a     (enable[0]),
      .en_b     (enable[1]),
      .en_c     (enable[2]),

      .out      (dccm_export.dccm_wr_data_bank[i]),

      .fault_a  (fault_dccm_wr_data_bank[0][i]),
      .fault_b  (fault_dccm_wr_data_bank[1][i]),
      .fault_c  (fault_dccm_wr_data_bank[2][i]),

      .critical (crit_dccm_wr_data_bank[i])
    );

    el2_tmr_voter #(.Width(pt.DCCM_ECC_WIDTH)) u_voter_dccm_wr_ecc_bank (
      .in_a     (dccm_export_veer[0].dccm_wr_ecc_bank[i]),
      .in_b     (dccm_export_veer[1].dccm_wr_ecc_bank[i]),
      .in_c     (dccm_export_veer[2].dccm_wr_ecc_bank[i]),

      .en_a     (enable[0]),
      .en_b     (enable[1]),
      .en_c     (enable[2]),

      .out      (dccm_export.dccm_wr_ecc_bank[i]),

      .fault_a  (fault_dccm_wr_ecc_bank[0][i]),
      .fault_b  (fault_dccm_wr_ecc_bank[1][i]),
      .fault_c  (fault_dccm_wr_ecc_bank[2][i]),

      .critical (crit_dccm_wr_ecc_bank[i])
    );
  end

  el2_mubi_t fault_dccm_addr_bank_aggr[3];
  el2_mubi_t fault_dccm_wr_data_bank_aggr[3];
  el2_mubi_t fault_dccm_wr_ecc_bank_aggr[3];

  el2_mubi_t crit_dccm_addr_bank_aggr;
  el2_mubi_t crit_dccm_wr_data_bank_aggr;
  el2_mubi_t crit_dccm_wr_ecc_bank_aggr;

  always_comb begin
    for (int i = 0; i < 3; i++) begin : gen_veer_dccm_faults
      fault_dccm_addr_bank_aggr[i]    = fault_dccm_addr_bank[i][0];
      fault_dccm_wr_data_bank_aggr[i] = fault_dccm_wr_data_bank[i][0];
      fault_dccm_wr_ecc_bank_aggr[i]  = fault_dccm_wr_ecc_bank[i][0];

      for (int j = 1; j < pt.DCCM_NUM_BANKS; j++) begin : gen_aggr_dccm_faults
        fault_dccm_addr_bank_aggr[i]    = mubi_or(fault_dccm_addr_bank_aggr[i],    fault_dccm_addr_bank[i][j]);
        fault_dccm_wr_data_bank_aggr[i] = mubi_or(fault_dccm_wr_data_bank_aggr[i], fault_dccm_wr_data_bank[i][j]);
        fault_dccm_wr_ecc_bank_aggr[i]  = mubi_or(fault_dccm_wr_ecc_bank_aggr[i],  fault_dccm_wr_ecc_bank[i][j]);
      end
    end
  end

  always_comb begin
    crit_dccm_addr_bank_aggr    = crit_dccm_addr_bank[0];
    crit_dccm_wr_data_bank_aggr = crit_dccm_wr_data_bank[0];
    crit_dccm_wr_ecc_bank_aggr  = crit_dccm_wr_ecc_bank[0];

    for (int i = 1; i < pt.DCCM_NUM_BANKS; i++) begin : gen_aggr_dccm_crits
      crit_dccm_addr_bank_aggr    = mubi_or(crit_dccm_addr_bank_aggr,    crit_dccm_addr_bank[i]);
      crit_dccm_wr_data_bank_aggr = mubi_or(crit_dccm_wr_data_bank_aggr, crit_dccm_wr_data_bank[i]);
      crit_dccm_wr_ecc_bank_aggr  = mubi_or(crit_dccm_wr_ecc_bank_aggr,  crit_dccm_wr_ecc_bank[i]);
    end
  end

  // ......................................................

  // Gate control signals with critical errors
  always_comb begin
    dccm_export.dccm_clken     = dccm_clken     & {pt.DCCM_NUM_BANKS{mubi_check_false(crit_any)}};
    dccm_export.dccm_wren_bank = dccm_wren_bank & {pt.DCCM_NUM_BANKS{mubi_check_false(crit_any)}};
  end

  // ......................................................

  // Fault aggregation and registers
  for (genvar i = 0; i < 3; i++) begin : gen_dccm_faults
    el2_mubi_t  fault_l0;
    el2_mubi_t  fault_l1;
    el2_mubi_t  fault_any;

    assign fault_l0 = mubi_or(fault_dccm_clken[i], fault_dccm_wren_bank[i]);
    assign fault_l1 = mubi_or3(fault_dccm_addr_bank_aggr[i], fault_dccm_wr_data_bank_aggr[i], fault_dccm_wr_ecc_bank_aggr[i]);

    assign fault_any  = mubi_or3(fault_l0,  fault_l1, dccm_fault_d[i]);

    always_ff @(posedge clk or negedge rst_l) begin
      if (!rst_l) begin
        dccm_fault_q[i] <= El2MuBiFalse;
      end else begin
        if (mubi_check_true(dccm_fault_clr[i])) begin
          dccm_fault_q[i] <= El2MuBiFalse;
        end else begin
          dccm_fault_q[i] <= mubi_or(dccm_fault_q[i], fault_any);
        end
      end
    end

    assign enable[i] = mubi_not(dccm_fault_q[i]);
  end

  // ......................................................

  // Critical fault aggregation
  el2_mubi_t  crit_l0;
  el2_mubi_t  crit_l1;

  assign crit_l0 = mubi_or(crit_dccm_clken, crit_dccm_wren_bank);
  assign crit_l1 = mubi_or3(crit_dccm_addr_bank_aggr, crit_dccm_wr_data_bank_aggr, crit_dccm_wr_ecc_bank_aggr);

  assign crit_any  = mubi_or(crit_l0,  crit_l1);

  // ......................................................

  // Propagate response to cores
  for (genvar i=0; i<3; i=i+1) begin
    always_comb begin
      dccm_export_veer[i].dccm_bank_dout = dccm_export.dccm_bank_dout;
      dccm_export_veer[i].dccm_bank_ecc = dccm_export.dccm_bank_ecc;
    end
  end

endmodule
`endif
