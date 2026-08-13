// Copyright 2026 Antmicro <www.antmicro.com>
// //
// // SPDX-License-Identifier: Apache-2.0
//
//
`ifdef RV_TRIPLE_MODULAR_REDUNDANCY_ENABLE
module el2_tmr_ic
  import el2_pkg::*;
  import el2_mubi_pkg::*;
  import el2_lockstep_pkg::*;
#(
    `include "el2_param.vh"
) (
   input logic clk,
   input logic rst_l,

    // I-Cache Memory
    el2_mem_if.veer_icache_src icache_export,

    // I-Cache TMR
    el2_mem_if.veer_icache_sink icache_export_veer[3],

    // Fault inputs
    input  el2_mubi_pkg::el2_mubi_t ic_fault_d[3],
    // Fault outputs
    output el2_mubi_pkg::el2_mubi_t ic_fault_q[3],
    // Fault clear inputs
    input  el2_mubi_pkg::el2_mubi_t ic_fault_clr[3]
);

  // Create constants with casting to avoid width expansion warnings
  localparam RW_ADDR_BANK_WIDTH = int'(pt.ICACHE_INDEX_HI) - int'(pt.ICACHE_DATA_INDEX_LO) + 1;
  localparam RW_ADDR_WIDTH = int'(pt.ICACHE_INDEX_HI) - int'(pt.ICACHE_TAG_INDEX_LO) + 1;

  el2_mem_if mem_if_int();

  el2_mubi_t enable[3];

  el2_mubi_t [pt.ICACHE_BANKS_WAY-1:0] fault_ic_b_sb_wren[3];
  el2_mubi_t [pt.ICACHE_BANKS_WAY-1:0] fault_ic_b_sb_bit_en_vec[3];
  el2_mubi_t [pt.ICACHE_BANKS_WAY-1:0] fault_ic_sb_wr_data[3];
  el2_mubi_t [pt.ICACHE_BANKS_WAY-1:0] fault_ic_rw_addr_bank_q[3];
  el2_mubi_t                           fault_ic_bank_way_clken_final[3];
  el2_mubi_t [pt.ICACHE_NUM_WAYS-1:0]  fault_ic_bank_way_clken_final_up[3];
  el2_mubi_t                           fault_ic_tag_clken_final[3];
  el2_mubi_t                           fault_ic_tag_wren_q[3];
  el2_mubi_t                           fault_ic_tag_wren_biten_vec[3];
  el2_mubi_t                           fault_ic_tag_wr_data[3];
  el2_mubi_t                           fault_ic_rw_addr_q[3];
  el2_mubi_t                           fault_ic_ctl_bundle[3];

  el2_mubi_t [pt.ICACHE_BANKS_WAY-1:0] crit_ic_b_sb_wren;
  el2_mubi_t [pt.ICACHE_BANKS_WAY-1:0] crit_ic_b_sb_bit_en_vec;
  el2_mubi_t [pt.ICACHE_BANKS_WAY-1:0] crit_ic_sb_wr_data;
  el2_mubi_t [pt.ICACHE_BANKS_WAY-1:0] crit_ic_rw_addr_bank_q;
  el2_mubi_t                           crit_ic_bank_way_clken_final;
  el2_mubi_t [pt.ICACHE_NUM_WAYS-1:0]  crit_ic_bank_way_clken_final_up;
  el2_mubi_t                           crit_ic_tag_clken_final;
  el2_mubi_t                           crit_ic_tag_wren_q;
  el2_mubi_t                           crit_ic_tag_wren_biten_vec;
  el2_mubi_t                           crit_ic_tag_wr_data;
  el2_mubi_t                           crit_ic_rw_addr_q;
  el2_mubi_t                           crit_ic_ctl_bundle;

  el2_mubi_t crit_any;

  // ......................................................

  // I-Cache Data
  el2_mubi_t fault_ic_b_sb_wren_aggr[3];
  el2_mubi_t fault_ic_b_sb_bit_en_vec_aggr[3];
  el2_mubi_t fault_ic_sb_wr_data_aggr[3];
  el2_mubi_t fault_ic_rw_addr_bank_q_aggr[3];

  el2_mubi_t crit_ic_b_sb_wren_aggr;
  el2_mubi_t crit_ic_b_sb_bit_en_vec_aggr;
  el2_mubi_t crit_ic_sb_wr_data_aggr;
  el2_mubi_t crit_ic_rw_addr_bank_q_aggr;

  for (genvar i = 0; i < pt.ICACHE_BANKS_WAY; i++) begin : gen_ic_data_voters_0
    el2_tmr_voter #(.Width(pt.ICACHE_NUM_WAYS)) u_voter_ic_b_sb_wren (
      .in_a     (icache_export_veer[0].ic_b_sb_wren[i]),
      .in_b     (icache_export_veer[1].ic_b_sb_wren[i]),
      .in_c     (icache_export_veer[2].ic_b_sb_wren[i]),

      .en_a     (enable[0]),
      .en_b     (enable[1]),
      .en_c     (enable[2]),

      .out      (mem_if_int.ic_b_sb_wren[i]),

      .fault_a  (fault_ic_b_sb_wren[0][i]),
      .fault_b  (fault_ic_b_sb_wren[1][i]),
      .fault_c  (fault_ic_b_sb_wren[2][i]),

      .critical (crit_ic_b_sb_wren[i])
    );

    el2_tmr_voter #(.Width(71*pt.ICACHE_NUM_WAYS)) u_voter_ic_b_sb_bit_en_vec (
      .in_a     (icache_export_veer[0].ic_b_sb_bit_en_vec[i]),
      .in_b     (icache_export_veer[1].ic_b_sb_bit_en_vec[i]),
      .in_c     (icache_export_veer[2].ic_b_sb_bit_en_vec[i]),

      .en_a     (enable[0]),
      .en_b     (enable[1]),
      .en_c     (enable[2]),

      .out      (mem_if_int.ic_b_sb_bit_en_vec[i]),

      .fault_a  (fault_ic_b_sb_bit_en_vec[0][i]),
      .fault_b  (fault_ic_b_sb_bit_en_vec[1][i]),
      .fault_c  (fault_ic_b_sb_bit_en_vec[2][i]),

      .critical (crit_ic_b_sb_bit_en_vec[i])
    );

    el2_tmr_voter #(.Width(71)) u_voter_ic_sb_wr_data (
      .in_a     (icache_export_veer[0].ic_sb_wr_data[i]),
      .in_b     (icache_export_veer[1].ic_sb_wr_data[i]),
      .in_c     (icache_export_veer[2].ic_sb_wr_data[i]),

      .en_a     (enable[0]),
      .en_b     (enable[1]),
      .en_c     (enable[2]),

      .out      (icache_export.ic_sb_wr_data[i]),

      .fault_a  (fault_ic_sb_wr_data[0][i]),
      .fault_b  (fault_ic_sb_wr_data[1][i]),
      .fault_c  (fault_ic_sb_wr_data[2][i]),

      .critical (crit_ic_sb_wr_data[i])
    );

    el2_tmr_voter #(.Width(RW_ADDR_BANK_WIDTH)) u_voter_ic_rw_addr_bank_q (
      .in_a     (icache_export_veer[0].ic_rw_addr_bank_q[i]),
      .in_b     (icache_export_veer[1].ic_rw_addr_bank_q[i]),
      .in_c     (icache_export_veer[2].ic_rw_addr_bank_q[i]),

      .en_a     (enable[0]),
      .en_b     (enable[1]),
      .en_c     (enable[2]),

      .out      (icache_export.ic_rw_addr_bank_q[i]),

      .fault_a  (fault_ic_rw_addr_bank_q[0][i]),
      .fault_b  (fault_ic_rw_addr_bank_q[1][i]),
      .fault_c  (fault_ic_rw_addr_bank_q[2][i]),

      .critical (crit_ic_rw_addr_bank_q[i])
    );
  end : gen_ic_data_voters_0

  always_comb begin
    for (int i = 0; i < 3; i++) begin : gen_veer_data_faults
      fault_ic_b_sb_wren_aggr[i]       = fault_ic_b_sb_wren[i][0];
      fault_ic_b_sb_bit_en_vec_aggr[i] = fault_ic_b_sb_bit_en_vec[i][0];
      fault_ic_sb_wr_data_aggr[i]      = fault_ic_sb_wr_data[i][0];
      fault_ic_rw_addr_bank_q_aggr[i]  = fault_ic_rw_addr_bank_q[i][0];

      for (int j = 1; j < pt.ICACHE_BANKS_WAY; j++) begin : gen_aggr_data_faults
        fault_ic_b_sb_wren_aggr[i]       = mubi_or(fault_ic_b_sb_wren_aggr[i],       fault_ic_b_sb_wren[i][j]);
        fault_ic_b_sb_bit_en_vec_aggr[i] = mubi_or(fault_ic_b_sb_bit_en_vec_aggr[i], fault_ic_b_sb_bit_en_vec[i][j]);
        fault_ic_sb_wr_data_aggr[i]      = mubi_or(fault_ic_sb_wr_data_aggr[i],      fault_ic_sb_wr_data[i][j]);
        fault_ic_rw_addr_bank_q_aggr[i]  = mubi_or(fault_ic_rw_addr_bank_q_aggr[i],  fault_ic_rw_addr_bank_q[i][j]);
      end
    end
  end

  always_comb begin
    crit_ic_b_sb_wren_aggr        = crit_ic_b_sb_wren[0];
    crit_ic_b_sb_bit_en_vec_aggr  = crit_ic_b_sb_bit_en_vec[0];
    crit_ic_sb_wr_data_aggr       = crit_ic_sb_wr_data[0];
    crit_ic_rw_addr_bank_q_aggr   = crit_ic_rw_addr_bank_q[0];

    for (int i = 1; i < pt.ICACHE_BANKS_WAY; i++) begin : gen_aggr_data_crits
      crit_ic_b_sb_wren_aggr        = mubi_or(crit_ic_b_sb_wren_aggr,        crit_ic_b_sb_wren[i]);
      crit_ic_b_sb_bit_en_vec_aggr  = mubi_or(crit_ic_b_sb_bit_en_vec_aggr,  crit_ic_b_sb_bit_en_vec[i]);
      crit_ic_sb_wr_data_aggr       = mubi_or(crit_ic_sb_wr_data_aggr,       crit_ic_sb_wr_data[i]);
      crit_ic_rw_addr_bank_q_aggr   = mubi_or(crit_ic_rw_addr_bank_q_aggr,   crit_ic_rw_addr_bank_q[i]);
    end
  end

  for (genvar i=0; i < pt.ICACHE_NUM_WAYS; i+=1) begin : gen_ic_data_voters_1
    el2_tmr_voter #(.Width(pt.ICACHE_BANKS_WAY)) u_voter_ic_bank_way_clken_final_up (
      .in_a     (icache_export_veer[0].ic_bank_way_clken_final_up[i]),
      .in_b     (icache_export_veer[1].ic_bank_way_clken_final_up[i]),
      .in_c     (icache_export_veer[2].ic_bank_way_clken_final_up[i]),

      .en_a     (enable[0]),
      .en_b     (enable[1]),
      .en_c     (enable[2]),

      .out      (icache_export.ic_bank_way_clken_final_up[i]),

      .fault_a  (fault_ic_bank_way_clken_final_up[0][i]),
      .fault_b  (fault_ic_bank_way_clken_final_up[1][i]),
      .fault_c  (fault_ic_bank_way_clken_final_up[2][i]),

      .critical (crit_ic_bank_way_clken_final_up[i])
    );
  end : gen_ic_data_voters_1

  el2_tmr_voter #(.Width(pt.ICACHE_BANKS_WAY)) u_voter_ic_bank_way_clken_final (
    .in_a     (icache_export_veer[0].ic_bank_way_clken_final),
    .in_b     (icache_export_veer[1].ic_bank_way_clken_final),
    .in_c     (icache_export_veer[2].ic_bank_way_clken_final),

    .en_a     (enable[0]),
    .en_b     (enable[1]),
    .en_c     (enable[2]),

    .out      (icache_export.ic_bank_way_clken_final),

    .fault_a  (fault_ic_bank_way_clken_final[0]),
    .fault_b  (fault_ic_bank_way_clken_final[1]),
    .fault_c  (fault_ic_bank_way_clken_final[2]),

    .critical (crit_ic_bank_way_clken_final)
  );

  // ......................................................

  // I-Cache Tag
  el2_tmr_voter #(.Width(pt.ICACHE_NUM_WAYS)) u_voter_ic_tag_clken_final (
    .in_a     (icache_export_veer[0].ic_tag_clken_final),
    .in_b     (icache_export_veer[1].ic_tag_clken_final),
    .in_c     (icache_export_veer[2].ic_tag_clken_final),

    .en_a     (enable[0]),
    .en_b     (enable[1]),
    .en_c     (enable[2]),

    .out      (icache_export.ic_tag_clken_final),

    .fault_a  (fault_ic_tag_clken_final[0]),
    .fault_b  (fault_ic_tag_clken_final[1]),
    .fault_c  (fault_ic_tag_clken_final[2]),

    .critical (crit_ic_tag_clken_final)
  );

  el2_tmr_voter #(.Width(pt.ICACHE_NUM_WAYS)) u_voter_ic_tag_wren_q (
    .in_a     (icache_export_veer[0].ic_tag_wren_q),
    .in_b     (icache_export_veer[1].ic_tag_wren_q),
    .in_c     (icache_export_veer[2].ic_tag_wren_q),

    .en_a     (enable[0]),
    .en_b     (enable[1]),
    .en_c     (enable[2]),

    .out      (mem_if_int.ic_tag_wren_q),

    .fault_a  (fault_ic_tag_wren_q[0]),
    .fault_b  (fault_ic_tag_wren_q[1]),
    .fault_c  (fault_ic_tag_wren_q[2]),

    .critical (crit_ic_tag_wren_q)
  );

  el2_tmr_voter #(.Width(26*pt.ICACHE_NUM_WAYS)) u_voter_ic_tag_wren_biten_vec (
    .in_a     (icache_export_veer[0].ic_tag_wren_biten_vec),
    .in_b     (icache_export_veer[1].ic_tag_wren_biten_vec),
    .in_c     (icache_export_veer[2].ic_tag_wren_biten_vec),

    .en_a     (enable[0]),
    .en_b     (enable[1]),
    .en_c     (enable[2]),

    .out      (mem_if_int.ic_tag_wren_biten_vec),

    .fault_a  (fault_ic_tag_wren_biten_vec[0]),
    .fault_b  (fault_ic_tag_wren_biten_vec[1]),
    .fault_c  (fault_ic_tag_wren_biten_vec[2]),

    .critical (crit_ic_tag_wren_biten_vec)
  );

  el2_tmr_voter #(.Width(25)) u_voter_ic_tag_wr_data (
    .in_a     (icache_export_veer[0].ic_tag_wr_data),
    .in_b     (icache_export_veer[1].ic_tag_wr_data),
    .in_c     (icache_export_veer[2].ic_tag_wr_data),

    .en_a     (enable[0]),
    .en_b     (enable[1]),
    .en_c     (enable[2]),

    .out      (icache_export.ic_tag_wr_data),

    .fault_a  (fault_ic_tag_wr_data[0]),
    .fault_b  (fault_ic_tag_wr_data[1]),
    .fault_c  (fault_ic_tag_wr_data[2]),

    .critical (crit_ic_tag_wr_data)
  );

  el2_tmr_voter #(.Width(RW_ADDR_WIDTH)) u_voter_ic_rw_addr_q (
    .in_a     (icache_export_veer[0].ic_rw_addr_q),
    .in_b     (icache_export_veer[1].ic_rw_addr_q),
    .in_c     (icache_export_veer[2].ic_rw_addr_q),

    .en_a     (enable[0]),
    .en_b     (enable[1]),
    .en_c     (enable[2]),

    .out      (icache_export.ic_rw_addr_q),

    .fault_a  (fault_ic_rw_addr_q[0]),
    .fault_b  (fault_ic_rw_addr_q[1]),
    .fault_c  (fault_ic_rw_addr_q[2]),

    .critical (crit_ic_rw_addr_q)
  );

  el2_mubi_t fault_ic_bank_way_clken_final_up_aggr[3];

  always_comb begin
    for (int i = 0; i < 3; i++) begin : gen_veer_tag_faults
      fault_ic_bank_way_clken_final_up_aggr[i] = fault_ic_bank_way_clken_final_up[i][0];

      for (int j = 1; j < pt.ICACHE_NUM_WAYS; j++) begin : gen_aggr_tag_faults
        fault_ic_bank_way_clken_final_up_aggr[i] = mubi_or(fault_ic_bank_way_clken_final_up_aggr[i], fault_ic_bank_way_clken_final_up[i][j]);
      end
    end
  end

  el2_mubi_t crit_ic_bank_way_clken_final_up_aggr;

  always_comb begin
    crit_ic_bank_way_clken_final_up_aggr = crit_ic_bank_way_clken_final_up[0];

    for (int i = 1; i < pt.ICACHE_NUM_WAYS; i++) begin : gen_aggr_tag_crits
      crit_ic_bank_way_clken_final_up_aggr = mubi_or(crit_ic_bank_way_clken_final_up_aggr, crit_ic_bank_way_clken_final_up[i]);
    end
  end

  // ......................................................

  // Gate control signals with critical errors
  always_comb begin
    icache_export.ic_b_sb_wren          = mem_if_int.ic_b_sb_wren          & {pt.ICACHE_NUM_WAYS{mubi_check_false(crit_any)}};
    icache_export.ic_b_sb_bit_en_vec    = mem_if_int.ic_b_sb_bit_en_vec    & {71*pt.ICACHE_NUM_WAYS{mubi_check_false(crit_any)}};
    icache_export.ic_tag_wren_q         = mem_if_int.ic_tag_wren_q         & {71{mubi_check_false(crit_any)}};
    icache_export.ic_tag_wren_biten_vec = mem_if_int.ic_tag_wren_biten_vec & {26*pt.ICACHE_NUM_WAYS{mubi_check_false(crit_any)}};
  end

  // ......................................................

  // Fault aggregation and registers
  for (genvar i = 0; i < 3; i++) begin : gen_ic_fault
    el2_mubi_t  fault_l00, fault_l01, fault_l02, fault_l03, fault_l04, fault_l05;
    el2_mubi_t  fault_l0, fault_l1;
    el2_mubi_t  fault_any;

    assign fault_l00 = mubi_or(fault_ic_b_sb_wren_aggr[i], fault_ic_b_sb_bit_en_vec_aggr[i]);
    assign fault_l01 = mubi_or(fault_ic_sb_wr_data_aggr[i], fault_ic_rw_addr_bank_q_aggr[i]);
    assign fault_l02 = mubi_or(fault_ic_bank_way_clken_final[i], fault_ic_bank_way_clken_final_up_aggr[i]);
    assign fault_l03 = mubi_or(fault_ic_tag_clken_final[i], fault_ic_tag_wren_q[i]);
    assign fault_l04 = mubi_or(fault_ic_tag_wren_biten_vec[i], fault_ic_tag_wr_data[i]);
    assign fault_l05 = mubi_or(fault_ic_rw_addr_q[i], fault_ic_ctl_bundle[i]);

    assign fault_l0  = mubi_or3(fault_l00,  fault_l01, fault_l02);
    assign fault_l1  = mubi_or3(fault_l03,  fault_l04, fault_l05);

    assign fault_any = mubi_or3(fault_l0, fault_l1, ic_fault_d[i]);

    always_ff @(posedge clk or negedge rst_l) begin
      if (!rst_l) begin
        ic_fault_q[i] <= El2MuBiFalse;
      end else begin
        if (mubi_check_true(ic_fault_clr[i])) begin
          ic_fault_q[i] <= El2MuBiFalse;
        end else begin
          ic_fault_q[i] <= mubi_or(ic_fault_q[i], fault_any);
        end
      end
    end

    assign enable[i] = mubi_not(ic_fault_q[i]);
  end : gen_ic_fault

  // ......................................................

  // Critical fault aggregation
  el2_mubi_t  crit_l00, crit_l01, crit_l02, crit_l03, crit_l04, crit_l05;
  el2_mubi_t  crit_l0, crit_l1;

  assign crit_l00 = mubi_or(crit_ic_b_sb_wren_aggr, crit_ic_b_sb_bit_en_vec_aggr);
  assign crit_l01 = mubi_or(crit_ic_sb_wr_data_aggr, crit_ic_rw_addr_bank_q_aggr);
  assign crit_l02 = mubi_or(crit_ic_bank_way_clken_final, crit_ic_bank_way_clken_final_up_aggr);
  assign crit_l03 = mubi_or(crit_ic_tag_clken_final, crit_ic_tag_wren_q);
  assign crit_l04 = mubi_or(crit_ic_tag_wren_biten_vec, crit_ic_tag_wr_data);
  assign crit_l05 = mubi_or(crit_ic_rw_addr_q, crit_ic_ctl_bundle);

  assign crit_l0  = mubi_or3(crit_l00, crit_l01, crit_l02);
  assign crit_l1  = mubi_or3(crit_l03, crit_l04, crit_l05);

  assign crit_any = mubi_or(crit_l0, crit_l1);

  // ......................................................

  // Propagate response to Cores
  for (genvar i = 0; i < 3; i++) begin
    always_comb begin
      // Data
      icache_export_veer[i].wb_packeddout_pre = icache_export.wb_packeddout_pre;
      icache_export_veer[i].wb_dout_pre_up = icache_export.wb_dout_pre_up;
      // Tag
      icache_export_veer[i].ic_tag_data_raw_packed_pre = icache_export.ic_tag_data_raw_packed_pre;
      icache_export_veer[i].ic_tag_data_raw_pre = icache_export.ic_tag_data_raw_pre;
    end
  end

endmodule
`endif
