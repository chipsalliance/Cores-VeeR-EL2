//
// Copyright (c) 2026 Antmicro
// SPDX-License-Identifier: Apache-2.0

module el2_tmr_axi_s_ch_r # (
  parameter unsigned DataWidth  = 64,
  parameter unsigned IdWidth    = 1
) (

  input  logic  clk_i,
  input  logic  rst_ni,

  // R channel input A
  input  logic                     m_axi_a_rvalid_i,
  output logic                     m_axi_a_rready_o,
  input  logic [IdWidth-1:0]       m_axi_a_rid_i,
  input  logic [DataWidth-1:0]     m_axi_a_rdata_i,
  input  logic [1:0]               m_axi_a_rresp_i,
  input  logic                     m_axi_a_rlast_i,

  // R channel input B
  input  logic                     m_axi_b_rvalid_i,
  output logic                     m_axi_b_rready_o,
  input  logic [IdWidth-1:0]       m_axi_b_rid_i,
  input  logic [DataWidth-1:0]     m_axi_b_rdata_i,
  input  logic [1:0]               m_axi_b_rresp_i,
  input  logic                     m_axi_b_rlast_i,

  // R channel input C
  input  logic                     m_axi_c_rvalid_i,
  output logic                     m_axi_c_rready_o,
  input  logic [IdWidth-1:0]       m_axi_c_rid_i,
  input  logic [DataWidth-1:0]     m_axi_c_rdata_i,
  input  logic [1:0]               m_axi_c_rresp_i,
  input  logic                     m_axi_c_rlast_i,

  // Channel fault output
  output el2_mubi_pkg::el2_mubi_t  m_axi_a_fault_o,
  output el2_mubi_pkg::el2_mubi_t  m_axi_b_fault_o,
  output el2_mubi_pkg::el2_mubi_t  m_axi_c_fault_o,

  // External fault input
  input  el2_mubi_pkg::el2_mubi_t  m_axi_a_fault_i,
  input  el2_mubi_pkg::el2_mubi_t  m_axi_b_fault_i,
  input  el2_mubi_pkg::el2_mubi_t  m_axi_c_fault_i,

  // Fault clear
  input  el2_mubi_pkg::el2_mubi_t  m_axi_a_fault_clr_i,
  input  el2_mubi_pkg::el2_mubi_t  m_axi_b_fault_clr_i,
  input  el2_mubi_pkg::el2_mubi_t  m_axi_c_fault_clr_i,

  // R channel output
  output logic                     s_axi_rvalid_o,
  input  logic                     s_axi_rready_i,
  output logic [IdWidth-1:0]       s_axi_rid_o,
  output logic [DataWidth-1:0]     s_axi_rdata_o,
  output logic [1:0]               s_axi_rresp_o,
  output logic                     s_axi_rlast_o
);
  import el2_mubi_pkg::*;

  el2_mubi_t m_axi_a_enable;
  el2_mubi_t m_axi_b_enable;
  el2_mubi_t m_axi_c_enable;

  el2_mubi_t fault_rvalid [3];
  el2_mubi_t fault_rid    [3];
  el2_mubi_t fault_rdata  [3];
  el2_mubi_t fault_rresp  [3];
  el2_mubi_t fault_rlast  [3];

  el2_mubi_t fault_d   [3];
  el2_mubi_t fault_q   [3];
  el2_mubi_t fault_clr [3];

  el2_mubi_t crit_rvalid;
  el2_mubi_t crit_rid;
  el2_mubi_t crit_rdata;
  el2_mubi_t crit_rresp;
  el2_mubi_t crit_rlast;

  el2_mubi_t crit_any;

  logic s_axi_rvalid;

  // ......................................................
  // Voters

  el2_tmr_voter #(.Width(1)) x_voter_rvalid (
    .in_a     (m_axi_a_rvalid_i),
    .in_b     (m_axi_b_rvalid_i),
    .in_c     (m_axi_c_rvalid_i),

    .en_a     (m_axi_a_enable),
    .en_b     (m_axi_b_enable),
    .en_c     (m_axi_c_enable),

    .out      (s_axi_rvalid),

    .fault_a  (fault_rvalid[0]),
    .fault_b  (fault_rvalid[1]),
    .fault_c  (fault_rvalid[2]),

    .critical (crit_rvalid)
  );

  el2_tmr_voter #(.Width($bits(s_axi_rid_o))) x_voter_rid (
    .in_a     (m_axi_a_rid_i),
    .in_b     (m_axi_b_rid_i),
    .in_c     (m_axi_c_rid_i),

    .en_a     (m_axi_a_enable),
    .en_b     (m_axi_b_enable),
    .en_c     (m_axi_c_enable),

    .out      (s_axi_rid_o),

    .fault_a  (fault_rid[0]),
    .fault_b  (fault_rid[1]),
    .fault_c  (fault_rid[2]),

    .critical (crit_rid)
  );

  el2_tmr_voter #(.Width($bits(s_axi_rdata_o))) x_voter_rdata (
    .in_a     (m_axi_a_rdata_i),
    .in_b     (m_axi_b_rdata_i),
    .in_c     (m_axi_c_rdata_i),

    .en_a     (m_axi_a_enable),
    .en_b     (m_axi_b_enable),
    .en_c     (m_axi_c_enable),

    .out      (s_axi_rdata_o),

    .fault_a  (fault_rdata[0]),
    .fault_b  (fault_rdata[1]),
    .fault_c  (fault_rdata[2]),

    .critical (crit_rdata)
  );

  el2_tmr_voter #(.Width($bits(s_axi_rresp_o))) x_voter_rresp (
    .in_a     (m_axi_a_rresp_i),
    .in_b     (m_axi_b_rresp_i),
    .in_c     (m_axi_c_rresp_i),

    .en_a     (m_axi_a_enable),
    .en_b     (m_axi_b_enable),
    .en_c     (m_axi_c_enable),

    .out      (s_axi_rresp_o),

    .fault_a  (fault_rresp[0]),
    .fault_b  (fault_rresp[1]),
    .fault_c  (fault_rresp[2]),

    .critical (crit_rresp)
  );

  el2_tmr_voter #(.Width($bits(s_axi_rlast_o))) x_voter_rlast (
    .in_a     (m_axi_a_rlast_i),
    .in_b     (m_axi_b_rlast_i),
    .in_c     (m_axi_c_rlast_i),

    .en_a     (m_axi_a_enable),
    .en_b     (m_axi_b_enable),
    .en_c     (m_axi_c_enable),

    .out      (s_axi_rlast_o),

    .fault_a  (fault_rlast[0]),
    .fault_b  (fault_rlast[1]),
    .fault_c  (fault_rlast[2]),

    .critical (crit_rlast)
  );

  // ......................................................
  // valid gate

  // A tree-like structure of multi-bit OR gates
  el2_mubi_t crit_l0;
  el2_mubi_t crit_l1;

  assign crit_l0  = mubi_or(crit_rid,   crit_rdata);
  assign crit_l1  = mubi_or(crit_rresp, crit_rlast);

  assign crit_any = mubi_or3(crit_rvalid, crit_l0, crit_l1);

  // Valid gate
  assign s_axi_rvalid_o = s_axi_rvalid & mubi_check_false(crit_any);

  // ......................................................
  // ready passthrough

  assign m_axi_a_rready_o = s_axi_rready_i;
  assign m_axi_b_rready_o = s_axi_rready_i;
  assign m_axi_c_rready_o = s_axi_rready_i;

  // ......................................................
  // Local and external fault OR gates

  el2_mubi_t fault_local_d[3];

  generate for (genvar i=0; i<3; i=i+1) begin : fault_gates
    el2_mubi_t fault_l0;
    el2_mubi_t fault_l1;

    // A tree-like structure of multi-bit OR gates
    assign fault_l0  = mubi_or(fault_rid  [i], fault_rdata[i]);
    assign fault_l1  = mubi_or(fault_rresp[i], fault_rid  [i]);

    assign fault_local_d[i] = mubi_or3(fault_rvalid[i], fault_l0, fault_l1);
  end endgenerate

  // Final fault state
  assign fault_d[0] = mubi_or(m_axi_a_fault_i, fault_local_d[0]);
  assign fault_d[1] = mubi_or(m_axi_b_fault_i, fault_local_d[1]);
  assign fault_d[2] = mubi_or(m_axi_c_fault_i, fault_local_d[2]);

  // ......................................................
  // Fault state register

  assign fault_clr[0] = m_axi_a_fault_clr_i;
  assign fault_clr[1] = m_axi_b_fault_clr_i;
  assign fault_clr[2] = m_axi_c_fault_clr_i;

  generate for (genvar i=0; i<3; i=i+1) begin : fault_ff
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        fault_q[i] <= El2MuBiFalse;
      end else begin
        if (mubi_check_true(fault_clr[i])) begin
          fault_q[i] <= El2MuBiFalse;
        end else begin
          fault_q[i] <= mubi_or(fault_q[i], fault_d[i]);
        end
      end
    end
  end endgenerate

  // Fault outputs (registered)
  assign m_axi_a_fault_o = fault_q[0];
  assign m_axi_b_fault_o = fault_q[1];
  assign m_axi_c_fault_o = fault_q[2];

  // Voter input enable
  assign m_axi_a_enable = mubi_not(fault_q[0]);
  assign m_axi_b_enable = mubi_not(fault_q[1]);
  assign m_axi_c_enable = mubi_not(fault_q[2]);

endmodule
