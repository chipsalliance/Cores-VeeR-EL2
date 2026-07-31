//
// Copyright (c) 2026 Antmicro
// SPDX-License-Identifier: Apache-2.0

module el2_tmr_axi_s_ch_b # (
  parameter unsigned IdWidth    = 1
) (

  input  logic  clk_i,
  input  logic  rst_ni,

  // B channel input A
  input  logic                     a_m_axi_bvalid_i,
  output logic                     a_m_axi_bready_o,
  input  logic [1:0]               a_m_axi_bresp_i,
  input  logic [IdWidth-1:0]       a_m_axi_bid_i,

  // B channel input B
  input  logic                     b_m_axi_bvalid_i,
  output logic                     b_m_axi_bready_o,
  input  logic [1:0]               b_m_axi_bresp_i,
  input  logic [IdWidth-1:0]       b_m_axi_bid_i,

  // B channel input C
  input  logic                     c_m_axi_bvalid_i,
  output logic                     c_m_axi_bready_o,
  input  logic [1:0]               c_m_axi_bresp_i,
  input  logic [IdWidth-1:0]       c_m_axi_bid_i,

  // Channel fault output
  output el2_mubi_pkg::el2_mubi_t  a_m_axi_fault_o,
  output el2_mubi_pkg::el2_mubi_t  b_m_axi_fault_o,
  output el2_mubi_pkg::el2_mubi_t  c_m_axi_fault_o,

  // External fault input
  input  el2_mubi_pkg::el2_mubi_t  a_m_axi_fault_i,
  input  el2_mubi_pkg::el2_mubi_t  b_m_axi_fault_i,
  input  el2_mubi_pkg::el2_mubi_t  c_m_axi_fault_i,

  // Fault clear
  input  el2_mubi_pkg::el2_mubi_t  a_m_axi_fault_clr_i,
  input  el2_mubi_pkg::el2_mubi_t  b_m_axi_fault_clr_i,
  input  el2_mubi_pkg::el2_mubi_t  c_m_axi_fault_clr_i,

  // B channel output
  output logic                     s_axi_bvalid_o,
  input  logic                     s_axi_bready_i,
  output logic [1:0]               s_axi_bresp_o,
  output logic [IdWidth-1:0]       s_axi_bid_o
);
  import el2_mubi_pkg::*;

  el2_mubi_t a_m_axi_enable;
  el2_mubi_t b_m_axi_enable;
  el2_mubi_t c_m_axi_enable;

  el2_mubi_t fault_bvalid [3];
  el2_mubi_t fault_bresp  [3];
  el2_mubi_t fault_bid    [3];

  el2_mubi_t fault_d   [3];
  el2_mubi_t fault_q   [3];
  el2_mubi_t fault_clr [3];

  el2_mubi_t crit_bvalid;
  el2_mubi_t crit_bresp;
  el2_mubi_t crit_bid;

  el2_mubi_t crit_any;

  logic s_axi_bvalid;

  // ......................................................
  // Voters

  el2_tmr_voter #(.Width(1)) x_voter_bvalid (
    .in_a     (a_m_axi_bvalid_i),
    .in_b     (b_m_axi_bvalid_i),
    .in_c     (c_m_axi_bvalid_i),

    .en_a     (a_m_axi_enable),
    .en_b     (b_m_axi_enable),
    .en_c     (c_m_axi_enable),

    .out      (s_axi_bvalid),

    .fault_a  (fault_bvalid[0]),
    .fault_b  (fault_bvalid[1]),
    .fault_c  (fault_bvalid[2]),

    .critical (crit_bvalid)
  );

  el2_tmr_voter #(.Width($bits(s_axi_bresp_o))) x_voter_bresp (
    .in_a     (a_m_axi_bresp_i),
    .in_b     (b_m_axi_bresp_i),
    .in_c     (c_m_axi_bresp_i),

    .en_a     (a_m_axi_enable),
    .en_b     (b_m_axi_enable),
    .en_c     (c_m_axi_enable),

    .out      (s_axi_bresp_o),

    .fault_a  (fault_bresp[0]),
    .fault_b  (fault_bresp[1]),
    .fault_c  (fault_bresp[2]),

    .critical (crit_bresp)
  );

  el2_tmr_voter #(.Width($bits(s_axi_bid_o))) x_voter_bid (
    .in_a     (a_m_axi_bid_i),
    .in_b     (b_m_axi_bid_i),
    .in_c     (c_m_axi_bid_i),

    .en_a     (a_m_axi_enable),
    .en_b     (b_m_axi_enable),
    .en_c     (c_m_axi_enable),

    .out      (s_axi_bid_o),

    .fault_a  (fault_bid[0]),
    .fault_b  (fault_bid[1]),
    .fault_c  (fault_bid[2]),

    .critical (crit_bid)
  );

  // ......................................................
  // valid gate

  assign crit_any = mubi_or3(crit_bvalid, crit_bresp, crit_bid);

  // Valid gate
  assign s_axi_bvalid_o = s_axi_bvalid & mubi_check_false(crit_any);

  // ......................................................
  // ready passthrough

  assign a_m_axi_bready_o = s_axi_bready_i;
  assign b_m_axi_bready_o = s_axi_bready_i;
  assign c_m_axi_bready_o = s_axi_bready_i;

  // ......................................................
  // Local and external fault OR gates

  el2_mubi_t fault_local_d[3];

  generate for (genvar i=0; i<3; i=i+1) begin : fault_gates
    assign fault_local_d[i] = mubi_or3(fault_bvalid[i], fault_bresp[i], fault_bid[i]);
  end endgenerate

  // Final fault state
  assign fault_d[0] = mubi_or(a_m_axi_fault_i, fault_local_d[0]);
  assign fault_d[1] = mubi_or(b_m_axi_fault_i, fault_local_d[1]);
  assign fault_d[2] = mubi_or(c_m_axi_fault_i, fault_local_d[2]);

  // ......................................................
  // Fault state register

  assign fault_clr[0] = a_m_axi_fault_clr_i;
  assign fault_clr[1] = b_m_axi_fault_clr_i;
  assign fault_clr[2] = c_m_axi_fault_clr_i;

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
  assign a_m_axi_fault_o = fault_q[0];
  assign b_m_axi_fault_o = fault_q[1];
  assign c_m_axi_fault_o = fault_q[2];

  // Voter input enable
  assign a_m_axi_enable = mubi_not(fault_q[0]);
  assign b_m_axi_enable = mubi_not(fault_q[1]);
  assign c_m_axi_enable = mubi_not(fault_q[2]);

endmodule
