//
// Copyright (c) 2026 Antmicro
// SPDX-License-Identifier: Apache-2.0

module el2_tmr_axi_ch_w # (
  parameter unsigned DataWidth  = 64
) (

  input  logic  clk_i,
  input  logic  rst_ni,

  // W channel input A
  input  logic                     s_axi_a_wvalid_i,
  output logic                     s_axi_a_wready_o,
  input  logic [DataWidth-1:0]     s_axi_a_wdata_i,
  input  logic [DataWidth/8-1:0]   s_axi_a_wstrb_i,
  input  logic                     s_axi_a_wlast_i,

  // W channel input B
  input  logic                     s_axi_b_wvalid_i,
  output logic                     s_axi_b_wready_o,
  input  logic [DataWidth-1:0]     s_axi_b_wdata_i,
  input  logic [DataWidth/8-1:0]   s_axi_b_wstrb_i,
  input  logic                     s_axi_b_wlast_i,

  // W channel input C
  input  logic                     s_axi_c_wvalid_i,
  output logic                     s_axi_c_wready_o,
  input  logic [DataWidth-1:0]     s_axi_c_wdata_i,
  input  logic [DataWidth/8-1:0]   s_axi_c_wstrb_i,
  input  logic                     s_axi_c_wlast_i,

  // Channel fault output
  output el2_mubi_pkg::el2_mubi_t  s_axi_a_fault_o,
  output el2_mubi_pkg::el2_mubi_t  s_axi_b_fault_o,
  output el2_mubi_pkg::el2_mubi_t  s_axi_c_fault_o,

  // External fault input
  input  el2_mubi_pkg::el2_mubi_t  s_axi_a_fault_i,
  input  el2_mubi_pkg::el2_mubi_t  s_axi_b_fault_i,
  input  el2_mubi_pkg::el2_mubi_t  s_axi_c_fault_i,

  // Fault clear
  input  el2_mubi_pkg::el2_mubi_t  s_axi_a_fault_clr_i,
  input  el2_mubi_pkg::el2_mubi_t  s_axi_b_fault_clr_i,
  input  el2_mubi_pkg::el2_mubi_t  s_axi_c_fault_clr_i,

  // W channel output
  output logic                     m_axi_wvalid_o,
  input  logic                     m_axi_wready_i,
  output logic [DataWidth-1:0]     m_axi_wdata_o,
  output logic [DataWidth/8-1:0]   m_axi_wstrb_o,
  output logic                     m_axi_wlast_o
);
  import el2_mubi_pkg::*;

  el2_mubi_t s_axi_a_enable;
  el2_mubi_t s_axi_b_enable;
  el2_mubi_t s_axi_c_enable;

  el2_mubi_t fault_wvalid [3];
  el2_mubi_t fault_wdata  [3];
  el2_mubi_t fault_wstrb  [3];
  el2_mubi_t fault_wlast  [3];

  el2_mubi_t fault_d   [3];
  el2_mubi_t fault_q   [3];
  el2_mubi_t fault_clr [3];

  el2_mubi_t crit_wvalid;
  el2_mubi_t crit_wdata;
  el2_mubi_t crit_wstrb;
  el2_mubi_t crit_wlast;

  el2_mubi_t crit_any;

  logic m_axi_wvalid;

  // ......................................................
  // Voters

  el2_tmr_voter #(.Width(1)) x_voter_wvalid (
    .in_a     (s_axi_a_wvalid_i),
    .in_b     (s_axi_b_wvalid_i),
    .in_c     (s_axi_c_wvalid_i),

    .en_a     (s_axi_a_enable),
    .en_b     (s_axi_b_enable),
    .en_c     (s_axi_c_enable),

    .out      (m_axi_wvalid),

    .fault_a  (fault_wvalid[0]),
    .fault_b  (fault_wvalid[1]),
    .fault_c  (fault_wvalid[2]),

    .critical (crit_wvalid)
  );

  el2_tmr_voter #(.Width($bits(m_axi_wdata_o))) x_voter_wdata (
    .in_a     (s_axi_a_wdata_i),
    .in_b     (s_axi_b_wdata_i),
    .in_c     (s_axi_c_wdata_i),

    .en_a     (s_axi_a_enable),
    .en_b     (s_axi_b_enable),
    .en_c     (s_axi_c_enable),

    .out      (m_axi_wdata_o),

    .fault_a  (fault_wdata[0]),
    .fault_b  (fault_wdata[1]),
    .fault_c  (fault_wdata[2]),

    .critical (crit_wdata)
  );

  el2_tmr_voter #(.Width($bits(m_axi_wstrb_o))) x_voter_wstrb (
    .in_a     (s_axi_a_wstrb_i),
    .in_b     (s_axi_b_wstrb_i),
    .in_c     (s_axi_c_wstrb_i),

    .en_a     (s_axi_a_enable),
    .en_b     (s_axi_b_enable),
    .en_c     (s_axi_c_enable),

    .out      (m_axi_wstrb_o),

    .fault_a  (fault_wstrb[0]),
    .fault_b  (fault_wstrb[1]),
    .fault_c  (fault_wstrb[2]),

    .critical (crit_wstrb)
  );

  el2_tmr_voter #(.Width($bits(m_axi_wlast_o))) x_voter_wlast (
    .in_a     (s_axi_a_wlast_i),
    .in_b     (s_axi_b_wlast_i),
    .in_c     (s_axi_c_wlast_i),

    .en_a     (s_axi_a_enable),
    .en_b     (s_axi_b_enable),
    .en_c     (s_axi_c_enable),

    .out      (m_axi_wlast_o),

    .fault_a  (fault_wlast[0]),
    .fault_b  (fault_wlast[1]),
    .fault_c  (fault_wlast[2]),

    .critical (crit_wlast)
  );

  // ......................................................
  // valid gate

  // A tree-like structure of multi-bit OR gates
  el2_mubi_t crit_l0;
  el2_mubi_t crit_l1;

  assign crit_l0  = mubi_or(crit_wvalid, crit_wdata);
  assign crit_l1  = mubi_or(crit_wstrb,  crit_wlast);

  assign crit_any = mubi_or(crit_l0, crit_l1);

  // Valid gate
  assign m_axi_wvalid_o = m_axi_wvalid & mubi_check_false(crit_any);

  // ......................................................
  // ready passthrough

  // TODO: Is it worth gating ready with fault ?
  assign s_axi_a_wready_o = m_axi_wready_i;
  assign s_axi_b_wready_o = m_axi_wready_i;
  assign s_axi_c_wready_o = m_axi_wready_i;

  // ......................................................
  // Local and external fault OR gates

  el2_mubi_t fault_local_d[3];

  generate for (genvar i=0; i<3; i=i+1) begin : fault_gates
    el2_mubi_t fault_l0;
    el2_mubi_t fault_l1;

    // A tree-like structure of multi-bit OR gates
    assign fault_l0  = mubi_or(fault_wvalid[i], fault_wdata[i]);
    assign fault_l1  = mubi_or(fault_wstrb [i], fault_wlast[i]);

    assign fault_local_d[i] = mubi_or(fault_l0, fault_l1);

  end endgenerate

  // Final fault state
  assign fault_d[0] = mubi_or(s_axi_a_fault_i, fault_local_d[0]);
  assign fault_d[1] = mubi_or(s_axi_b_fault_i, fault_local_d[1]);
  assign fault_d[2] = mubi_or(s_axi_c_fault_i, fault_local_d[2]);

  // ......................................................
  // Fault state register

  assign fault_clr[0] = s_axi_a_fault_clr_i;
  assign fault_clr[1] = s_axi_b_fault_clr_i;
  assign fault_clr[2] = s_axi_c_fault_clr_i;

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
  assign s_axi_a_fault_o = fault_q[0];
  assign s_axi_b_fault_o = fault_q[1];
  assign s_axi_c_fault_o = fault_q[2];

  // Voter input enable
  assign s_axi_a_enable = mubi_not(fault_q[0]);
  assign s_axi_b_enable = mubi_not(fault_q[1]);
  assign s_axi_c_enable = mubi_not(fault_q[2]);

endmodule
