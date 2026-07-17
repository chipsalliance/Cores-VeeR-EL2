//
// Copyright (c) 2026 Antmicro
// SPDX-License-Identifier: Apache-2.0

module el2_tmr_axi_m_ch_ax # (
  parameter unsigned AddrWidth  = 32,
  parameter unsigned IdWidth    = 1
) (

  input  logic  clk_i,
  input  logic  rst_ni,

  // AR/AW channel input A
  input  logic                     s_axi_a_axvalid_i,
  output logic                     s_axi_a_axready_o,
  input  logic [IdWidth-1:0]       s_axi_a_axid_i,
  input  logic [AddrWidth-1:0]     s_axi_a_axaddr_i,
  input  logic [3:0]               s_axi_a_axregion_i,
  input  logic [7:0]               s_axi_a_axlen_i,
  input  logic [2:0]               s_axi_a_axsize_i,
  input  logic [1:0]               s_axi_a_axburst_i,
  input  logic                     s_axi_a_axlock_i,
  input  logic [3:0]               s_axi_a_axcache_i,
  input  logic [2:0]               s_axi_a_axprot_i,
  input  logic [3:0]               s_axi_a_axqos_i,

  // AR/AW channel input B
  input  logic                     s_axi_b_axvalid_i,
  output logic                     s_axi_b_axready_o,
  input  logic [IdWidth-1:0]       s_axi_b_axid_i,
  input  logic [AddrWidth-1:0]     s_axi_b_axaddr_i,
  input  logic [3:0]               s_axi_b_axregion_i,
  input  logic [7:0]               s_axi_b_axlen_i,
  input  logic [2:0]               s_axi_b_axsize_i,
  input  logic [1:0]               s_axi_b_axburst_i,
  input  logic                     s_axi_b_axlock_i,
  input  logic [3:0]               s_axi_b_axcache_i,
  input  logic [2:0]               s_axi_b_axprot_i,
  input  logic [3:0]               s_axi_b_axqos_i,

  // AR/AW channel input C
  input  logic                     s_axi_c_axvalid_i,
  output logic                     s_axi_c_axready_o,
  input  logic [IdWidth-1:0]       s_axi_c_axid_i,
  input  logic [AddrWidth-1:0]     s_axi_c_axaddr_i,
  input  logic [3:0]               s_axi_c_axregion_i,
  input  logic [7:0]               s_axi_c_axlen_i,
  input  logic [2:0]               s_axi_c_axsize_i,
  input  logic [1:0]               s_axi_c_axburst_i,
  input  logic                     s_axi_c_axlock_i,
  input  logic [3:0]               s_axi_c_axcache_i,
  input  logic [2:0]               s_axi_c_axprot_i,
  input  logic [3:0]               s_axi_c_axqos_i,

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

  // AR/AW channel output
  output logic                     m_axi_axvalid_o,
  input  logic                     m_axi_axready_i,
  output logic [IdWidth-1:0]       m_axi_axid_o,
  output logic [AddrWidth-1:0]     m_axi_axaddr_o,
  output logic [3:0]               m_axi_axregion_o,
  output logic [7:0]               m_axi_axlen_o,
  output logic [2:0]               m_axi_axsize_o,
  output logic [1:0]               m_axi_axburst_o,
  output logic                     m_axi_axlock_o,
  output logic [3:0]               m_axi_axcache_o,
  output logic [2:0]               m_axi_axprot_o,
  output logic [3:0]               m_axi_axqos_o
);
  import el2_mubi_pkg::*;

  el2_mubi_t s_axi_a_enable;
  el2_mubi_t s_axi_b_enable;
  el2_mubi_t s_axi_c_enable;

  el2_mubi_t fault_axvalid  [3];
  el2_mubi_t fault_axid     [3];
  el2_mubi_t fault_axaddr   [3];
  el2_mubi_t fault_axregion [3];
  el2_mubi_t fault_axlen    [3];
  el2_mubi_t fault_axsize   [3];
  el2_mubi_t fault_axburst  [3];
  el2_mubi_t fault_axlock   [3];
  el2_mubi_t fault_axcache  [3];
  el2_mubi_t fault_axprot   [3];
  el2_mubi_t fault_axqos    [3];

  el2_mubi_t fault_d   [3];
  el2_mubi_t fault_q   [3];
  el2_mubi_t fault_clr [3];

  el2_mubi_t crit_axvalid;
  el2_mubi_t crit_axid;
  el2_mubi_t crit_axaddr;
  el2_mubi_t crit_axregion;
  el2_mubi_t crit_axlen;
  el2_mubi_t crit_axsize;
  el2_mubi_t crit_axburst;
  el2_mubi_t crit_axlock;
  el2_mubi_t crit_axcache;
  el2_mubi_t crit_axprot;
  el2_mubi_t crit_axqos;

  el2_mubi_t crit_any;

  logic m_axi_axvalid;

  // ......................................................
  // Voters

  el2_tmr_voter #(.Width(1)) x_voter_axvalid (
    .in_a     (s_axi_a_axvalid_i),
    .in_b     (s_axi_b_axvalid_i),
    .in_c     (s_axi_c_axvalid_i),

    .en_a     (s_axi_a_enable),
    .en_b     (s_axi_b_enable),
    .en_c     (s_axi_c_enable),

    .out      (m_axi_axvalid),

    .fault_a  (fault_axvalid[0]),
    .fault_b  (fault_axvalid[1]),
    .fault_c  (fault_axvalid[2]),

    .critical (crit_axvalid)
  );

  el2_tmr_voter #(.Width($bits(m_axi_axid_o))) x_voter_axid (
    .in_a     (s_axi_a_axid_i),
    .in_b     (s_axi_b_axid_i),
    .in_c     (s_axi_c_axid_i),

    .en_a     (s_axi_a_enable),
    .en_b     (s_axi_b_enable),
    .en_c     (s_axi_c_enable),

    .out      (m_axi_axid_o),

    .fault_a  (fault_axid[0]),
    .fault_b  (fault_axid[1]),
    .fault_c  (fault_axid[2]),

    .critical (crit_axid)
  );

  el2_tmr_voter #(.Width($bits(m_axi_axaddr_o))) x_voter_axaddr (
    .in_a     (s_axi_a_axaddr_i),
    .in_b     (s_axi_b_axaddr_i),
    .in_c     (s_axi_c_axaddr_i),

    .en_a     (s_axi_a_enable),
    .en_b     (s_axi_b_enable),
    .en_c     (s_axi_c_enable),

    .out      (m_axi_axaddr_o),

    .fault_a  (fault_axaddr[0]),
    .fault_b  (fault_axaddr[1]),
    .fault_c  (fault_axaddr[2]),

    .critical (crit_axaddr)
  );

  el2_tmr_voter #(.Width($bits(m_axi_axregion_o))) x_voter_axregion (
    .in_a     (s_axi_a_axregion_i),
    .in_b     (s_axi_b_axregion_i),
    .in_c     (s_axi_c_axregion_i),

    .en_a     (s_axi_a_enable),
    .en_b     (s_axi_b_enable),
    .en_c     (s_axi_c_enable),

    .out      (m_axi_axregion_o),

    .fault_a  (fault_axregion[0]),
    .fault_b  (fault_axregion[1]),
    .fault_c  (fault_axregion[2]),

    .critical (crit_axregion)
  );

  el2_tmr_voter #(.Width($bits(m_axi_axlen_o))) x_voter_axlen (
    .in_a     (s_axi_a_axlen_i),
    .in_b     (s_axi_b_axlen_i),
    .in_c     (s_axi_c_axlen_i),

    .en_a     (s_axi_a_enable),
    .en_b     (s_axi_b_enable),
    .en_c     (s_axi_c_enable),

    .out      (m_axi_axlen_o),

    .fault_a  (fault_axlen[0]),
    .fault_b  (fault_axlen[1]),
    .fault_c  (fault_axlen[2]),

    .critical (crit_axlen)
  );

  el2_tmr_voter #(.Width($bits(m_axi_axsize_o))) x_voter_axsize (
    .in_a     (s_axi_a_axsize_i),
    .in_b     (s_axi_b_axsize_i),
    .in_c     (s_axi_c_axsize_i),

    .en_a     (s_axi_a_enable),
    .en_b     (s_axi_b_enable),
    .en_c     (s_axi_c_enable),

    .out      (m_axi_axsize_o),

    .fault_a  (fault_axsize[0]),
    .fault_b  (fault_axsize[1]),
    .fault_c  (fault_axsize[2]),

    .critical (crit_axsize)
  );

  el2_tmr_voter #(.Width($bits(m_axi_axburst_o))) x_voter_axburst (
    .in_a     (s_axi_a_axburst_i),
    .in_b     (s_axi_b_axburst_i),
    .in_c     (s_axi_c_axburst_i),

    .en_a     (s_axi_a_enable),
    .en_b     (s_axi_b_enable),
    .en_c     (s_axi_c_enable),

    .out      (m_axi_axburst_o),

    .fault_a  (fault_axburst[0]),
    .fault_b  (fault_axburst[1]),
    .fault_c  (fault_axburst[2]),

    .critical (crit_axburst)
  );

  el2_tmr_voter #(.Width($bits(m_axi_axlock_o))) x_voter_axlock (
    .in_a     (s_axi_a_axlock_i),
    .in_b     (s_axi_b_axlock_i),
    .in_c     (s_axi_c_axlock_i),

    .en_a     (s_axi_a_enable),
    .en_b     (s_axi_b_enable),
    .en_c     (s_axi_c_enable),

    .out      (m_axi_axlock_o),

    .fault_a  (fault_axlock[0]),
    .fault_b  (fault_axlock[1]),
    .fault_c  (fault_axlock[2]),

    .critical (crit_axlock)
  );

  el2_tmr_voter #(.Width($bits(m_axi_axprot_o))) x_voter_axprot (
    .in_a     (s_axi_a_axprot_i),
    .in_b     (s_axi_b_axprot_i),
    .in_c     (s_axi_c_axprot_i),

    .en_a     (s_axi_a_enable),
    .en_b     (s_axi_b_enable),
    .en_c     (s_axi_c_enable),

    .out      (m_axi_axprot_o),

    .fault_a  (fault_axprot[0]),
    .fault_b  (fault_axprot[1]),
    .fault_c  (fault_axprot[2]),

    .critical (crit_axprot)
  );

  el2_tmr_voter #(.Width($bits(m_axi_axcache_o))) x_voter_axcache (
    .in_a     (s_axi_a_axcache_i),
    .in_b     (s_axi_b_axcache_i),
    .in_c     (s_axi_c_axcache_i),

    .en_a     (s_axi_a_enable),
    .en_b     (s_axi_b_enable),
    .en_c     (s_axi_c_enable),

    .out      (m_axi_axcache_o),

    .fault_a  (fault_axcache[0]),
    .fault_b  (fault_axcache[1]),
    .fault_c  (fault_axcache[2]),

    .critical (crit_axcache)
  );

  el2_tmr_voter #(.Width($bits(m_axi_axqos_o))) x_voter_axqos (
    .in_a     (s_axi_a_axqos_i),
    .in_b     (s_axi_b_axqos_i),
    .in_c     (s_axi_c_axqos_i),

    .en_a     (s_axi_a_enable),
    .en_b     (s_axi_b_enable),
    .en_c     (s_axi_c_enable),

    .out      (m_axi_axqos_o),

    .fault_a  (fault_axqos[0]),
    .fault_b  (fault_axqos[1]),
    .fault_c  (fault_axqos[2]),

    .critical (crit_axqos)
  );

  // ......................................................
  // valid gate

  // A tree-like structure of multi-bit OR gates
  el2_mubi_t crit_l0;
  el2_mubi_t crit_l1;
  el2_mubi_t crit_l2;
  el2_mubi_t crit_l3;
  el2_mubi_t crit_l4;
  el2_mubi_t crit_l5;

  el2_mubi_t crit_l01;
  el2_mubi_t crit_l23;
  el2_mubi_t crit_l45;

  assign crit_l0  = mubi_or(crit_axvalid, crit_axid);
  assign crit_l1  = mubi_or(crit_axaddr,  crit_axregion);
  assign crit_l2  = mubi_or(crit_axlen,   crit_axsize);
  assign crit_l3  = mubi_or(crit_axburst, crit_axlock);
  assign crit_l4  = mubi_or(crit_axprot,  crit_axcache);
  assign crit_l5  = crit_axqos;

  assign crit_l01 = mubi_or(crit_l0, crit_l1);
  assign crit_l23 = mubi_or(crit_l2, crit_l3);
  assign crit_l45 = mubi_or(crit_l4, crit_l5);

  assign crit_any = mubi_or3(crit_l01, crit_l23, crit_l45);

  // Valid gate
  assign m_axi_axvalid_o = m_axi_axvalid & mubi_check_false(crit_any);

  // ......................................................
  // ready passthrough

  // TODO: Is it worth gating ready with fault ?
  assign s_axi_a_axready_o = m_axi_axready_i;
  assign s_axi_b_axready_o = m_axi_axready_i;
  assign s_axi_c_axready_o = m_axi_axready_i;

  // ......................................................
  // Local and external fault OR gates

  el2_mubi_t fault_local_d[3];

  generate for (genvar i=0; i<3; i=i+1) begin : fault_gates
    el2_mubi_t fault_l0;
    el2_mubi_t fault_l1;
    el2_mubi_t fault_l2;
    el2_mubi_t fault_l3;
    el2_mubi_t fault_l4;
    el2_mubi_t fault_l5;

    el2_mubi_t fault_l01;
    el2_mubi_t fault_l23;
    el2_mubi_t fault_l45;

    // A tree-like structure of multi-bit OR gates
    assign fault_l0  = mubi_or(fault_axvalid[i], fault_axid    [i]);
    assign fault_l1  = mubi_or(fault_axaddr [i], fault_axregion[i]);
    assign fault_l2  = mubi_or(fault_axlen  [i], fault_axsize  [i]);
    assign fault_l3  = mubi_or(fault_axburst[i], fault_axlock  [i]);
    assign fault_l4  = mubi_or(fault_axprot [i], fault_axcache [i]);
    assign fault_l5  = fault_axqos[i];

    assign fault_l01 = mubi_or(fault_l0, fault_l1);
    assign fault_l23 = mubi_or(fault_l2, fault_l3);
    assign fault_l45 = mubi_or(fault_l4, fault_l5);

    assign fault_local_d[i] = mubi_or3(fault_l01, fault_l23, fault_l45);

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
