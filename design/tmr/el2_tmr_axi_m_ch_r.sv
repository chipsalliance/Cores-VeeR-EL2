//
// Copyright (c) 2026 Antmicro
// SPDX-License-Identifier: Apache-2.0

module el2_tmr_axi_m_ch_r # (
  parameter unsigned DataWidth = 64,
  parameter unsigned IdWidth   = 1
) (

  input  logic  clk_i,
  input  logic  rst_ni,

  // R channel output A
  output logic                     a_s_axi_rvalid_o,
  input  logic                     a_s_axi_rready_i,
  output logic [IdWidth-1:0]       a_s_axi_rid_o,
  output logic [DataWidth-1:0]     a_s_axi_rdata_o,
  output logic [1:0]               a_s_axi_rresp_o,
  output logic                     a_s_axi_rlast_o,

  // R channel output B
  output logic                     b_s_axi_rvalid_o,
  input  logic                     b_s_axi_rready_i,
  output logic [IdWidth-1:0]       b_s_axi_rid_o,
  output logic [DataWidth-1:0]     b_s_axi_rdata_o,
  output logic [1:0]               b_s_axi_rresp_o,
  output logic                     b_s_axi_rlast_o,

  // R channel output C
  output logic                     c_s_axi_rvalid_o,
  input  logic                     c_s_axi_rready_i,
  output logic [IdWidth-1:0]       c_s_axi_rid_o,
  output logic [DataWidth-1:0]     c_s_axi_rdata_o,
  output logic [1:0]               c_s_axi_rresp_o,
  output logic                     c_s_axi_rlast_o,

  // Channel fault output
  output el2_mubi_pkg::el2_mubi_t  a_s_axi_fault_o,
  output el2_mubi_pkg::el2_mubi_t  b_s_axi_fault_o,
  output el2_mubi_pkg::el2_mubi_t  c_s_axi_fault_o,

  // External fault input
  input  el2_mubi_pkg::el2_mubi_t  a_s_axi_fault_i,
  input  el2_mubi_pkg::el2_mubi_t  b_s_axi_fault_i,
  input  el2_mubi_pkg::el2_mubi_t  c_s_axi_fault_i,

  // Fault clear
  input  el2_mubi_pkg::el2_mubi_t  a_s_axi_fault_clr_i,
  input  el2_mubi_pkg::el2_mubi_t  b_s_axi_fault_clr_i,
  input  el2_mubi_pkg::el2_mubi_t  c_s_axi_fault_clr_i,

  // AR/AW channel output
  input  logic                     m_axi_rvalid_i,
  output logic                     m_axi_rready_o,
  input  logic [IdWidth-1:0]       m_axi_rid_i,
  input  logic [DataWidth-1:0]     m_axi_rdata_i,
  input  logic [1:0]               m_axi_rresp_i,
  input  logic                     m_axi_rlast_i

);

  // Insert TMR AXI ready module for rready
  el2_tmr_axi_rdy x_ready (
    .clk_i         (clk_i),
    .rst_ni        (rst_ni),

    .ready_a_i     (a_s_axi_rready_i),
    .ready_b_i     (b_s_axi_rready_i),
    .ready_c_i     (c_s_axi_rready_i),

    .fault_a_o     (a_s_axi_fault_o),
    .fault_b_o     (b_s_axi_fault_o),
    .fault_c_o     (c_s_axi_fault_o),

    .fault_a_i     (a_s_axi_fault_i),
    .fault_b_i     (b_s_axi_fault_i),
    .fault_c_i     (c_s_axi_fault_i),

    .fault_clr_a_i (a_s_axi_fault_clr_i),
    .fault_clr_b_i (b_s_axi_fault_clr_i),
    .fault_clr_c_i (c_s_axi_fault_clr_i),

    .ready_o       (m_axi_rready_o)
  );

  // Pass AXI R channel signals through
  always_comb begin
    a_s_axi_rvalid_o = m_axi_rvalid_i;
    a_s_axi_rid_o    = m_axi_rid_i;
    a_s_axi_rdata_o  = m_axi_rdata_i;
    a_s_axi_rresp_o  = m_axi_rresp_i;
    a_s_axi_rlast_o  = m_axi_rlast_i;

    b_s_axi_rvalid_o = m_axi_rvalid_i;
    b_s_axi_rid_o    = m_axi_rid_i;
    b_s_axi_rdata_o  = m_axi_rdata_i;
    b_s_axi_rresp_o  = m_axi_rresp_i;
    b_s_axi_rlast_o  = m_axi_rlast_i;

    c_s_axi_rvalid_o = m_axi_rvalid_i;
    c_s_axi_rid_o    = m_axi_rid_i;
    c_s_axi_rdata_o  = m_axi_rdata_i;
    c_s_axi_rresp_o  = m_axi_rresp_i;
    c_s_axi_rlast_o  = m_axi_rlast_i;
  end

endmodule
