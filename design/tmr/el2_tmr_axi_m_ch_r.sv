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
  output logic                     s_axi_a_rvalid_o,
  input  logic                     s_axi_a_rready_i,
  output logic [IdWidth-1:0]       s_axi_a_rid_o,
  output logic [DataWidth-1:0]     s_axi_a_rdata_o,
  output logic [1:0]               s_axi_a_rresp_o,
  output logic                     s_axi_a_rlast_o,

  // R channel output B
  output logic                     s_axi_b_rvalid_o,
  input  logic                     s_axi_b_rready_i,
  output logic [IdWidth-1:0]       s_axi_b_rid_o,
  output logic [DataWidth-1:0]     s_axi_b_rdata_o,
  output logic [1:0]               s_axi_b_rresp_o,
  output logic                     s_axi_b_rlast_o,

  // R channel output C
  output logic                     s_axi_c_rvalid_o,
  input  logic                     s_axi_c_rready_i,
  output logic [IdWidth-1:0]       s_axi_c_rid_o,
  output logic [DataWidth-1:0]     s_axi_c_rdata_o,
  output logic [1:0]               s_axi_c_rresp_o,
  output logic                     s_axi_c_rlast_o,

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

    .ready_a_i     (s_axi_a_rready_i),
    .ready_b_i     (s_axi_b_rready_i),
    .ready_c_i     (s_axi_c_rready_i),

    .fault_a_o     (s_axi_a_fault_o),
    .fault_b_o     (s_axi_b_fault_o),
    .fault_c_o     (s_axi_c_fault_o),

    .fault_a_i     (s_axi_a_fault_i),
    .fault_b_i     (s_axi_b_fault_i),
    .fault_c_i     (s_axi_c_fault_i),

    .fault_clr_a_i (s_axi_a_fault_clr_i),
    .fault_clr_b_i (s_axi_b_fault_clr_i),
    .fault_clr_c_i (s_axi_c_fault_clr_i),

    .ready_o       (m_axi_rready_o)
  );

  // Pass AXI R channel signals through
  always_comb begin
    s_axi_a_rvalid_o = m_axi_rvalid_i;
    s_axi_a_rid_o    = m_axi_rid_i;
    s_axi_a_rdata_o  = m_axi_rdata_i;
    s_axi_a_rresp_o  = m_axi_rresp_i;
    s_axi_a_rlast_o  = m_axi_rlast_i;

    s_axi_b_rvalid_o = m_axi_rvalid_i;
    s_axi_b_rid_o    = m_axi_rid_i;
    s_axi_b_rdata_o  = m_axi_rdata_i;
    s_axi_b_rresp_o  = m_axi_rresp_i;
    s_axi_b_rlast_o  = m_axi_rlast_i;

    s_axi_c_rvalid_o = m_axi_rvalid_i;
    s_axi_c_rid_o    = m_axi_rid_i;
    s_axi_c_rdata_o  = m_axi_rdata_i;
    s_axi_c_rresp_o  = m_axi_rresp_i;
    s_axi_c_rlast_o  = m_axi_rlast_i;
  end

endmodule
