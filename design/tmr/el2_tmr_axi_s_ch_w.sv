//
// Copyright (c) 2026 Antmicro
// SPDX-License-Identifier: Apache-2.0

module el2_tmr_axi_s_ch_w # (
  parameter unsigned DataWidth = 64
) (

  input  logic  clk_i,
  input  logic  rst_ni,

  // B channel output A
  output logic                     m_axi_a_wvalid_o,
  input  logic                     m_axi_a_wready_i,
  output logic [DataWidth-1:0]     m_axi_a_wdata_o,
  output logic [DataWidth/8-1:0]   m_axi_a_wstrb_o,
  output logic                     m_axi_a_wlast_o,

  // B channel output B
  output logic                     m_axi_b_wvalid_o,
  input  logic                     m_axi_b_wready_i,
  output logic [DataWidth-1:0]     m_axi_b_wdata_o,
  output logic [DataWidth/8-1:0]   m_axi_b_wstrb_o,
  output logic                     m_axi_b_wlast_o,

  // B channel output C
  output logic                     m_axi_c_wvalid_o,
  input  logic                     m_axi_c_wready_i,
  output logic [DataWidth-1:0]     m_axi_c_wdata_o,
  output logic [DataWidth/8-1:0]   m_axi_c_wstrb_o,
  output logic                     m_axi_c_wlast_o,

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

  // W channel input
  input  logic                     s_axi_wvalid_i,
  output logic                     s_axi_wready_o,
  input  logic [DataWidth-1:0]     s_axi_wdata_i,
  input  logic [DataWidth/8-1:0]   s_axi_wstrb_i,
  input  logic                     s_axi_wlast_i
);

  // Insert TMR AXI ready module for wready
  el2_tmr_axi_rdy x_ready (
    .clk_i         (clk_i),
    .rst_ni        (rst_ni),

    .ready_a_i     (m_axi_a_wready_i),
    .ready_b_i     (m_axi_b_wready_i),
    .ready_c_i     (m_axi_c_wready_i),

    .fault_a_o     (m_axi_a_fault_o),
    .fault_b_o     (m_axi_b_fault_o),
    .fault_c_o     (m_axi_c_fault_o),

    .fault_a_i     (m_axi_a_fault_i),
    .fault_b_i     (m_axi_b_fault_i),
    .fault_c_i     (m_axi_c_fault_i),

    .fault_clr_a_i (m_axi_a_fault_clr_i),
    .fault_clr_b_i (m_axi_b_fault_clr_i),
    .fault_clr_c_i (m_axi_c_fault_clr_i),

    .ready_o       (s_axi_wready_o)
  );

  // Pass AXI AW/AR channel signals through
  always_comb begin
    m_axi_a_wvalid_o = s_axi_wvalid_i;
    m_axi_a_wdata_o  = s_axi_wdata_i;
    m_axi_a_wstrb_o  = s_axi_wstrb_i;
    m_axi_a_wlast_o  = s_axi_wlast_i;

    m_axi_b_wvalid_o = s_axi_wvalid_i;
    m_axi_b_wdata_o  = s_axi_wdata_i;
    m_axi_b_wstrb_o  = s_axi_wstrb_i;
    m_axi_b_wlast_o  = s_axi_wlast_i;

    m_axi_c_wvalid_o = s_axi_wvalid_i;
    m_axi_c_wdata_o  = s_axi_wdata_i;
    m_axi_c_wstrb_o  = s_axi_wstrb_i;
    m_axi_c_wlast_o  = s_axi_wlast_i;
  end

endmodule
