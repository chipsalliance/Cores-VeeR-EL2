//
// Copyright (c) 2026 Antmicro
// SPDX-License-Identifier: Apache-2.0

module el2_tmr_axi_s_ch_w # (
  parameter unsigned DataWidth = 64
) (

  input  logic  clk_i,
  input  logic  rst_ni,

  // B channel output A
  output logic                     a_m_axi_wvalid_o,
  input  logic                     a_m_axi_wready_i,
  output logic [DataWidth-1:0]     a_m_axi_wdata_o,
  output logic [DataWidth/8-1:0]   a_m_axi_wstrb_o,
  output logic                     a_m_axi_wlast_o,

  // B channel output B
  output logic                     b_m_axi_wvalid_o,
  input  logic                     b_m_axi_wready_i,
  output logic [DataWidth-1:0]     b_m_axi_wdata_o,
  output logic [DataWidth/8-1:0]   b_m_axi_wstrb_o,
  output logic                     b_m_axi_wlast_o,

  // B channel output C
  output logic                     c_m_axi_wvalid_o,
  input  logic                     c_m_axi_wready_i,
  output logic [DataWidth-1:0]     c_m_axi_wdata_o,
  output logic [DataWidth/8-1:0]   c_m_axi_wstrb_o,
  output logic                     c_m_axi_wlast_o,

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

    .ready_a_i     (a_m_axi_wready_i),
    .ready_b_i     (b_m_axi_wready_i),
    .ready_c_i     (c_m_axi_wready_i),

    .fault_a_o     (a_m_axi_fault_o),
    .fault_b_o     (b_m_axi_fault_o),
    .fault_c_o     (c_m_axi_fault_o),

    .fault_a_i     (a_m_axi_fault_i),
    .fault_b_i     (b_m_axi_fault_i),
    .fault_c_i     (c_m_axi_fault_i),

    .fault_clr_a_i (a_m_axi_fault_clr_i),
    .fault_clr_b_i (b_m_axi_fault_clr_i),
    .fault_clr_c_i (c_m_axi_fault_clr_i),

    .ready_o       (s_axi_wready_o)
  );

  // Pass AXI AW/AR channel signals through
  always_comb begin
    a_m_axi_wvalid_o = s_axi_wvalid_i;
    a_m_axi_wdata_o  = s_axi_wdata_i;
    a_m_axi_wstrb_o  = s_axi_wstrb_i;
    a_m_axi_wlast_o  = s_axi_wlast_i;

    b_m_axi_wvalid_o = s_axi_wvalid_i;
    b_m_axi_wdata_o  = s_axi_wdata_i;
    b_m_axi_wstrb_o  = s_axi_wstrb_i;
    b_m_axi_wlast_o  = s_axi_wlast_i;

    c_m_axi_wvalid_o = s_axi_wvalid_i;
    c_m_axi_wdata_o  = s_axi_wdata_i;
    c_m_axi_wstrb_o  = s_axi_wstrb_i;
    c_m_axi_wlast_o  = s_axi_wlast_i;
  end

endmodule
