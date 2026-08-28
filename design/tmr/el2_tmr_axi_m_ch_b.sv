//
// Copyright (c) 2026 Antmicro
// SPDX-License-Identifier: Apache-2.0

module el2_tmr_axi_m_ch_b # (
  parameter unsigned IdWidth = 1
) (

  input  logic  clk_i,
  input  logic  rst_ni,

  // B channel output A
  output logic                     a_s_axi_bvalid_o,
  input  logic                     a_s_axi_bready_i,
  output logic [1:0]               a_s_axi_bresp_o,
  output logic [IdWidth-1:0]       a_s_axi_bid_o,

  // B channel output B
  output logic                     b_s_axi_bvalid_o,
  input  logic                     b_s_axi_bready_i,
  output logic [1:0]               b_s_axi_bresp_o,
  output logic [IdWidth-1:0]       b_s_axi_bid_o,

  // B channel output C
  output logic                     c_s_axi_bvalid_o,
  input  logic                     c_s_axi_bready_i,
  output logic [1:0]               c_s_axi_bresp_o,
  output logic [IdWidth-1:0]       c_s_axi_bid_o,

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

  // B channel output
  input  logic                     m_axi_bvalid_i,
  output logic                     m_axi_bready_o,
  input  logic [1:0]               m_axi_bresp_i,
  input  logic [IdWidth-1:0]       m_axi_bid_i

);

  // Insert TMR AXI ready module for bready
  el2_tmr_axi_rdy x_ready (
    .clk_i         (clk_i),
    .rst_ni        (rst_ni),

    .ready_a_i     (a_s_axi_bready_i),
    .ready_b_i     (b_s_axi_bready_i),
    .ready_c_i     (c_s_axi_bready_i),

    .fault_a_o     (a_s_axi_fault_o),
    .fault_b_o     (b_s_axi_fault_o),
    .fault_c_o     (c_s_axi_fault_o),

    .fault_a_i     (a_s_axi_fault_i),
    .fault_b_i     (b_s_axi_fault_i),
    .fault_c_i     (c_s_axi_fault_i),

    .fault_clr_a_i (a_s_axi_fault_clr_i),
    .fault_clr_b_i (b_s_axi_fault_clr_i),
    .fault_clr_c_i (c_s_axi_fault_clr_i),

    .ready_o       (m_axi_bready_o)
  );

  // Pass AXI B channel signals through
  always_comb begin
    a_s_axi_bvalid_o = m_axi_bvalid_i;
    a_s_axi_bresp_o  = m_axi_bresp_i;
    a_s_axi_bid_o    = m_axi_bid_i;

    b_s_axi_bvalid_o = m_axi_bvalid_i;
    b_s_axi_bresp_o  = m_axi_bresp_i;
    b_s_axi_bid_o    = m_axi_bid_i;

    c_s_axi_bvalid_o = m_axi_bvalid_i;
    c_s_axi_bresp_o  = m_axi_bresp_i;
    c_s_axi_bid_o    = m_axi_bid_i;
  end

endmodule
