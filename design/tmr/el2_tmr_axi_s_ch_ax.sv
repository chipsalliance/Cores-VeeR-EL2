//
// Copyright (c) 2026 Antmicro
// SPDX-License-Identifier: Apache-2.0

module el2_tmr_axi_s_ch_ax # (
  parameter unsigned AddrWidth = 32,
  parameter unsigned IdWidth   = 1
) (

  input  logic  clk_i,
  input  logic  rst_ni,

  // B channel output A
  output logic                     a_m_axi_axvalid_o,
  input  logic                     a_m_axi_axready_i,
  output logic [IdWidth-1:0]       a_m_axi_axid_o,
  output logic [AddrWidth-1:0]     a_m_axi_axaddr_o,
  output logic [3:0]               a_m_axi_axregion_o,
  output logic [7:0]               a_m_axi_axlen_o,
  output logic [2:0]               a_m_axi_axsize_o,
  output logic [1:0]               a_m_axi_axburst_o,
  output logic                     a_m_axi_axlock_o,
  output logic [3:0]               a_m_axi_axcache_o,
  output logic [2:0]               a_m_axi_axprot_o,
  output logic [3:0]               a_m_axi_axqos_o,

  // B channel output B
  output logic                     b_m_axi_axvalid_o,
  input  logic                     b_m_axi_axready_i,
  output logic [IdWidth-1:0]       b_m_axi_axid_o,
  output logic [AddrWidth-1:0]     b_m_axi_axaddr_o,
  output logic [3:0]               b_m_axi_axregion_o,
  output logic [7:0]               b_m_axi_axlen_o,
  output logic [2:0]               b_m_axi_axsize_o,
  output logic [1:0]               b_m_axi_axburst_o,
  output logic                     b_m_axi_axlock_o,
  output logic [3:0]               b_m_axi_axcache_o,
  output logic [2:0]               b_m_axi_axprot_o,
  output logic [3:0]               b_m_axi_axqos_o,

  // B channel output C
  output logic                     c_m_axi_axvalid_o,
  input  logic                     c_m_axi_axready_i,
  output logic [IdWidth-1:0]       c_m_axi_axid_o,
  output logic [AddrWidth-1:0]     c_m_axi_axaddr_o,
  output logic [3:0]               c_m_axi_axregion_o,
  output logic [7:0]               c_m_axi_axlen_o,
  output logic [2:0]               c_m_axi_axsize_o,
  output logic [1:0]               c_m_axi_axburst_o,
  output logic                     c_m_axi_axlock_o,
  output logic [3:0]               c_m_axi_axcache_o,
  output logic [2:0]               c_m_axi_axprot_o,
  output logic [3:0]               c_m_axi_axqos_o,

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

  // AR/AW channel input
  input  logic                     s_axi_axvalid_i,
  output logic                     s_axi_axready_o,
  input  logic [IdWidth-1:0]       s_axi_axid_i,
  input  logic [AddrWidth-1:0]     s_axi_axaddr_i,
  input  logic [3:0]               s_axi_axregion_i,
  input  logic [7:0]               s_axi_axlen_i,
  input  logic [2:0]               s_axi_axsize_i,
  input  logic [1:0]               s_axi_axburst_i,
  input  logic                     s_axi_axlock_i,
  input  logic [3:0]               s_axi_axcache_i,
  input  logic [2:0]               s_axi_axprot_i,
  input  logic [3:0]               s_axi_axqos_i

);

  // Insert TMR AXI ready module for axready
  el2_tmr_axi_rdy x_ready (
    .clk_i         (clk_i),
    .rst_ni        (rst_ni),

    .ready_a_i     (a_m_axi_axready_i),
    .ready_b_i     (b_m_axi_axready_i),
    .ready_c_i     (c_m_axi_axready_i),

    .fault_a_o     (a_m_axi_fault_o),
    .fault_b_o     (b_m_axi_fault_o),
    .fault_c_o     (c_m_axi_fault_o),

    .fault_a_i     (a_m_axi_fault_i),
    .fault_b_i     (b_m_axi_fault_i),
    .fault_c_i     (c_m_axi_fault_i),

    .fault_clr_a_i (a_m_axi_fault_clr_i),
    .fault_clr_b_i (b_m_axi_fault_clr_i),
    .fault_clr_c_i (c_m_axi_fault_clr_i),

    .ready_o       (s_axi_axready_o)
  );

  // Pass AXI AW/AR channel signals through
  always_comb begin
    a_m_axi_axvalid_o  = s_axi_axvalid_i; 
    a_m_axi_axid_o     = s_axi_axid_i; 
    a_m_axi_axaddr_o   = s_axi_axaddr_i; 
    a_m_axi_axregion_o = s_axi_axregion_i; 
    a_m_axi_axlen_o    = s_axi_axlen_i; 
    a_m_axi_axsize_o   = s_axi_axsize_i; 
    a_m_axi_axburst_o  = s_axi_axburst_i; 
    a_m_axi_axlock_o   = s_axi_axlock_i; 
    a_m_axi_axcache_o  = s_axi_axcache_i; 
    a_m_axi_axprot_o   = s_axi_axprot_i; 
    a_m_axi_axqos_o    = s_axi_axqos_i; 

    b_m_axi_axvalid_o  = s_axi_axvalid_i; 
    b_m_axi_axid_o     = s_axi_axid_i; 
    b_m_axi_axaddr_o   = s_axi_axaddr_i; 
    b_m_axi_axregion_o = s_axi_axregion_i; 
    b_m_axi_axlen_o    = s_axi_axlen_i; 
    b_m_axi_axsize_o   = s_axi_axsize_i; 
    b_m_axi_axburst_o  = s_axi_axburst_i; 
    b_m_axi_axlock_o   = s_axi_axlock_i; 
    b_m_axi_axcache_o  = s_axi_axcache_i; 
    b_m_axi_axprot_o   = s_axi_axprot_i; 
    b_m_axi_axqos_o    = s_axi_axqos_i; 

    c_m_axi_axvalid_o  = s_axi_axvalid_i; 
    c_m_axi_axid_o     = s_axi_axid_i; 
    c_m_axi_axaddr_o   = s_axi_axaddr_i; 
    c_m_axi_axregion_o = s_axi_axregion_i; 
    c_m_axi_axlen_o    = s_axi_axlen_i; 
    c_m_axi_axsize_o   = s_axi_axsize_i; 
    c_m_axi_axburst_o  = s_axi_axburst_i; 
    c_m_axi_axlock_o   = s_axi_axlock_i; 
    c_m_axi_axcache_o  = s_axi_axcache_i; 
    c_m_axi_axprot_o   = s_axi_axprot_i; 
    c_m_axi_axqos_o    = s_axi_axqos_i; 
  end

endmodule
