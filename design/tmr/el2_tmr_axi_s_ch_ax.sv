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
  output logic                     m_axi_a_axvalid_o,
  input  logic                     m_axi_a_axready_i,
  output logic [IdWidth-1:0]       m_axi_a_axid_o,
  output logic [AddrWidth-1:0]     m_axi_a_axaddr_o,
  output logic [3:0]               m_axi_a_axregion_o,
  output logic [7:0]               m_axi_a_axlen_o,
  output logic [2:0]               m_axi_a_axsize_o,
  output logic [1:0]               m_axi_a_axburst_o,
  output logic                     m_axi_a_axlock_o,
  output logic [3:0]               m_axi_a_axcache_o,
  output logic [2:0]               m_axi_a_axprot_o,
  output logic [3:0]               m_axi_a_axqos_o,

  // B channel output B
  output logic                     m_axi_b_axvalid_o,
  input  logic                     m_axi_b_axready_i,
  output logic [IdWidth-1:0]       m_axi_b_axid_o,
  output logic [AddrWidth-1:0]     m_axi_b_axaddr_o,
  output logic [3:0]               m_axi_b_axregion_o,
  output logic [7:0]               m_axi_b_axlen_o,
  output logic [2:0]               m_axi_b_axsize_o,
  output logic [1:0]               m_axi_b_axburst_o,
  output logic                     m_axi_b_axlock_o,
  output logic [3:0]               m_axi_b_axcache_o,
  output logic [2:0]               m_axi_b_axprot_o,
  output logic [3:0]               m_axi_b_axqos_o,

  // B channel output C
  output logic                     m_axi_c_axvalid_o,
  input  logic                     m_axi_c_axready_i,
  output logic [IdWidth-1:0]       m_axi_c_axid_o,
  output logic [AddrWidth-1:0]     m_axi_c_axaddr_o,
  output logic [3:0]               m_axi_c_axregion_o,
  output logic [7:0]               m_axi_c_axlen_o,
  output logic [2:0]               m_axi_c_axsize_o,
  output logic [1:0]               m_axi_c_axburst_o,
  output logic                     m_axi_c_axlock_o,
  output logic [3:0]               m_axi_c_axcache_o,
  output logic [2:0]               m_axi_c_axprot_o,
  output logic [3:0]               m_axi_c_axqos_o,

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

    .ready_a_i     (m_axi_a_axready_i),
    .ready_b_i     (m_axi_b_axready_i),
    .ready_c_i     (m_axi_c_axready_i),

    .fault_a_o     (m_axi_a_fault_o),
    .fault_b_o     (m_axi_b_fault_o),
    .fault_c_o     (m_axi_c_fault_o),

    .fault_a_i     (m_axi_a_fault_i),
    .fault_b_i     (m_axi_b_fault_i),
    .fault_c_i     (m_axi_c_fault_i),

    .fault_clr_a_i (m_axi_a_fault_clr_i),
    .fault_clr_b_i (m_axi_b_fault_clr_i),
    .fault_clr_c_i (m_axi_c_fault_clr_i),

    .ready_o       (s_axi_axready_o)
  );

  // Pass AXI AW/AR channel signals through
  always_comb begin
    m_axi_a_axvalid_o  = s_axi_axvalid_i; 
    m_axi_a_axid_o     = s_axi_axid_i; 
    m_axi_a_axaddr_o   = s_axi_axaddr_i; 
    m_axi_a_axregion_o = s_axi_axregion_i; 
    m_axi_a_axlen_o    = s_axi_axlen_i; 
    m_axi_a_axsize_o   = s_axi_axsize_i; 
    m_axi_a_axburst_o  = s_axi_axburst_i; 
    m_axi_a_axlock_o   = s_axi_axlock_i; 
    m_axi_a_axcache_o  = s_axi_axcache_i; 
    m_axi_a_axprot_o   = s_axi_axprot_i; 
    m_axi_a_axqos_o    = s_axi_axqos_i; 

    m_axi_b_axvalid_o  = s_axi_axvalid_i; 
    m_axi_b_axid_o     = s_axi_axid_i; 
    m_axi_b_axaddr_o   = s_axi_axaddr_i; 
    m_axi_b_axregion_o = s_axi_axregion_i; 
    m_axi_b_axlen_o    = s_axi_axlen_i; 
    m_axi_b_axsize_o   = s_axi_axsize_i; 
    m_axi_b_axburst_o  = s_axi_axburst_i; 
    m_axi_b_axlock_o   = s_axi_axlock_i; 
    m_axi_b_axcache_o  = s_axi_axcache_i; 
    m_axi_b_axprot_o   = s_axi_axprot_i; 
    m_axi_b_axqos_o    = s_axi_axqos_i; 

    m_axi_c_axvalid_o  = s_axi_axvalid_i; 
    m_axi_c_axid_o     = s_axi_axid_i; 
    m_axi_c_axaddr_o   = s_axi_axaddr_i; 
    m_axi_c_axregion_o = s_axi_axregion_i; 
    m_axi_c_axlen_o    = s_axi_axlen_i; 
    m_axi_c_axsize_o   = s_axi_axsize_i; 
    m_axi_c_axburst_o  = s_axi_axburst_i; 
    m_axi_c_axlock_o   = s_axi_axlock_i; 
    m_axi_c_axcache_o  = s_axi_axcache_i; 
    m_axi_c_axprot_o   = s_axi_axprot_i; 
    m_axi_c_axqos_o    = s_axi_axqos_i; 
  end

endmodule
