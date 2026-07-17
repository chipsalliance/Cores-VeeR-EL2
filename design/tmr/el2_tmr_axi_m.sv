//
// Copyright (c) 2026 Antmicro
// SPDX-License-Identifier: Apache-2.0

module el2_tmr_axi_m # (
  parameter unsigned AddrWidth = 32,
  parameter unsigned DataWidth = 64,
  parameter unsigned IdWidth   = 1
) (

  input  logic  clk_i,
  input  logic  rst_ni,

  // AXI port for core A
  input  logic                     s_axi_a_awvalid_i,
  output logic                     s_axi_a_awready_o,
  input  logic [IdWidth-1:0]       s_axi_a_awid_i,
  input  logic [AddrWidth-1:0]     s_axi_a_awaddr_i,
  input  logic [3:0]               s_axi_a_awregion_i,
  input  logic [7:0]               s_axi_a_awlen_i,
  input  logic [2:0]               s_axi_a_awsize_i,
  input  logic [1:0]               s_axi_a_awburst_i,
  input  logic                     s_axi_a_awlock_i,
  input  logic [3:0]               s_axi_a_awcache_i,
  input  logic [2:0]               s_axi_a_awprot_i,
  input  logic [3:0]               s_axi_a_awqos_i,

  input  logic                     s_axi_a_wvalid_i,
  output logic                     s_axi_a_wready_o,
  input  logic [DataWidth-1:0]     s_axi_a_wdata_i,
  input  logic [DataWidth/8-1:0]   s_axi_a_wstrb_i,
  input  logic                     s_axi_a_wlast_i,

  output logic                     s_axi_a_bvalid_o,
  input  logic                     s_axi_a_bready_i,
  output logic [1:0]               s_axi_a_bresp_o,
  output logic [IdWidth-1:0]       s_axi_a_bid_o,

  input  logic                     s_axi_a_arvalid_i,
  output logic                     s_axi_a_arready_o,
  input  logic [IdWidth-1:0]       s_axi_a_arid_i,
  input  logic [AddrWidth-1:0]     s_axi_a_araddr_i,
  input  logic [3:0]               s_axi_a_arregion_i,
  input  logic [7:0]               s_axi_a_arlen_i,
  input  logic [2:0]               s_axi_a_arsize_i,
  input  logic [1:0]               s_axi_a_arburst_i,
  input  logic                     s_axi_a_arlock_i,
  input  logic [3:0]               s_axi_a_arcache_i,
  input  logic [2:0]               s_axi_a_arprot_i,
  input  logic [3:0]               s_axi_a_arqos_i,

  output logic                     s_axi_a_rvalid_o,
  input  logic                     s_axi_a_rready_i,
  output logic [IdWidth-1:0]       s_axi_a_rid_o,
  output logic [DataWidth-1:0]     s_axi_a_rdata_o,
  output logic [1:0]               s_axi_a_rresp_o,
  output logic                     s_axi_a_rlast_o,

  // AXI port for core A
  input  logic                     s_axi_b_awvalid_i,
  output logic                     s_axi_b_awready_o,
  input  logic [IdWidth-1:0]       s_axi_b_awid_i,
  input  logic [AddrWidth-1:0]     s_axi_b_awaddr_i,
  input  logic [3:0]               s_axi_b_awregion_i,
  input  logic [7:0]               s_axi_b_awlen_i,
  input  logic [2:0]               s_axi_b_awsize_i,
  input  logic [1:0]               s_axi_b_awburst_i,
  input  logic                     s_axi_b_awlock_i,
  input  logic [3:0]               s_axi_b_awcache_i,
  input  logic [2:0]               s_axi_b_awprot_i,
  input  logic [3:0]               s_axi_b_awqos_i,

  input  logic                     s_axi_b_wvalid_i,
  output logic                     s_axi_b_wready_o,
  input  logic [DataWidth-1:0]     s_axi_b_wdata_i,
  input  logic [DataWidth/8-1:0]   s_axi_b_wstrb_i,
  input  logic                     s_axi_b_wlast_i,

  output logic                     s_axi_b_bvalid_o,
  input  logic                     s_axi_b_bready_i,
  output logic [1:0]               s_axi_b_bresp_o,
  output logic [IdWidth-1:0]       s_axi_b_bid_o,

  input  logic                     s_axi_b_arvalid_i,
  output logic                     s_axi_b_arready_o,
  input  logic [IdWidth-1:0]       s_axi_b_arid_i,
  input  logic [AddrWidth-1:0]     s_axi_b_araddr_i,
  input  logic [3:0]               s_axi_b_arregion_i,
  input  logic [7:0]               s_axi_b_arlen_i,
  input  logic [2:0]               s_axi_b_arsize_i,
  input  logic [1:0]               s_axi_b_arburst_i,
  input  logic                     s_axi_b_arlock_i,
  input  logic [3:0]               s_axi_b_arcache_i,
  input  logic [2:0]               s_axi_b_arprot_i,
  input  logic [3:0]               s_axi_b_arqos_i,

  output logic                     s_axi_b_rvalid_o,
  input  logic                     s_axi_b_rready_i,
  output logic [IdWidth-1:0]       s_axi_b_rid_o,
  output logic [DataWidth-1:0]     s_axi_b_rdata_o,
  output logic [1:0]               s_axi_b_rresp_o,
  output logic                     s_axi_b_rlast_o,

  // AXI port for core C
  input  logic                     s_axi_c_awvalid_i,
  output logic                     s_axi_c_awready_o,
  input  logic [IdWidth-1:0]       s_axi_c_awid_i,
  input  logic [AddrWidth-1:0]     s_axi_c_awaddr_i,
  input  logic [3:0]               s_axi_c_awregion_i,
  input  logic [7:0]               s_axi_c_awlen_i,
  input  logic [2:0]               s_axi_c_awsize_i,
  input  logic [1:0]               s_axi_c_awburst_i,
  input  logic                     s_axi_c_awlock_i,
  input  logic [3:0]               s_axi_c_awcache_i,
  input  logic [2:0]               s_axi_c_awprot_i,
  input  logic [3:0]               s_axi_c_awqos_i,

  input  logic                     s_axi_c_wvalid_i,
  output logic                     s_axi_c_wready_o,
  input  logic [DataWidth-1:0]     s_axi_c_wdata_i,
  input  logic [DataWidth/8-1:0]   s_axi_c_wstrb_i,
  input  logic                     s_axi_c_wlast_i,

  output logic                     s_axi_c_bvalid_o,
  input  logic                     s_axi_c_bready_i,
  output logic [1:0]               s_axi_c_bresp_o,
  output logic [IdWidth-1:0]       s_axi_c_bid_o,

  input  logic                     s_axi_c_arvalid_i,
  output logic                     s_axi_c_arready_o,
  input  logic [IdWidth-1:0]       s_axi_c_arid_i,
  input  logic [AddrWidth-1:0]     s_axi_c_araddr_i,
  input  logic [3:0]               s_axi_c_arregion_i,
  input  logic [7:0]               s_axi_c_arlen_i,
  input  logic [2:0]               s_axi_c_arsize_i,
  input  logic [1:0]               s_axi_c_arburst_i,
  input  logic                     s_axi_c_arlock_i,
  input  logic [3:0]               s_axi_c_arcache_i,
  input  logic [2:0]               s_axi_c_arprot_i,
  input  logic [3:0]               s_axi_c_arqos_i,

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

  // Outgoing AXI manager port
  output logic                     m_axi_awvalid_o,
  input  logic                     m_axi_awready_i,
  output logic [IdWidth-1:0]       m_axi_awid_o,
  output logic [AddrWidth-1:0]     m_axi_awaddr_o,
  output logic [3:0]               m_axi_awregion_o,
  output logic [7:0]               m_axi_awlen_o,
  output logic [2:0]               m_axi_awsize_o,
  output logic [1:0]               m_axi_awburst_o,
  output logic                     m_axi_awlock_o,
  output logic [3:0]               m_axi_awcache_o,
  output logic [2:0]               m_axi_awprot_o,
  output logic [3:0]               m_axi_awqos_o,

  output logic                     m_axi_wvalid_o,
  input  logic                     m_axi_wready_i,
  output logic [DataWidth-1:0]     m_axi_wdata_o,
  output logic [DataWidth/8-1:0]   m_axi_wstrb_o,
  output logic                     m_axi_wlast_o,

  input  logic                     m_axi_bvalid_i,
  output logic                     m_axi_bready_o,
  input  logic [1:0]               m_axi_bresp_i,
  input  logic [IdWidth-1:0]       m_axi_bid_i,

  output logic                     m_axi_arvalid_o,
  input  logic                     m_axi_arready_i,
  output logic [IdWidth-1:0]       m_axi_arid_o,
  output logic [AddrWidth-1:0]     m_axi_araddr_o,
  output logic [3:0]               m_axi_arregion_o,
  output logic [7:0]               m_axi_arlen_o,
  output logic [2:0]               m_axi_arsize_o,
  output logic [1:0]               m_axi_arburst_o,
  output logic                     m_axi_arlock_o,
  output logic [3:0]               m_axi_arcache_o,
  output logic [2:0]               m_axi_arprot_o,
  output logic [3:0]               m_axi_arqos_o,

  input  logic                     m_axi_rvalid_i,
  output logic                     m_axi_rready_o,
  input  logic [IdWidth-1:0]       m_axi_rid_i,
  input  logic [DataWidth-1:0]     m_axi_rdata_i,
  input  logic [1:0]               m_axi_rresp_i,
  input  logic                     m_axi_rlast_i
);

  import el2_mubi_pkg::*;

  el2_mubi_t s_axi_a_fault;
  el2_mubi_t s_axi_b_fault;
  el2_mubi_t s_axi_c_fault;

  // ......................................................
  // AXI AW channel
  el2_mubi_t s_axi_aw_a_fault;
  el2_mubi_t s_axi_aw_b_fault;
  el2_mubi_t s_axi_aw_c_fault;

  el2_tmr_axi_m_ch_ax # (
    .AddrWidth (AddrWidth),
    .IdWidth   (IdWidth)

  ) ch_aw (

    .clk_i               (clk_i),
    .rst_ni              (rst_ni),

    .s_axi_a_axvalid_i   (s_axi_a_awvalid_i),
    .s_axi_a_axready_o   (s_axi_a_awready_o),
    .s_axi_a_axid_i      (s_axi_a_awid_i),
    .s_axi_a_axaddr_i    (s_axi_a_awaddr_i),
    .s_axi_a_axregion_i  (s_axi_a_awregion_i),
    .s_axi_a_axlen_i     (s_axi_a_awlen_i),
    .s_axi_a_axsize_i    (s_axi_a_awsize_i),
    .s_axi_a_axburst_i   (s_axi_a_awburst_i),
    .s_axi_a_axlock_i    (s_axi_a_awlock_i),
    .s_axi_a_axcache_i   (s_axi_a_awcache_i),
    .s_axi_a_axprot_i    (s_axi_a_awprot_i),
    .s_axi_a_axqos_i     (s_axi_a_awqos_i),

    .s_axi_b_axvalid_i   (s_axi_b_awvalid_i),
    .s_axi_b_axready_o   (s_axi_b_awready_o),
    .s_axi_b_axid_i      (s_axi_b_awid_i),
    .s_axi_b_axaddr_i    (s_axi_b_awaddr_i),
    .s_axi_b_axregion_i  (s_axi_b_awregion_i),
    .s_axi_b_axlen_i     (s_axi_b_awlen_i),
    .s_axi_b_axsize_i    (s_axi_b_awsize_i),
    .s_axi_b_axburst_i   (s_axi_b_awburst_i),
    .s_axi_b_axlock_i    (s_axi_b_awlock_i),
    .s_axi_b_axcache_i   (s_axi_b_awcache_i),
    .s_axi_b_axprot_i    (s_axi_b_awprot_i),
    .s_axi_b_axqos_i     (s_axi_b_awqos_i),

    .s_axi_c_axvalid_i   (s_axi_c_awvalid_i),
    .s_axi_c_axready_o   (s_axi_c_awready_o),
    .s_axi_c_axid_i      (s_axi_c_awid_i),
    .s_axi_c_axaddr_i    (s_axi_c_awaddr_i),
    .s_axi_c_axregion_i  (s_axi_c_awregion_i),
    .s_axi_c_axlen_i     (s_axi_c_awlen_i),
    .s_axi_c_axsize_i    (s_axi_c_awsize_i),
    .s_axi_c_axburst_i   (s_axi_c_awburst_i),
    .s_axi_c_axlock_i    (s_axi_c_awlock_i),
    .s_axi_c_axcache_i   (s_axi_c_awcache_i),
    .s_axi_c_axprot_i    (s_axi_c_awprot_i),
    .s_axi_c_axqos_i     (s_axi_c_awqos_i),

    .s_axi_a_fault_o     (s_axi_aw_a_fault),
    .s_axi_b_fault_o     (s_axi_aw_b_fault),
    .s_axi_c_fault_o     (s_axi_aw_c_fault),

    .s_axi_a_fault_i     (s_axi_a_fault),
    .s_axi_b_fault_i     (s_axi_b_fault),
    .s_axi_c_fault_i     (s_axi_c_fault),

    .s_axi_a_fault_clr_i (s_axi_a_fault_clr_i),
    .s_axi_b_fault_clr_i (s_axi_b_fault_clr_i),
    .s_axi_c_fault_clr_i (s_axi_c_fault_clr_i),

    .m_axi_axvalid_o     (m_axi_awvalid_o),
    .m_axi_axready_i     (m_axi_awready_i),
    .m_axi_axid_o        (m_axi_awid_o),
    .m_axi_axaddr_o      (m_axi_awaddr_o),
    .m_axi_axregion_o    (m_axi_awregion_o),
    .m_axi_axlen_o       (m_axi_awlen_o),
    .m_axi_axsize_o      (m_axi_awsize_o),
    .m_axi_axburst_o     (m_axi_awburst_o),
    .m_axi_axlock_o      (m_axi_awlock_o),
    .m_axi_axcache_o     (m_axi_awcache_o),
    .m_axi_axprot_o      (m_axi_awprot_o),
    .m_axi_axqos_o       (m_axi_awqos_o)
  );

  // ........................................_i..............
  // AXI W channel
  el2_mubi_t s_axi_w_a_fault;
  el2_mubi_t s_axi_w_b_fault;
  el2_mubi_t s_axi_w_c_fault;

  el2_tmr_axi_m_ch_w # (
    .DataWidth (DataWidth)

  ) ch_w (

    .clk_i               (clk_i),
    .rst_ni              (rst_ni),

    .s_axi_a_wvalid_i    (s_axi_a_wvalid_i),
    .s_axi_a_wready_o    (s_axi_a_wready_o),
    .s_axi_a_wdata_i     (s_axi_a_wdata_i),
    .s_axi_a_wstrb_i     (s_axi_a_wstrb_i),
    .s_axi_a_wlast_i     (s_axi_a_wlast_i),

    .s_axi_b_wvalid_i    (s_axi_b_wvalid_i),
    .s_axi_b_wready_o    (s_axi_b_wready_o),
    .s_axi_b_wdata_i     (s_axi_b_wdata_i),
    .s_axi_b_wstrb_i     (s_axi_b_wstrb_i),
    .s_axi_b_wlast_i     (s_axi_b_wlast_i),

    .s_axi_c_wvalid_i    (s_axi_c_wvalid_i),
    .s_axi_c_wready_o    (s_axi_c_wready_o),
    .s_axi_c_wdata_i     (s_axi_c_wdata_i),
    .s_axi_c_wstrb_i     (s_axi_c_wstrb_i),
    .s_axi_c_wlast_i     (s_axi_c_wlast_i),

    .s_axi_a_fault_o     (s_axi_w_a_fault),
    .s_axi_b_fault_o     (s_axi_w_b_fault),
    .s_axi_c_fault_o     (s_axi_w_c_fault),

    .s_axi_a_fault_i     (s_axi_a_fault),
    .s_axi_b_fault_i     (s_axi_b_fault),
    .s_axi_c_fault_i     (s_axi_c_fault),

    .s_axi_a_fault_clr_i (s_axi_a_fault_clr_i),
    .s_axi_b_fault_clr_i (s_axi_b_fault_clr_i),
    .s_axi_c_fault_clr_i (s_axi_c_fault_clr_i),

    .m_axi_wvalid_o      (m_axi_wvalid_o),
    .m_axi_wready_i      (m_axi_wready_i),
    .m_axi_wdata_o       (m_axi_wdata_o),
    .m_axi_wstrb_o       (m_axi_wstrb_o),
    .m_axi_wlast_o       (m_axi_wlast_o)
  );

  // ......................................................
  // AXI B channel
  el2_mubi_t s_axi_b_a_fault;
  el2_mubi_t s_axi_b_b_fault;
  el2_mubi_t s_axi_b_c_fault;

  el2_tmr_axi_m_ch_b # (
    .IdWidth (IdWidth)

  ) ch_b (

    .clk_i               (clk_i),
    .rst_ni              (rst_ni),

    .s_axi_a_bvalid_o    (s_axi_a_bvalid_o),
    .s_axi_a_bready_i    (s_axi_a_bready_i),
    .s_axi_a_bresp_o     (s_axi_a_bresp_o),
    .s_axi_a_bid_o       (s_axi_a_bid_o),

    .s_axi_b_bvalid_o    (s_axi_b_bvalid_o),
    .s_axi_b_bready_i    (s_axi_b_bready_i),
    .s_axi_b_bresp_o     (s_axi_b_bresp_o),
    .s_axi_b_bid_o       (s_axi_b_bid_o),

    .s_axi_c_bvalid_o    (s_axi_c_bvalid_o),
    .s_axi_c_bready_i    (s_axi_c_bready_i),
    .s_axi_c_bresp_o     (s_axi_c_bresp_o),
    .s_axi_c_bid_o       (s_axi_c_bid_o),

    .s_axi_a_fault_o     (s_axi_b_a_fault),
    .s_axi_b_fault_o     (s_axi_b_b_fault),
    .s_axi_c_fault_o     (s_axi_b_c_fault),

    .s_axi_a_fault_i     (s_axi_a_fault),
    .s_axi_b_fault_i     (s_axi_b_fault),
    .s_axi_c_fault_i     (s_axi_c_fault),

    .s_axi_a_fault_clr_i (s_axi_a_fault_clr_i),
    .s_axi_b_fault_clr_i (s_axi_b_fault_clr_i),
    .s_axi_c_fault_clr_i (s_axi_c_fault_clr_i),

    .m_axi_bvalid_i      (m_axi_bvalid_i),
    .m_axi_bready_o      (m_axi_bready_o),
    .m_axi_bresp_i       (m_axi_bresp_i),
    .m_axi_bid_i         (m_axi_bid_i)
  );

  // ......................................................
  // AXI AR channel
  el2_mubi_t s_axi_ar_a_fault;
  el2_mubi_t s_axi_ar_b_fault;
  el2_mubi_t s_axi_ar_c_fault;

  el2_tmr_axi_m_ch_ax # (
    .AddrWidth (AddrWidth),
    .IdWidth   (IdWidth)

  ) ch_ar (

    .clk_i               (clk_i),
    .rst_ni              (rst_ni),

    .s_axi_a_axvalid_i   (s_axi_a_arvalid_i),
    .s_axi_a_axready_o   (s_axi_a_arready_o),
    .s_axi_a_axid_i      (s_axi_a_arid_i),
    .s_axi_a_axaddr_i    (s_axi_a_araddr_i),
    .s_axi_a_axregion_i  (s_axi_a_arregion_i),
    .s_axi_a_axlen_i     (s_axi_a_arlen_i),
    .s_axi_a_axsize_i    (s_axi_a_arsize_i),
    .s_axi_a_axburst_i   (s_axi_a_arburst_i),
    .s_axi_a_axlock_i    (s_axi_a_arlock_i),
    .s_axi_a_axcache_i   (s_axi_a_arcache_i),
    .s_axi_a_axprot_i    (s_axi_a_arprot_i),
    .s_axi_a_axqos_i     (s_axi_a_arqos_i),

    .s_axi_b_axvalid_i   (s_axi_b_arvalid_i),
    .s_axi_b_axready_o   (s_axi_b_arready_o),
    .s_axi_b_axid_i      (s_axi_b_arid_i),
    .s_axi_b_axaddr_i    (s_axi_b_araddr_i),
    .s_axi_b_axregion_i  (s_axi_b_arregion_i),
    .s_axi_b_axlen_i     (s_axi_b_arlen_i),
    .s_axi_b_axsize_i    (s_axi_b_arsize_i),
    .s_axi_b_axburst_i   (s_axi_b_arburst_i),
    .s_axi_b_axlock_i    (s_axi_b_arlock_i),
    .s_axi_b_axcache_i   (s_axi_b_arcache_i),
    .s_axi_b_axprot_i    (s_axi_b_arprot_i),
    .s_axi_b_axqos_i     (s_axi_b_arqos_i),

    .s_axi_c_axvalid_i   (s_axi_c_arvalid_i),
    .s_axi_c_axready_o   (s_axi_c_arready_o),
    .s_axi_c_axid_i      (s_axi_c_arid_i),
    .s_axi_c_axaddr_i    (s_axi_c_araddr_i),
    .s_axi_c_axregion_i  (s_axi_c_arregion_i),
    .s_axi_c_axlen_i     (s_axi_c_arlen_i),
    .s_axi_c_axsize_i    (s_axi_c_arsize_i),
    .s_axi_c_axburst_i   (s_axi_c_arburst_i),
    .s_axi_c_axlock_i    (s_axi_c_arlock_i),
    .s_axi_c_axcache_i   (s_axi_c_arcache_i),
    .s_axi_c_axprot_i    (s_axi_c_arprot_i),
    .s_axi_c_axqos_i     (s_axi_c_arqos_i),

    .s_axi_a_fault_o     (s_axi_ar_a_fault),
    .s_axi_b_fault_o     (s_axi_ar_b_fault),
    .s_axi_c_fault_o     (s_axi_ar_c_fault),

    .s_axi_a_fault_i     (s_axi_a_fault),
    .s_axi_b_fault_i     (s_axi_b_fault),
    .s_axi_c_fault_i     (s_axi_c_fault),

    .s_axi_a_fault_clr_i (s_axi_a_fault_clr_i),
    .s_axi_b_fault_clr_i (s_axi_b_fault_clr_i),
    .s_axi_c_fault_clr_i (s_axi_c_fault_clr_i),

    .m_axi_axvalid_o     (m_axi_arvalid_o),
    .m_axi_axready_i     (m_axi_arready_i),
    .m_axi_axid_o        (m_axi_arid_o),
    .m_axi_axaddr_o      (m_axi_araddr_o),
    .m_axi_axregion_o    (m_axi_arregion_o),
    .m_axi_axlen_o       (m_axi_arlen_o),
    .m_axi_axsize_o      (m_axi_arsize_o),
    .m_axi_axburst_o     (m_axi_arburst_o),
    .m_axi_axlock_o      (m_axi_arlock_o),
    .m_axi_axcache_o     (m_axi_arcache_o),
    .m_axi_axprot_o      (m_axi_arprot_o),
    .m_axi_axqos_o       (m_axi_arqos_o)
  );

  // ......................................................
  // AXI R channel
  el2_mubi_t s_axi_r_a_fault;
  el2_mubi_t s_axi_r_b_fault;
  el2_mubi_t s_axi_r_c_fault;

  el2_tmr_axi_m_ch_r # (
    .DataWidth (DataWidth),
    .IdWidth   (IdWidth)

  ) ch_r (

    .clk_i               (clk_i),
    .rst_ni              (rst_ni),

    .s_axi_a_rvalid_o    (s_axi_a_rvalid_o),
    .s_axi_a_rready_i    (s_axi_a_rready_i),
    .s_axi_a_rid_o       (s_axi_a_rid_o),
    .s_axi_a_rdata_o     (s_axi_a_rdata_o),
    .s_axi_a_rresp_o     (s_axi_a_rresp_o),
    .s_axi_a_rlast_o     (s_axi_a_rlast_o),

    .s_axi_b_rvalid_o    (s_axi_b_rvalid_o),
    .s_axi_b_rready_i    (s_axi_b_rready_i),
    .s_axi_b_rid_o       (s_axi_b_rid_o),
    .s_axi_b_rdata_o     (s_axi_b_rdata_o),
    .s_axi_b_rresp_o     (s_axi_b_rresp_o),
    .s_axi_b_rlast_o     (s_axi_b_rlast_o),

    .s_axi_c_rvalid_o    (s_axi_c_rvalid_o),
    .s_axi_c_rready_i    (s_axi_c_rready_i),
    .s_axi_c_rid_o       (s_axi_c_rid_o),
    .s_axi_c_rdata_o     (s_axi_c_rdata_o),
    .s_axi_c_rresp_o     (s_axi_c_rresp_o),
    .s_axi_c_rlast_o     (s_axi_c_rlast_o),

    .s_axi_a_fault_o     (s_axi_r_a_fault),
    .s_axi_b_fault_o     (s_axi_r_b_fault),
    .s_axi_c_fault_o     (s_axi_r_c_fault),

    .s_axi_a_fault_i     (s_axi_a_fault),
    .s_axi_b_fault_i     (s_axi_b_fault),
    .s_axi_c_fault_i     (s_axi_c_fault),

    .s_axi_a_fault_clr_i (s_axi_a_fault_clr_i),
    .s_axi_b_fault_clr_i (s_axi_b_fault_clr_i),
    .s_axi_c_fault_clr_i (s_axi_c_fault_clr_i),

    .m_axi_rvalid_i      (m_axi_rvalid_i),
    .m_axi_rready_o      (m_axi_rready_o),
    .m_axi_rid_i         (m_axi_rid_i),
    .m_axi_rdata_i       (m_axi_rdata_i),
    .m_axi_rresp_i       (m_axi_rresp_i),
    .m_axi_rlast_i       (m_axi_rlast_i)
  );

  // ......................................................
  // Fault aggregation and loopback

  el2_mubi_t s_axi_a_fault_l0;
  el2_mubi_t s_axi_a_fault_l1;
  el2_mubi_t s_axi_a_fault_l2;

  el2_mubi_t s_axi_b_fault_l0;
  el2_mubi_t s_axi_b_fault_l1;
  el2_mubi_t s_axi_b_fault_l2;

  el2_mubi_t s_axi_c_fault_l0;
  el2_mubi_t s_axi_c_fault_l1;
  el2_mubi_t s_axi_c_fault_l2;

  always_comb begin
    s_axi_a_fault_l0 = mubi_or(s_axi_aw_a_fault, s_axi_w_a_fault);
    s_axi_a_fault_l1 = mubi_or(s_axi_b_a_fault,  s_axi_ar_a_fault);
    s_axi_a_fault_l2 = mubi_or(s_axi_r_a_fault,  s_axi_a_fault_i);

    s_axi_a_fault    = mubi_or3(s_axi_a_fault_l0, s_axi_a_fault_l1, s_axi_a_fault_l2);
  end

  always_comb begin
    s_axi_b_fault_l0 = mubi_or(s_axi_aw_b_fault, s_axi_w_b_fault);
    s_axi_b_fault_l1 = mubi_or(s_axi_b_b_fault,  s_axi_ar_b_fault);
    s_axi_b_fault_l2 = mubi_or(s_axi_r_b_fault,  s_axi_b_fault_i);

    s_axi_b_fault    = mubi_or3(s_axi_b_fault_l0, s_axi_b_fault_l1, s_axi_b_fault_l2);
  end

  always_comb begin
    s_axi_c_fault_l0 = mubi_or(s_axi_aw_c_fault, s_axi_w_c_fault);
    s_axi_c_fault_l1 = mubi_or(s_axi_b_c_fault,  s_axi_ar_c_fault);
    s_axi_c_fault_l2 = mubi_or(s_axi_r_c_fault,  s_axi_c_fault_i);

    s_axi_c_fault    = mubi_or3(s_axi_c_fault_l0, s_axi_c_fault_l1, s_axi_c_fault_l2);
  end

  // ......................................................
  // Fault output

  always_comb begin
    s_axi_a_fault_o = s_axi_a_fault;
    s_axi_b_fault_o = s_axi_b_fault;
    s_axi_c_fault_o = s_axi_c_fault;
  end

endmodule
