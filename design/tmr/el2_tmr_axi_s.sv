//
// Copyright (c) 2026 Antmicro
// SPDX-License-Identifier: Apache-2.0

module el2_tmr_axi_s # (
  parameter unsigned AddrWidth = 32,
  parameter unsigned DataWidth = 64,
  parameter unsigned IdWidth   = 1
) (

  input  logic  clk_i,
  input  logic  rst_ni,

  // AXI port for core A
  output logic                     m_axi_a_awvalid_o,
  input  logic                     m_axi_a_awready_i,
  output logic [IdWidth-1:0]       m_axi_a_awid_o,
  output logic [AddrWidth-1:0]     m_axi_a_awaddr_o,
  output logic [3:0]               m_axi_a_awregion_o,
  output logic [7:0]               m_axi_a_awlen_o,
  output logic [2:0]               m_axi_a_awsize_o,
  output logic [1:0]               m_axi_a_awburst_o,
  output logic                     m_axi_a_awlock_o,
  output logic [3:0]               m_axi_a_awcache_o,
  output logic [2:0]               m_axi_a_awprot_o,
  output logic [3:0]               m_axi_a_awqos_o,

  output logic                     m_axi_a_wvalid_o,
  input  logic                     m_axi_a_wready_i,
  output logic [DataWidth-1:0]     m_axi_a_wdata_o,
  output logic [DataWidth/8-1:0]   m_axi_a_wstrb_o,
  output logic                     m_axi_a_wlast_o,

  input  logic                     m_axi_a_bvalid_i,
  output logic                     m_axi_a_bready_o,
  input  logic [1:0]               m_axi_a_bresp_i,
  input  logic [IdWidth-1:0]       m_axi_a_bid_i,

  output logic                     m_axi_a_arvalid_o,
  input  logic                     m_axi_a_arready_i,
  output logic [IdWidth-1:0]       m_axi_a_arid_o,
  output logic [AddrWidth-1:0]     m_axi_a_araddr_o,
  output logic [3:0]               m_axi_a_arregion_o,
  output logic [7:0]               m_axi_a_arlen_o,
  output logic [2:0]               m_axi_a_arsize_o,
  output logic [1:0]               m_axi_a_arburst_o,
  output logic                     m_axi_a_arlock_o,
  output logic [3:0]               m_axi_a_arcache_o,
  output logic [2:0]               m_axi_a_arprot_o,
  output logic [3:0]               m_axi_a_arqos_o,

  input  logic                     m_axi_a_rvalid_i,
  output logic                     m_axi_a_rready_o,
  input  logic [IdWidth-1:0]       m_axi_a_rid_i,
  input  logic [DataWidth-1:0]     m_axi_a_rdata_i,
  input  logic [1:0]               m_axi_a_rresp_i,
  input  logic                     m_axi_a_rlast_i,

  // AXI port for core A
  output logic                     m_axi_b_awvalid_o,
  input  logic                     m_axi_b_awready_i,
  output logic [IdWidth-1:0]       m_axi_b_awid_o,
  output logic [AddrWidth-1:0]     m_axi_b_awaddr_o,
  output logic [3:0]               m_axi_b_awregion_o,
  output logic [7:0]               m_axi_b_awlen_o,
  output logic [2:0]               m_axi_b_awsize_o,
  output logic [1:0]               m_axi_b_awburst_o,
  output logic                     m_axi_b_awlock_o,
  output logic [3:0]               m_axi_b_awcache_o,
  output logic [2:0]               m_axi_b_awprot_o,
  output logic [3:0]               m_axi_b_awqos_o,

  output logic                     m_axi_b_wvalid_o,
  input  logic                     m_axi_b_wready_i,
  output logic [DataWidth-1:0]     m_axi_b_wdata_o,
  output logic [DataWidth/8-1:0]   m_axi_b_wstrb_o,
  output logic                     m_axi_b_wlast_o,

  input  logic                     m_axi_b_bvalid_i,
  output logic                     m_axi_b_bready_o,
  input  logic [1:0]               m_axi_b_bresp_i,
  input  logic [IdWidth-1:0]       m_axi_b_bid_i,

  output logic                     m_axi_b_arvalid_o,
  input  logic                     m_axi_b_arready_i,
  output logic [IdWidth-1:0]       m_axi_b_arid_o,
  output logic [AddrWidth-1:0]     m_axi_b_araddr_o,
  output logic [3:0]               m_axi_b_arregion_o,
  output logic [7:0]               m_axi_b_arlen_o,
  output logic [2:0]               m_axi_b_arsize_o,
  output logic [1:0]               m_axi_b_arburst_o,
  output logic                     m_axi_b_arlock_o,
  output logic [3:0]               m_axi_b_arcache_o,
  output logic [2:0]               m_axi_b_arprot_o,
  output logic [3:0]               m_axi_b_arqos_o,

  input  logic                     m_axi_b_rvalid_i,
  output logic                     m_axi_b_rready_o,
  input  logic [IdWidth-1:0]       m_axi_b_rid_i,
  input  logic [DataWidth-1:0]     m_axi_b_rdata_i,
  input  logic [1:0]               m_axi_b_rresp_i,
  input  logic                     m_axi_b_rlast_i,

  // AXI port for core C
  output logic                     m_axi_c_awvalid_o,
  input  logic                     m_axi_c_awready_i,
  output logic [IdWidth-1:0]       m_axi_c_awid_o,
  output logic [AddrWidth-1:0]     m_axi_c_awaddr_o,
  output logic [3:0]               m_axi_c_awregion_o,
  output logic [7:0]               m_axi_c_awlen_o,
  output logic [2:0]               m_axi_c_awsize_o,
  output logic [1:0]               m_axi_c_awburst_o,
  output logic                     m_axi_c_awlock_o,
  output logic [3:0]               m_axi_c_awcache_o,
  output logic [2:0]               m_axi_c_awprot_o,
  output logic [3:0]               m_axi_c_awqos_o,

  output logic                     m_axi_c_wvalid_o,
  input  logic                     m_axi_c_wready_i,
  output logic [DataWidth-1:0]     m_axi_c_wdata_o,
  output logic [DataWidth/8-1:0]   m_axi_c_wstrb_o,
  output logic                     m_axi_c_wlast_o,

  input  logic                     m_axi_c_bvalid_i,
  output logic                     m_axi_c_bready_o,
  input  logic [1:0]               m_axi_c_bresp_i,
  input  logic [IdWidth-1:0]       m_axi_c_bid_i,

  output logic                     m_axi_c_arvalid_o,
  input  logic                     m_axi_c_arready_i,
  output logic [IdWidth-1:0]       m_axi_c_arid_o,
  output logic [AddrWidth-1:0]     m_axi_c_araddr_o,
  output logic [3:0]               m_axi_c_arregion_o,
  output logic [7:0]               m_axi_c_arlen_o,
  output logic [2:0]               m_axi_c_arsize_o,
  output logic [1:0]               m_axi_c_arburst_o,
  output logic                     m_axi_c_arlock_o,
  output logic [3:0]               m_axi_c_arcache_o,
  output logic [2:0]               m_axi_c_arprot_o,
  output logic [3:0]               m_axi_c_arqos_o,

  input  logic                     m_axi_c_rvalid_i,
  output logic                     m_axi_c_rready_o,
  input  logic [IdWidth-1:0]       m_axi_c_rid_i,
  input  logic [DataWidth-1:0]     m_axi_c_rdata_i,
  input  logic [1:0]               m_axi_c_rresp_i,
  input  logic                     m_axi_c_rlast_i,

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

  // Outgoing AXI subordinate port
  input  logic                     s_axi_awvalid_i,
  output logic                     s_axi_awready_o,
  input  logic [IdWidth-1:0]       s_axi_awid_i,
  input  logic [AddrWidth-1:0]     s_axi_awaddr_i,
  input  logic [3:0]               s_axi_awregion_i,
  input  logic [7:0]               s_axi_awlen_i,
  input  logic [2:0]               s_axi_awsize_i,
  input  logic [1:0]               s_axi_awburst_i,
  input  logic                     s_axi_awlock_i,
  input  logic [3:0]               s_axi_awcache_i,
  input  logic [2:0]               s_axi_awprot_i,
  input  logic [3:0]               s_axi_awqos_i,

  input  logic                     s_axi_wvalid_i,
  output logic                     s_axi_wready_o,
  input  logic [DataWidth-1:0]     s_axi_wdata_i,
  input  logic [DataWidth/8-1:0]   s_axi_wstrb_i,
  input  logic                     s_axi_wlast_i,

  output logic                     s_axi_bvalid_o,
  input  logic                     s_axi_bready_i,
  output logic [1:0]               s_axi_bresp_o,
  output logic [IdWidth-1:0]       s_axi_bid_o,

  input  logic                     s_axi_arvalid_i,
  output logic                     s_axi_arready_o,
  input  logic [IdWidth-1:0]       s_axi_arid_i,
  input  logic [AddrWidth-1:0]     s_axi_araddr_i,
  input  logic [3:0]               s_axi_arregion_i,
  input  logic [7:0]               s_axi_arlen_i,
  input  logic [2:0]               s_axi_arsize_i,
  input  logic [1:0]               s_axi_arburst_i,
  input  logic                     s_axi_arlock_i,
  input  logic [3:0]               s_axi_arcache_i,
  input  logic [2:0]               s_axi_arprot_i,
  input  logic [3:0]               s_axi_arqos_i,

  output logic                     s_axi_rvalid_o,
  input  logic                     s_axi_rready_i,
  output logic [IdWidth-1:0]       s_axi_rid_o,
  output logic [DataWidth-1:0]     s_axi_rdata_o,
  output logic [1:0]               s_axi_rresp_o,
  output logic                     s_axi_rlast_o
);

  import el2_mubi_pkg::*;

  el2_mubi_t m_axi_a_fault;
  el2_mubi_t m_axi_b_fault;
  el2_mubi_t m_axi_c_fault;

  // ......................................................
  // AXI AW channel
  el2_mubi_t m_axi_aw_a_fault;
  el2_mubi_t m_axi_aw_b_fault;
  el2_mubi_t m_axi_aw_c_fault;

  el2_tmr_axi_s_ch_ax # (
    .AddrWidth (AddrWidth),
    .IdWidth   (IdWidth)

  ) ch_aw (

    .clk_i               (clk_i),
    .rst_ni              (rst_ni),

    .m_axi_a_axvalid_o   (m_axi_a_awvalid_o),
    .m_axi_a_axready_i   (m_axi_a_awready_i),
    .m_axi_a_axid_o      (m_axi_a_awid_o),
    .m_axi_a_axaddr_o    (m_axi_a_awaddr_o),
    .m_axi_a_axregion_o  (m_axi_a_awregion_o),
    .m_axi_a_axlen_o     (m_axi_a_awlen_o),
    .m_axi_a_axsize_o    (m_axi_a_awsize_o),
    .m_axi_a_axburst_o   (m_axi_a_awburst_o),
    .m_axi_a_axlock_o    (m_axi_a_awlock_o),
    .m_axi_a_axcache_o   (m_axi_a_awcache_o),
    .m_axi_a_axprot_o    (m_axi_a_awprot_o),
    .m_axi_a_axqos_o     (m_axi_a_awqos_o),

    .m_axi_b_axvalid_o   (m_axi_b_awvalid_o),
    .m_axi_b_axready_i   (m_axi_b_awready_i),
    .m_axi_b_axid_o      (m_axi_b_awid_o),
    .m_axi_b_axaddr_o    (m_axi_b_awaddr_o),
    .m_axi_b_axregion_o  (m_axi_b_awregion_o),
    .m_axi_b_axlen_o     (m_axi_b_awlen_o),
    .m_axi_b_axsize_o    (m_axi_b_awsize_o),
    .m_axi_b_axburst_o   (m_axi_b_awburst_o),
    .m_axi_b_axlock_o    (m_axi_b_awlock_o),
    .m_axi_b_axcache_o   (m_axi_b_awcache_o),
    .m_axi_b_axprot_o    (m_axi_b_awprot_o),
    .m_axi_b_axqos_o     (m_axi_b_awqos_o),

    .m_axi_c_axvalid_o   (m_axi_c_awvalid_o),
    .m_axi_c_axready_i   (m_axi_c_awready_i),
    .m_axi_c_axid_o      (m_axi_c_awid_o),
    .m_axi_c_axaddr_o    (m_axi_c_awaddr_o),
    .m_axi_c_axregion_o  (m_axi_c_awregion_o),
    .m_axi_c_axlen_o     (m_axi_c_awlen_o),
    .m_axi_c_axsize_o    (m_axi_c_awsize_o),
    .m_axi_c_axburst_o   (m_axi_c_awburst_o),
    .m_axi_c_axlock_o    (m_axi_c_awlock_o),
    .m_axi_c_axcache_o   (m_axi_c_awcache_o),
    .m_axi_c_axprot_o    (m_axi_c_awprot_o),
    .m_axi_c_axqos_o     (m_axi_c_awqos_o),

    .m_axi_a_fault_o     (m_axi_aw_a_fault),
    .m_axi_b_fault_o     (m_axi_aw_b_fault),
    .m_axi_c_fault_o     (m_axi_aw_c_fault),

    .m_axi_a_fault_i     (m_axi_a_fault),
    .m_axi_b_fault_i     (m_axi_b_fault),
    .m_axi_c_fault_i     (m_axi_c_fault),

    .m_axi_a_fault_clr_i (m_axi_a_fault_clr_i),
    .m_axi_b_fault_clr_i (m_axi_b_fault_clr_i),
    .m_axi_c_fault_clr_i (m_axi_c_fault_clr_i),

    .s_axi_axvalid_i     (s_axi_awvalid_i),
    .s_axi_axready_o     (s_axi_awready_o),
    .s_axi_axid_i        (s_axi_awid_i),
    .s_axi_axaddr_i      (s_axi_awaddr_i),
    .s_axi_axregion_i    (s_axi_awregion_i),
    .s_axi_axlen_i       (s_axi_awlen_i),
    .s_axi_axsize_i      (s_axi_awsize_i),
    .s_axi_axburst_i     (s_axi_awburst_i),
    .s_axi_axlock_i      (s_axi_awlock_i),
    .s_axi_axcache_i     (s_axi_awcache_i),
    .s_axi_axprot_i      (s_axi_awprot_i),
    .s_axi_axqos_i       (s_axi_awqos_i)
  );

  // ......................................................
  // AXI W channel
  el2_mubi_t m_axi_w_a_fault;
  el2_mubi_t m_axi_w_b_fault;
  el2_mubi_t m_axi_w_c_fault;

  el2_tmr_axi_s_ch_w # (
    .DataWidth (DataWidth)

  ) ch_w (

    .clk_i               (clk_i),
    .rst_ni              (rst_ni),

    .m_axi_a_wvalid_o    (m_axi_a_wvalid_o),
    .m_axi_a_wready_i    (m_axi_a_wready_i),
    .m_axi_a_wdata_o     (m_axi_a_wdata_o),
    .m_axi_a_wstrb_o     (m_axi_a_wstrb_o),
    .m_axi_a_wlast_o     (m_axi_a_wlast_o),

    .m_axi_b_wvalid_o    (m_axi_b_wvalid_o),
    .m_axi_b_wready_i    (m_axi_b_wready_i),
    .m_axi_b_wdata_o     (m_axi_b_wdata_o),
    .m_axi_b_wstrb_o     (m_axi_b_wstrb_o),
    .m_axi_b_wlast_o     (m_axi_b_wlast_o),

    .m_axi_c_wvalid_o    (m_axi_c_wvalid_o),
    .m_axi_c_wready_i    (m_axi_c_wready_i),
    .m_axi_c_wdata_o     (m_axi_c_wdata_o),
    .m_axi_c_wstrb_o     (m_axi_c_wstrb_o),
    .m_axi_c_wlast_o     (m_axi_c_wlast_o),

    .m_axi_a_fault_o     (m_axi_w_a_fault),
    .m_axi_b_fault_o     (m_axi_w_b_fault),
    .m_axi_c_fault_o     (m_axi_w_c_fault),

    .m_axi_a_fault_i     (m_axi_a_fault),
    .m_axi_b_fault_i     (m_axi_b_fault),
    .m_axi_c_fault_i     (m_axi_c_fault),

    .m_axi_a_fault_clr_i (m_axi_a_fault_clr_i),
    .m_axi_b_fault_clr_i (m_axi_b_fault_clr_i),
    .m_axi_c_fault_clr_i (m_axi_c_fault_clr_i),

    .s_axi_wvalid_i      (s_axi_wvalid_i),
    .s_axi_wready_o      (s_axi_wready_o),
    .s_axi_wdata_i       (s_axi_wdata_i),
    .s_axi_wstrb_i       (s_axi_wstrb_i),
    .s_axi_wlast_i       (s_axi_wlast_i)
  );

  // ......................................................
  // AXI B channel
  el2_mubi_t m_axi_b_a_fault;
  el2_mubi_t m_axi_b_b_fault;
  el2_mubi_t m_axi_b_c_fault;

  el2_tmr_axi_s_ch_b # (
    .IdWidth (IdWidth)

  ) ch_b (

    .clk_i               (clk_i),
    .rst_ni              (rst_ni),

    .m_axi_a_bvalid_i    (m_axi_a_bvalid_i),
    .m_axi_a_bready_o    (m_axi_a_bready_o),
    .m_axi_a_bresp_i     (m_axi_a_bresp_i),
    .m_axi_a_bid_i       (m_axi_a_bid_i),

    .m_axi_b_bvalid_i    (m_axi_b_bvalid_i),
    .m_axi_b_bready_o    (m_axi_b_bready_o),
    .m_axi_b_bresp_i     (m_axi_b_bresp_i),
    .m_axi_b_bid_i       (m_axi_b_bid_i),

    .m_axi_c_bvalid_i    (m_axi_c_bvalid_i),
    .m_axi_c_bready_o    (m_axi_c_bready_o),
    .m_axi_c_bresp_i     (m_axi_c_bresp_i),
    .m_axi_c_bid_i       (m_axi_c_bid_i),

    .m_axi_a_fault_o     (m_axi_b_a_fault),
    .m_axi_b_fault_o     (m_axi_b_b_fault),
    .m_axi_c_fault_o     (m_axi_b_c_fault),

    .m_axi_a_fault_i     (m_axi_a_fault),
    .m_axi_b_fault_i     (m_axi_b_fault),
    .m_axi_c_fault_i     (m_axi_c_fault),

    .m_axi_a_fault_clr_i (m_axi_a_fault_clr_i),
    .m_axi_b_fault_clr_i (m_axi_b_fault_clr_i),
    .m_axi_c_fault_clr_i (m_axi_c_fault_clr_i),

    .s_axi_bvalid_o      (s_axi_bvalid_o),
    .s_axi_bready_i      (s_axi_bready_i),
    .s_axi_bresp_o       (s_axi_bresp_o),
    .s_axi_bid_o         (s_axi_bid_o)
  );

  // ......................................................
  // AXI AR channel
  el2_mubi_t m_axi_ar_a_fault;
  el2_mubi_t m_axi_ar_b_fault;
  el2_mubi_t m_axi_ar_c_fault;

  el2_tmr_axi_s_ch_ax # (
    .AddrWidth (AddrWidth),
    .IdWidth   (IdWidth)

  ) ch_ar (

    .clk_i               (clk_i),
    .rst_ni              (rst_ni),

    .m_axi_a_axvalid_o   (m_axi_a_arvalid_o),
    .m_axi_a_axready_i   (m_axi_a_arready_i),
    .m_axi_a_axid_o      (m_axi_a_arid_o),
    .m_axi_a_axaddr_o    (m_axi_a_araddr_o),
    .m_axi_a_axregion_o  (m_axi_a_arregion_o),
    .m_axi_a_axlen_o     (m_axi_a_arlen_o),
    .m_axi_a_axsize_o    (m_axi_a_arsize_o),
    .m_axi_a_axburst_o   (m_axi_a_arburst_o),
    .m_axi_a_axlock_o    (m_axi_a_arlock_o),
    .m_axi_a_axcache_o   (m_axi_a_arcache_o),
    .m_axi_a_axprot_o    (m_axi_a_arprot_o),
    .m_axi_a_axqos_o     (m_axi_a_arqos_o),

    .m_axi_b_axvalid_o   (m_axi_b_arvalid_o),
    .m_axi_b_axready_i   (m_axi_b_arready_i),
    .m_axi_b_axid_o      (m_axi_b_arid_o),
    .m_axi_b_axaddr_o    (m_axi_b_araddr_o),
    .m_axi_b_axregion_o  (m_axi_b_arregion_o),
    .m_axi_b_axlen_o     (m_axi_b_arlen_o),
    .m_axi_b_axsize_o    (m_axi_b_arsize_o),
    .m_axi_b_axburst_o   (m_axi_b_arburst_o),
    .m_axi_b_axlock_o    (m_axi_b_arlock_o),
    .m_axi_b_axcache_o   (m_axi_b_arcache_o),
    .m_axi_b_axprot_o    (m_axi_b_arprot_o),
    .m_axi_b_axqos_o     (m_axi_b_arqos_o),

    .m_axi_c_axvalid_o   (m_axi_c_arvalid_o),
    .m_axi_c_axready_i   (m_axi_c_arready_i),
    .m_axi_c_axid_o      (m_axi_c_arid_o),
    .m_axi_c_axaddr_o    (m_axi_c_araddr_o),
    .m_axi_c_axregion_o  (m_axi_c_arregion_o),
    .m_axi_c_axlen_o     (m_axi_c_arlen_o),
    .m_axi_c_axsize_o    (m_axi_c_arsize_o),
    .m_axi_c_axburst_o   (m_axi_c_arburst_o),
    .m_axi_c_axlock_o    (m_axi_c_arlock_o),
    .m_axi_c_axcache_o   (m_axi_c_arcache_o),
    .m_axi_c_axprot_o    (m_axi_c_arprot_o),
    .m_axi_c_axqos_o     (m_axi_c_arqos_o),

    .m_axi_a_fault_o     (m_axi_ar_a_fault),
    .m_axi_b_fault_o     (m_axi_ar_b_fault),
    .m_axi_c_fault_o     (m_axi_ar_c_fault),

    .m_axi_a_fault_i     (m_axi_a_fault),
    .m_axi_b_fault_i     (m_axi_b_fault),
    .m_axi_c_fault_i     (m_axi_c_fault),

    .m_axi_a_fault_clr_i (m_axi_a_fault_clr_i),
    .m_axi_b_fault_clr_i (m_axi_b_fault_clr_i),
    .m_axi_c_fault_clr_i (m_axi_c_fault_clr_i),

    .s_axi_axvalid_i     (s_axi_arvalid_i),
    .s_axi_axready_o     (s_axi_arready_o),
    .s_axi_axid_i        (s_axi_arid_i),
    .s_axi_axaddr_i      (s_axi_araddr_i),
    .s_axi_axregion_i    (s_axi_arregion_i),
    .s_axi_axlen_i       (s_axi_arlen_i),
    .s_axi_axsize_i      (s_axi_arsize_i),
    .s_axi_axburst_i     (s_axi_arburst_i),
    .s_axi_axlock_i      (s_axi_arlock_i),
    .s_axi_axcache_i     (s_axi_arcache_i),
    .s_axi_axprot_i      (s_axi_arprot_i),
    .s_axi_axqos_i       (s_axi_arqos_i)
  );

  // ......................................................
  // AXI R channel
  el2_mubi_t m_axi_r_a_fault;
  el2_mubi_t m_axi_r_b_fault;
  el2_mubi_t m_axi_r_c_fault;

  el2_tmr_axi_s_ch_r # (
    .DataWidth (DataWidth),
    .IdWidth   (IdWidth)

  ) ch_r (

    .clk_i               (clk_i),
    .rst_ni              (rst_ni),

    .m_axi_a_rvalid_i    (m_axi_a_rvalid_i),
    .m_axi_a_rready_o    (m_axi_a_rready_o),
    .m_axi_a_rid_i       (m_axi_a_rid_i),
    .m_axi_a_rdata_i     (m_axi_a_rdata_i),
    .m_axi_a_rresp_i     (m_axi_a_rresp_i),
    .m_axi_a_rlast_i     (m_axi_a_rlast_i),

    .m_axi_b_rvalid_i    (m_axi_b_rvalid_i),
    .m_axi_b_rready_o    (m_axi_b_rready_o),
    .m_axi_b_rid_i       (m_axi_b_rid_i),
    .m_axi_b_rdata_i     (m_axi_b_rdata_i),
    .m_axi_b_rresp_i     (m_axi_b_rresp_i),
    .m_axi_b_rlast_i     (m_axi_b_rlast_i),

    .m_axi_c_rvalid_i    (m_axi_c_rvalid_i),
    .m_axi_c_rready_o    (m_axi_c_rready_o),
    .m_axi_c_rid_i       (m_axi_c_rid_i),
    .m_axi_c_rdata_i     (m_axi_c_rdata_i),
    .m_axi_c_rresp_i     (m_axi_c_rresp_i),
    .m_axi_c_rlast_i     (m_axi_c_rlast_i),

    .m_axi_a_fault_o     (m_axi_r_a_fault),
    .m_axi_b_fault_o     (m_axi_r_b_fault),
    .m_axi_c_fault_o     (m_axi_r_c_fault),

    .m_axi_a_fault_i     (m_axi_a_fault),
    .m_axi_b_fault_i     (m_axi_b_fault),
    .m_axi_c_fault_i     (m_axi_c_fault),

    .m_axi_a_fault_clr_i (m_axi_a_fault_clr_i),
    .m_axi_b_fault_clr_i (m_axi_b_fault_clr_i),
    .m_axi_c_fault_clr_i (m_axi_c_fault_clr_i),

    .s_axi_rvalid_o      (s_axi_rvalid_o),
    .s_axi_rready_i      (s_axi_rready_i),
    .s_axi_rid_o         (s_axi_rid_o),
    .s_axi_rdata_o       (s_axi_rdata_o),
    .s_axi_rresp_o       (s_axi_rresp_o),
    .s_axi_rlast_o       (s_axi_rlast_o)
  );

  // ......................................................
  // Fault aggregation and loopback

  el2_mubi_t m_axi_a_fault_l0;
  el2_mubi_t m_axi_a_fault_l1;
  el2_mubi_t m_axi_a_fault_l2;

  el2_mubi_t m_axi_b_fault_l0;
  el2_mubi_t m_axi_b_fault_l1;
  el2_mubi_t m_axi_b_fault_l2;

  el2_mubi_t m_axi_c_fault_l0;
  el2_mubi_t m_axi_c_fault_l1;
  el2_mubi_t m_axi_c_fault_l2;

  always_comb begin
    m_axi_a_fault_l0 = mubi_or(m_axi_aw_a_fault, m_axi_w_a_fault);
    m_axi_a_fault_l1 = mubi_or(m_axi_b_a_fault,  m_axi_ar_a_fault);
    m_axi_a_fault_l2 = mubi_or(m_axi_r_a_fault,  m_axi_a_fault_i);

    m_axi_a_fault    = mubi_or3(m_axi_a_fault_l0, m_axi_a_fault_l1, m_axi_a_fault_l2);
  end

  always_comb begin
    m_axi_b_fault_l0 = mubi_or(m_axi_aw_b_fault, m_axi_w_b_fault);
    m_axi_b_fault_l1 = mubi_or(m_axi_b_b_fault,  m_axi_ar_b_fault);
    m_axi_b_fault_l2 = mubi_or(m_axi_r_b_fault,  m_axi_b_fault_i);

    m_axi_b_fault    = mubi_or3(m_axi_b_fault_l0, m_axi_b_fault_l1, m_axi_b_fault_l2);
  end

  always_comb begin
    m_axi_c_fault_l0 = mubi_or(m_axi_aw_c_fault, m_axi_w_c_fault);
    m_axi_c_fault_l1 = mubi_or(m_axi_b_c_fault,  m_axi_ar_c_fault);
    m_axi_c_fault_l2 = mubi_or(m_axi_r_c_fault,  m_axi_c_fault_i);

    m_axi_c_fault    = mubi_or3(m_axi_c_fault_l0, m_axi_c_fault_l1, m_axi_c_fault_l2);
  end

  // ......................................................
  // Fault output

  always_comb begin
    m_axi_a_fault_o = m_axi_a_fault;
    m_axi_b_fault_o = m_axi_b_fault;
    m_axi_c_fault_o = m_axi_c_fault;
  end

endmodule
