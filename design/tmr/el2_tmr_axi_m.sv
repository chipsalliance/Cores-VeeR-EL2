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
  input  logic                     a_s_axi_awvalid_i,
  output logic                     a_s_axi_awready_o,
  input  logic [IdWidth-1:0]       a_s_axi_awid_i,
  input  logic [AddrWidth-1:0]     a_s_axi_awaddr_i,
  input  logic [3:0]               a_s_axi_awregion_i,
  input  logic [7:0]               a_s_axi_awlen_i,
  input  logic [2:0]               a_s_axi_awsize_i,
  input  logic [1:0]               a_s_axi_awburst_i,
  input  logic                     a_s_axi_awlock_i,
  input  logic [3:0]               a_s_axi_awcache_i,
  input  logic [2:0]               a_s_axi_awprot_i,
  input  logic [3:0]               a_s_axi_awqos_i,

  input  logic                     a_s_axi_wvalid_i,
  output logic                     a_s_axi_wready_o,
  input  logic [DataWidth-1:0]     a_s_axi_wdata_i,
  input  logic [DataWidth/8-1:0]   a_s_axi_wstrb_i,
  input  logic                     a_s_axi_wlast_i,

  output logic                     a_s_axi_bvalid_o,
  input  logic                     a_s_axi_bready_i,
  output logic [1:0]               a_s_axi_bresp_o,
  output logic [IdWidth-1:0]       a_s_axi_bid_o,

  input  logic                     a_s_axi_arvalid_i,
  output logic                     a_s_axi_arready_o,
  input  logic [IdWidth-1:0]       a_s_axi_arid_i,
  input  logic [AddrWidth-1:0]     a_s_axi_araddr_i,
  input  logic [3:0]               a_s_axi_arregion_i,
  input  logic [7:0]               a_s_axi_arlen_i,
  input  logic [2:0]               a_s_axi_arsize_i,
  input  logic [1:0]               a_s_axi_arburst_i,
  input  logic                     a_s_axi_arlock_i,
  input  logic [3:0]               a_s_axi_arcache_i,
  input  logic [2:0]               a_s_axi_arprot_i,
  input  logic [3:0]               a_s_axi_arqos_i,

  output logic                     a_s_axi_rvalid_o,
  input  logic                     a_s_axi_rready_i,
  output logic [IdWidth-1:0]       a_s_axi_rid_o,
  output logic [DataWidth-1:0]     a_s_axi_rdata_o,
  output logic [1:0]               a_s_axi_rresp_o,
  output logic                     a_s_axi_rlast_o,

  // AXI port for core A
  input  logic                     b_s_axi_awvalid_i,
  output logic                     b_s_axi_awready_o,
  input  logic [IdWidth-1:0]       b_s_axi_awid_i,
  input  logic [AddrWidth-1:0]     b_s_axi_awaddr_i,
  input  logic [3:0]               b_s_axi_awregion_i,
  input  logic [7:0]               b_s_axi_awlen_i,
  input  logic [2:0]               b_s_axi_awsize_i,
  input  logic [1:0]               b_s_axi_awburst_i,
  input  logic                     b_s_axi_awlock_i,
  input  logic [3:0]               b_s_axi_awcache_i,
  input  logic [2:0]               b_s_axi_awprot_i,
  input  logic [3:0]               b_s_axi_awqos_i,

  input  logic                     b_s_axi_wvalid_i,
  output logic                     b_s_axi_wready_o,
  input  logic [DataWidth-1:0]     b_s_axi_wdata_i,
  input  logic [DataWidth/8-1:0]   b_s_axi_wstrb_i,
  input  logic                     b_s_axi_wlast_i,

  output logic                     b_s_axi_bvalid_o,
  input  logic                     b_s_axi_bready_i,
  output logic [1:0]               b_s_axi_bresp_o,
  output logic [IdWidth-1:0]       b_s_axi_bid_o,

  input  logic                     b_s_axi_arvalid_i,
  output logic                     b_s_axi_arready_o,
  input  logic [IdWidth-1:0]       b_s_axi_arid_i,
  input  logic [AddrWidth-1:0]     b_s_axi_araddr_i,
  input  logic [3:0]               b_s_axi_arregion_i,
  input  logic [7:0]               b_s_axi_arlen_i,
  input  logic [2:0]               b_s_axi_arsize_i,
  input  logic [1:0]               b_s_axi_arburst_i,
  input  logic                     b_s_axi_arlock_i,
  input  logic [3:0]               b_s_axi_arcache_i,
  input  logic [2:0]               b_s_axi_arprot_i,
  input  logic [3:0]               b_s_axi_arqos_i,

  output logic                     b_s_axi_rvalid_o,
  input  logic                     b_s_axi_rready_i,
  output logic [IdWidth-1:0]       b_s_axi_rid_o,
  output logic [DataWidth-1:0]     b_s_axi_rdata_o,
  output logic [1:0]               b_s_axi_rresp_o,
  output logic                     b_s_axi_rlast_o,

  // AXI port for core C
  input  logic                     c_s_axi_awvalid_i,
  output logic                     c_s_axi_awready_o,
  input  logic [IdWidth-1:0]       c_s_axi_awid_i,
  input  logic [AddrWidth-1:0]     c_s_axi_awaddr_i,
  input  logic [3:0]               c_s_axi_awregion_i,
  input  logic [7:0]               c_s_axi_awlen_i,
  input  logic [2:0]               c_s_axi_awsize_i,
  input  logic [1:0]               c_s_axi_awburst_i,
  input  logic                     c_s_axi_awlock_i,
  input  logic [3:0]               c_s_axi_awcache_i,
  input  logic [2:0]               c_s_axi_awprot_i,
  input  logic [3:0]               c_s_axi_awqos_i,

  input  logic                     c_s_axi_wvalid_i,
  output logic                     c_s_axi_wready_o,
  input  logic [DataWidth-1:0]     c_s_axi_wdata_i,
  input  logic [DataWidth/8-1:0]   c_s_axi_wstrb_i,
  input  logic                     c_s_axi_wlast_i,

  output logic                     c_s_axi_bvalid_o,
  input  logic                     c_s_axi_bready_i,
  output logic [1:0]               c_s_axi_bresp_o,
  output logic [IdWidth-1:0]       c_s_axi_bid_o,

  input  logic                     c_s_axi_arvalid_i,
  output logic                     c_s_axi_arready_o,
  input  logic [IdWidth-1:0]       c_s_axi_arid_i,
  input  logic [AddrWidth-1:0]     c_s_axi_araddr_i,
  input  logic [3:0]               c_s_axi_arregion_i,
  input  logic [7:0]               c_s_axi_arlen_i,
  input  logic [2:0]               c_s_axi_arsize_i,
  input  logic [1:0]               c_s_axi_arburst_i,
  input  logic                     c_s_axi_arlock_i,
  input  logic [3:0]               c_s_axi_arcache_i,
  input  logic [2:0]               c_s_axi_arprot_i,
  input  logic [3:0]               c_s_axi_arqos_i,

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

  el2_mubi_t a_s_axi_fault;
  el2_mubi_t b_s_axi_fault;
  el2_mubi_t c_s_axi_fault;

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

    .a_s_axi_axvalid_i   (a_s_axi_awvalid_i),
    .a_s_axi_axready_o   (a_s_axi_awready_o),
    .a_s_axi_axid_i      (a_s_axi_awid_i),
    .a_s_axi_axaddr_i    (a_s_axi_awaddr_i),
    .a_s_axi_axregion_i  (a_s_axi_awregion_i),
    .a_s_axi_axlen_i     (a_s_axi_awlen_i),
    .a_s_axi_axsize_i    (a_s_axi_awsize_i),
    .a_s_axi_axburst_i   (a_s_axi_awburst_i),
    .a_s_axi_axlock_i    (a_s_axi_awlock_i),
    .a_s_axi_axcache_i   (a_s_axi_awcache_i),
    .a_s_axi_axprot_i    (a_s_axi_awprot_i),
    .a_s_axi_axqos_i     (a_s_axi_awqos_i),

    .b_s_axi_axvalid_i   (b_s_axi_awvalid_i),
    .b_s_axi_axready_o   (b_s_axi_awready_o),
    .b_s_axi_axid_i      (b_s_axi_awid_i),
    .b_s_axi_axaddr_i    (b_s_axi_awaddr_i),
    .b_s_axi_axregion_i  (b_s_axi_awregion_i),
    .b_s_axi_axlen_i     (b_s_axi_awlen_i),
    .b_s_axi_axsize_i    (b_s_axi_awsize_i),
    .b_s_axi_axburst_i   (b_s_axi_awburst_i),
    .b_s_axi_axlock_i    (b_s_axi_awlock_i),
    .b_s_axi_axcache_i   (b_s_axi_awcache_i),
    .b_s_axi_axprot_i    (b_s_axi_awprot_i),
    .b_s_axi_axqos_i     (b_s_axi_awqos_i),

    .c_s_axi_axvalid_i   (c_s_axi_awvalid_i),
    .c_s_axi_axready_o   (c_s_axi_awready_o),
    .c_s_axi_axid_i      (c_s_axi_awid_i),
    .c_s_axi_axaddr_i    (c_s_axi_awaddr_i),
    .c_s_axi_axregion_i  (c_s_axi_awregion_i),
    .c_s_axi_axlen_i     (c_s_axi_awlen_i),
    .c_s_axi_axsize_i    (c_s_axi_awsize_i),
    .c_s_axi_axburst_i   (c_s_axi_awburst_i),
    .c_s_axi_axlock_i    (c_s_axi_awlock_i),
    .c_s_axi_axcache_i   (c_s_axi_awcache_i),
    .c_s_axi_axprot_i    (c_s_axi_awprot_i),
    .c_s_axi_axqos_i     (c_s_axi_awqos_i),

    .a_s_axi_fault_o     (s_axi_aw_a_fault),
    .b_s_axi_fault_o     (s_axi_aw_b_fault),
    .c_s_axi_fault_o     (s_axi_aw_c_fault),

    .a_s_axi_fault_i     (a_s_axi_fault),
    .b_s_axi_fault_i     (b_s_axi_fault),
    .c_s_axi_fault_i     (c_s_axi_fault),

    .a_s_axi_fault_clr_i (a_s_axi_fault_clr_i),
    .b_s_axi_fault_clr_i (b_s_axi_fault_clr_i),
    .c_s_axi_fault_clr_i (c_s_axi_fault_clr_i),

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

    .a_s_axi_wvalid_i    (a_s_axi_wvalid_i),
    .a_s_axi_wready_o    (a_s_axi_wready_o),
    .a_s_axi_wdata_i     (a_s_axi_wdata_i),
    .a_s_axi_wstrb_i     (a_s_axi_wstrb_i),
    .a_s_axi_wlast_i     (a_s_axi_wlast_i),

    .b_s_axi_wvalid_i    (b_s_axi_wvalid_i),
    .b_s_axi_wready_o    (b_s_axi_wready_o),
    .b_s_axi_wdata_i     (b_s_axi_wdata_i),
    .b_s_axi_wstrb_i     (b_s_axi_wstrb_i),
    .b_s_axi_wlast_i     (b_s_axi_wlast_i),

    .c_s_axi_wvalid_i    (c_s_axi_wvalid_i),
    .c_s_axi_wready_o    (c_s_axi_wready_o),
    .c_s_axi_wdata_i     (c_s_axi_wdata_i),
    .c_s_axi_wstrb_i     (c_s_axi_wstrb_i),
    .c_s_axi_wlast_i     (c_s_axi_wlast_i),

    .a_s_axi_fault_o     (s_axi_w_a_fault),
    .b_s_axi_fault_o     (s_axi_w_b_fault),
    .c_s_axi_fault_o     (s_axi_w_c_fault),

    .a_s_axi_fault_i     (a_s_axi_fault),
    .b_s_axi_fault_i     (b_s_axi_fault),
    .c_s_axi_fault_i     (c_s_axi_fault),

    .a_s_axi_fault_clr_i (a_s_axi_fault_clr_i),
    .b_s_axi_fault_clr_i (b_s_axi_fault_clr_i),
    .c_s_axi_fault_clr_i (c_s_axi_fault_clr_i),

    .m_axi_wvalid_o      (m_axi_wvalid_o),
    .m_axi_wready_i      (m_axi_wready_i),
    .m_axi_wdata_o       (m_axi_wdata_o),
    .m_axi_wstrb_o       (m_axi_wstrb_o),
    .m_axi_wlast_o       (m_axi_wlast_o)
  );

  // ......................................................
  // AXI B channel
  el2_mubi_t b_s_axi_a_fault;
  el2_mubi_t b_s_axi_b_fault;
  el2_mubi_t b_c_s_axi_fault;

  el2_tmr_axi_m_ch_b # (
    .IdWidth (IdWidth)

  ) ch_b (

    .clk_i               (clk_i),
    .rst_ni              (rst_ni),

    .a_s_axi_bvalid_o    (a_s_axi_bvalid_o),
    .a_s_axi_bready_i    (a_s_axi_bready_i),
    .a_s_axi_bresp_o     (a_s_axi_bresp_o),
    .a_s_axi_bid_o       (a_s_axi_bid_o),

    .b_s_axi_bvalid_o    (b_s_axi_bvalid_o),
    .b_s_axi_bready_i    (b_s_axi_bready_i),
    .b_s_axi_bresp_o     (b_s_axi_bresp_o),
    .b_s_axi_bid_o       (b_s_axi_bid_o),

    .c_s_axi_bvalid_o    (c_s_axi_bvalid_o),
    .c_s_axi_bready_i    (c_s_axi_bready_i),
    .c_s_axi_bresp_o     (c_s_axi_bresp_o),
    .c_s_axi_bid_o       (c_s_axi_bid_o),

    .a_s_axi_fault_o     (b_s_axi_a_fault),
    .b_s_axi_fault_o     (b_s_axi_b_fault),
    .c_s_axi_fault_o     (b_c_s_axi_fault),

    .a_s_axi_fault_i     (a_s_axi_fault),
    .b_s_axi_fault_i     (b_s_axi_fault),
    .c_s_axi_fault_i     (c_s_axi_fault),

    .a_s_axi_fault_clr_i (a_s_axi_fault_clr_i),
    .b_s_axi_fault_clr_i (b_s_axi_fault_clr_i),
    .c_s_axi_fault_clr_i (c_s_axi_fault_clr_i),

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

    .a_s_axi_axvalid_i   (a_s_axi_arvalid_i),
    .a_s_axi_axready_o   (a_s_axi_arready_o),
    .a_s_axi_axid_i      (a_s_axi_arid_i),
    .a_s_axi_axaddr_i    (a_s_axi_araddr_i),
    .a_s_axi_axregion_i  (a_s_axi_arregion_i),
    .a_s_axi_axlen_i     (a_s_axi_arlen_i),
    .a_s_axi_axsize_i    (a_s_axi_arsize_i),
    .a_s_axi_axburst_i   (a_s_axi_arburst_i),
    .a_s_axi_axlock_i    (a_s_axi_arlock_i),
    .a_s_axi_axcache_i   (a_s_axi_arcache_i),
    .a_s_axi_axprot_i    (a_s_axi_arprot_i),
    .a_s_axi_axqos_i     (a_s_axi_arqos_i),

    .b_s_axi_axvalid_i   (b_s_axi_arvalid_i),
    .b_s_axi_axready_o   (b_s_axi_arready_o),
    .b_s_axi_axid_i      (b_s_axi_arid_i),
    .b_s_axi_axaddr_i    (b_s_axi_araddr_i),
    .b_s_axi_axregion_i  (b_s_axi_arregion_i),
    .b_s_axi_axlen_i     (b_s_axi_arlen_i),
    .b_s_axi_axsize_i    (b_s_axi_arsize_i),
    .b_s_axi_axburst_i   (b_s_axi_arburst_i),
    .b_s_axi_axlock_i    (b_s_axi_arlock_i),
    .b_s_axi_axcache_i   (b_s_axi_arcache_i),
    .b_s_axi_axprot_i    (b_s_axi_arprot_i),
    .b_s_axi_axqos_i     (b_s_axi_arqos_i),

    .c_s_axi_axvalid_i   (c_s_axi_arvalid_i),
    .c_s_axi_axready_o   (c_s_axi_arready_o),
    .c_s_axi_axid_i      (c_s_axi_arid_i),
    .c_s_axi_axaddr_i    (c_s_axi_araddr_i),
    .c_s_axi_axregion_i  (c_s_axi_arregion_i),
    .c_s_axi_axlen_i     (c_s_axi_arlen_i),
    .c_s_axi_axsize_i    (c_s_axi_arsize_i),
    .c_s_axi_axburst_i   (c_s_axi_arburst_i),
    .c_s_axi_axlock_i    (c_s_axi_arlock_i),
    .c_s_axi_axcache_i   (c_s_axi_arcache_i),
    .c_s_axi_axprot_i    (c_s_axi_arprot_i),
    .c_s_axi_axqos_i     (c_s_axi_arqos_i),

    .a_s_axi_fault_o     (s_axi_ar_a_fault),
    .b_s_axi_fault_o     (s_axi_ar_b_fault),
    .c_s_axi_fault_o     (s_axi_ar_c_fault),

    .a_s_axi_fault_i     (a_s_axi_fault),
    .b_s_axi_fault_i     (b_s_axi_fault),
    .c_s_axi_fault_i     (c_s_axi_fault),

    .a_s_axi_fault_clr_i (a_s_axi_fault_clr_i),
    .b_s_axi_fault_clr_i (b_s_axi_fault_clr_i),
    .c_s_axi_fault_clr_i (c_s_axi_fault_clr_i),

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

    .a_s_axi_rvalid_o    (a_s_axi_rvalid_o),
    .a_s_axi_rready_i    (a_s_axi_rready_i),
    .a_s_axi_rid_o       (a_s_axi_rid_o),
    .a_s_axi_rdata_o     (a_s_axi_rdata_o),
    .a_s_axi_rresp_o     (a_s_axi_rresp_o),
    .a_s_axi_rlast_o     (a_s_axi_rlast_o),

    .b_s_axi_rvalid_o    (b_s_axi_rvalid_o),
    .b_s_axi_rready_i    (b_s_axi_rready_i),
    .b_s_axi_rid_o       (b_s_axi_rid_o),
    .b_s_axi_rdata_o     (b_s_axi_rdata_o),
    .b_s_axi_rresp_o     (b_s_axi_rresp_o),
    .b_s_axi_rlast_o     (b_s_axi_rlast_o),

    .c_s_axi_rvalid_o    (c_s_axi_rvalid_o),
    .c_s_axi_rready_i    (c_s_axi_rready_i),
    .c_s_axi_rid_o       (c_s_axi_rid_o),
    .c_s_axi_rdata_o     (c_s_axi_rdata_o),
    .c_s_axi_rresp_o     (c_s_axi_rresp_o),
    .c_s_axi_rlast_o     (c_s_axi_rlast_o),

    .a_s_axi_fault_o     (s_axi_r_a_fault),
    .b_s_axi_fault_o     (s_axi_r_b_fault),
    .c_s_axi_fault_o     (s_axi_r_c_fault),

    .a_s_axi_fault_i     (a_s_axi_fault),
    .b_s_axi_fault_i     (b_s_axi_fault),
    .c_s_axi_fault_i     (c_s_axi_fault),

    .a_s_axi_fault_clr_i (a_s_axi_fault_clr_i),
    .b_s_axi_fault_clr_i (b_s_axi_fault_clr_i),
    .c_s_axi_fault_clr_i (c_s_axi_fault_clr_i),

    .m_axi_rvalid_i      (m_axi_rvalid_i),
    .m_axi_rready_o      (m_axi_rready_o),
    .m_axi_rid_i         (m_axi_rid_i),
    .m_axi_rdata_i       (m_axi_rdata_i),
    .m_axi_rresp_i       (m_axi_rresp_i),
    .m_axi_rlast_i       (m_axi_rlast_i)
  );

  // ......................................................
  // Fault aggregation and loopback

  el2_mubi_t a_s_axi_fault_l0;
  el2_mubi_t a_s_axi_fault_l1;
  el2_mubi_t a_s_axi_fault_l2;

  el2_mubi_t b_s_axi_fault_l0;
  el2_mubi_t b_s_axi_fault_l1;
  el2_mubi_t b_s_axi_fault_l2;

  el2_mubi_t c_s_axi_fault_l0;
  el2_mubi_t c_s_axi_fault_l1;
  el2_mubi_t c_s_axi_fault_l2;

  always_comb begin
    a_s_axi_fault_l0 = mubi_or(s_axi_aw_a_fault, s_axi_w_a_fault);
    a_s_axi_fault_l1 = mubi_or(b_s_axi_a_fault,  s_axi_ar_a_fault);
    a_s_axi_fault_l2 = mubi_or(s_axi_r_a_fault,  a_s_axi_fault_i);

    a_s_axi_fault    = mubi_or3(a_s_axi_fault_l0, a_s_axi_fault_l1, a_s_axi_fault_l2);
  end

  always_comb begin
    b_s_axi_fault_l0 = mubi_or(s_axi_aw_b_fault, s_axi_w_b_fault);
    b_s_axi_fault_l1 = mubi_or(b_s_axi_b_fault,  s_axi_ar_b_fault);
    b_s_axi_fault_l2 = mubi_or(s_axi_r_b_fault,  b_s_axi_fault_i);

    b_s_axi_fault    = mubi_or3(b_s_axi_fault_l0, b_s_axi_fault_l1, b_s_axi_fault_l2);
  end

  always_comb begin
    c_s_axi_fault_l0 = mubi_or(s_axi_aw_c_fault, s_axi_w_c_fault);
    c_s_axi_fault_l1 = mubi_or(b_c_s_axi_fault,  s_axi_ar_c_fault);
    c_s_axi_fault_l2 = mubi_or(s_axi_r_c_fault,  c_s_axi_fault_i);

    c_s_axi_fault    = mubi_or3(c_s_axi_fault_l0, c_s_axi_fault_l1, c_s_axi_fault_l2);
  end

  // ......................................................
  // Fault output

  always_comb begin
    a_s_axi_fault_o = a_s_axi_fault;
    b_s_axi_fault_o = b_s_axi_fault;
    c_s_axi_fault_o = c_s_axi_fault;
  end

endmodule
