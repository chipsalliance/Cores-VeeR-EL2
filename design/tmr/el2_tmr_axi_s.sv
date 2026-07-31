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
  output logic                     a_m_axi_awvalid_o,
  input  logic                     a_m_axi_awready_i,
  output logic [IdWidth-1:0]       a_m_axi_awid_o,
  output logic [AddrWidth-1:0]     a_m_axi_awaddr_o,
  output logic [3:0]               a_m_axi_awregion_o,
  output logic [7:0]               a_m_axi_awlen_o,
  output logic [2:0]               a_m_axi_awsize_o,
  output logic [1:0]               a_m_axi_awburst_o,
  output logic                     a_m_axi_awlock_o,
  output logic [3:0]               a_m_axi_awcache_o,
  output logic [2:0]               a_m_axi_awprot_o,
  output logic [3:0]               a_m_axi_awqos_o,

  output logic                     a_m_axi_wvalid_o,
  input  logic                     a_m_axi_wready_i,
  output logic [DataWidth-1:0]     a_m_axi_wdata_o,
  output logic [DataWidth/8-1:0]   a_m_axi_wstrb_o,
  output logic                     a_m_axi_wlast_o,

  input  logic                     a_m_axi_bvalid_i,
  output logic                     a_m_axi_bready_o,
  input  logic [1:0]               a_m_axi_bresp_i,
  input  logic [IdWidth-1:0]       a_m_axi_bid_i,

  output logic                     a_m_axi_arvalid_o,
  input  logic                     a_m_axi_arready_i,
  output logic [IdWidth-1:0]       a_m_axi_arid_o,
  output logic [AddrWidth-1:0]     a_m_axi_araddr_o,
  output logic [3:0]               a_m_axi_arregion_o,
  output logic [7:0]               a_m_axi_arlen_o,
  output logic [2:0]               a_m_axi_arsize_o,
  output logic [1:0]               a_m_axi_arburst_o,
  output logic                     a_m_axi_arlock_o,
  output logic [3:0]               a_m_axi_arcache_o,
  output logic [2:0]               a_m_axi_arprot_o,
  output logic [3:0]               a_m_axi_arqos_o,

  input  logic                     a_m_axi_rvalid_i,
  output logic                     a_m_axi_rready_o,
  input  logic [IdWidth-1:0]       a_m_axi_rid_i,
  input  logic [DataWidth-1:0]     a_m_axi_rdata_i,
  input  logic [1:0]               a_m_axi_rresp_i,
  input  logic                     a_m_axi_rlast_i,

  // AXI port for core A
  output logic                     b_m_axi_awvalid_o,
  input  logic                     b_m_axi_awready_i,
  output logic [IdWidth-1:0]       b_m_axi_awid_o,
  output logic [AddrWidth-1:0]     b_m_axi_awaddr_o,
  output logic [3:0]               b_m_axi_awregion_o,
  output logic [7:0]               b_m_axi_awlen_o,
  output logic [2:0]               b_m_axi_awsize_o,
  output logic [1:0]               b_m_axi_awburst_o,
  output logic                     b_m_axi_awlock_o,
  output logic [3:0]               b_m_axi_awcache_o,
  output logic [2:0]               b_m_axi_awprot_o,
  output logic [3:0]               b_m_axi_awqos_o,

  output logic                     b_m_axi_wvalid_o,
  input  logic                     b_m_axi_wready_i,
  output logic [DataWidth-1:0]     b_m_axi_wdata_o,
  output logic [DataWidth/8-1:0]   b_m_axi_wstrb_o,
  output logic                     b_m_axi_wlast_o,

  input  logic                     b_m_axi_bvalid_i,
  output logic                     b_m_axi_bready_o,
  input  logic [1:0]               b_m_axi_bresp_i,
  input  logic [IdWidth-1:0]       b_m_axi_bid_i,

  output logic                     b_m_axi_arvalid_o,
  input  logic                     b_m_axi_arready_i,
  output logic [IdWidth-1:0]       b_m_axi_arid_o,
  output logic [AddrWidth-1:0]     b_m_axi_araddr_o,
  output logic [3:0]               b_m_axi_arregion_o,
  output logic [7:0]               b_m_axi_arlen_o,
  output logic [2:0]               b_m_axi_arsize_o,
  output logic [1:0]               b_m_axi_arburst_o,
  output logic                     b_m_axi_arlock_o,
  output logic [3:0]               b_m_axi_arcache_o,
  output logic [2:0]               b_m_axi_arprot_o,
  output logic [3:0]               b_m_axi_arqos_o,

  input  logic                     b_m_axi_rvalid_i,
  output logic                     b_m_axi_rready_o,
  input  logic [IdWidth-1:0]       b_m_axi_rid_i,
  input  logic [DataWidth-1:0]     b_m_axi_rdata_i,
  input  logic [1:0]               b_m_axi_rresp_i,
  input  logic                     b_m_axi_rlast_i,

  // AXI port for core C
  output logic                     c_m_axi_awvalid_o,
  input  logic                     c_m_axi_awready_i,
  output logic [IdWidth-1:0]       c_m_axi_awid_o,
  output logic [AddrWidth-1:0]     c_m_axi_awaddr_o,
  output logic [3:0]               c_m_axi_awregion_o,
  output logic [7:0]               c_m_axi_awlen_o,
  output logic [2:0]               c_m_axi_awsize_o,
  output logic [1:0]               c_m_axi_awburst_o,
  output logic                     c_m_axi_awlock_o,
  output logic [3:0]               c_m_axi_awcache_o,
  output logic [2:0]               c_m_axi_awprot_o,
  output logic [3:0]               c_m_axi_awqos_o,

  output logic                     c_m_axi_wvalid_o,
  input  logic                     c_m_axi_wready_i,
  output logic [DataWidth-1:0]     c_m_axi_wdata_o,
  output logic [DataWidth/8-1:0]   c_m_axi_wstrb_o,
  output logic                     c_m_axi_wlast_o,

  input  logic                     c_m_axi_bvalid_i,
  output logic                     c_m_axi_bready_o,
  input  logic [1:0]               c_m_axi_bresp_i,
  input  logic [IdWidth-1:0]       c_m_axi_bid_i,

  output logic                     c_m_axi_arvalid_o,
  input  logic                     c_m_axi_arready_i,
  output logic [IdWidth-1:0]       c_m_axi_arid_o,
  output logic [AddrWidth-1:0]     c_m_axi_araddr_o,
  output logic [3:0]               c_m_axi_arregion_o,
  output logic [7:0]               c_m_axi_arlen_o,
  output logic [2:0]               c_m_axi_arsize_o,
  output logic [1:0]               c_m_axi_arburst_o,
  output logic                     c_m_axi_arlock_o,
  output logic [3:0]               c_m_axi_arcache_o,
  output logic [2:0]               c_m_axi_arprot_o,
  output logic [3:0]               c_m_axi_arqos_o,

  input  logic                     c_m_axi_rvalid_i,
  output logic                     c_m_axi_rready_o,
  input  logic [IdWidth-1:0]       c_m_axi_rid_i,
  input  logic [DataWidth-1:0]     c_m_axi_rdata_i,
  input  logic [1:0]               c_m_axi_rresp_i,
  input  logic                     c_m_axi_rlast_i,

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

  el2_mubi_t a_m_axi_fault;
  el2_mubi_t b_m_axi_fault;
  el2_mubi_t c_m_axi_fault;

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

    .a_m_axi_axvalid_o   (a_m_axi_awvalid_o),
    .a_m_axi_axready_i   (a_m_axi_awready_i),
    .a_m_axi_axid_o      (a_m_axi_awid_o),
    .a_m_axi_axaddr_o    (a_m_axi_awaddr_o),
    .a_m_axi_axregion_o  (a_m_axi_awregion_o),
    .a_m_axi_axlen_o     (a_m_axi_awlen_o),
    .a_m_axi_axsize_o    (a_m_axi_awsize_o),
    .a_m_axi_axburst_o   (a_m_axi_awburst_o),
    .a_m_axi_axlock_o    (a_m_axi_awlock_o),
    .a_m_axi_axcache_o   (a_m_axi_awcache_o),
    .a_m_axi_axprot_o    (a_m_axi_awprot_o),
    .a_m_axi_axqos_o     (a_m_axi_awqos_o),

    .b_m_axi_axvalid_o   (b_m_axi_awvalid_o),
    .b_m_axi_axready_i   (b_m_axi_awready_i),
    .b_m_axi_axid_o      (b_m_axi_awid_o),
    .b_m_axi_axaddr_o    (b_m_axi_awaddr_o),
    .b_m_axi_axregion_o  (b_m_axi_awregion_o),
    .b_m_axi_axlen_o     (b_m_axi_awlen_o),
    .b_m_axi_axsize_o    (b_m_axi_awsize_o),
    .b_m_axi_axburst_o   (b_m_axi_awburst_o),
    .b_m_axi_axlock_o    (b_m_axi_awlock_o),
    .b_m_axi_axcache_o   (b_m_axi_awcache_o),
    .b_m_axi_axprot_o    (b_m_axi_awprot_o),
    .b_m_axi_axqos_o     (b_m_axi_awqos_o),

    .c_m_axi_axvalid_o   (c_m_axi_awvalid_o),
    .c_m_axi_axready_i   (c_m_axi_awready_i),
    .c_m_axi_axid_o      (c_m_axi_awid_o),
    .c_m_axi_axaddr_o    (c_m_axi_awaddr_o),
    .c_m_axi_axregion_o  (c_m_axi_awregion_o),
    .c_m_axi_axlen_o     (c_m_axi_awlen_o),
    .c_m_axi_axsize_o    (c_m_axi_awsize_o),
    .c_m_axi_axburst_o   (c_m_axi_awburst_o),
    .c_m_axi_axlock_o    (c_m_axi_awlock_o),
    .c_m_axi_axcache_o   (c_m_axi_awcache_o),
    .c_m_axi_axprot_o    (c_m_axi_awprot_o),
    .c_m_axi_axqos_o     (c_m_axi_awqos_o),

    .a_m_axi_fault_o     (m_axi_aw_a_fault),
    .b_m_axi_fault_o     (m_axi_aw_b_fault),
    .c_m_axi_fault_o     (m_axi_aw_c_fault),

    .a_m_axi_fault_i     (a_m_axi_fault),
    .b_m_axi_fault_i     (b_m_axi_fault),
    .c_m_axi_fault_i     (c_m_axi_fault),

    .a_m_axi_fault_clr_i (a_m_axi_fault_clr_i),
    .b_m_axi_fault_clr_i (b_m_axi_fault_clr_i),
    .c_m_axi_fault_clr_i (c_m_axi_fault_clr_i),

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

    .a_m_axi_wvalid_o    (a_m_axi_wvalid_o),
    .a_m_axi_wready_i    (a_m_axi_wready_i),
    .a_m_axi_wdata_o     (a_m_axi_wdata_o),
    .a_m_axi_wstrb_o     (a_m_axi_wstrb_o),
    .a_m_axi_wlast_o     (a_m_axi_wlast_o),

    .b_m_axi_wvalid_o    (b_m_axi_wvalid_o),
    .b_m_axi_wready_i    (b_m_axi_wready_i),
    .b_m_axi_wdata_o     (b_m_axi_wdata_o),
    .b_m_axi_wstrb_o     (b_m_axi_wstrb_o),
    .b_m_axi_wlast_o     (b_m_axi_wlast_o),

    .c_m_axi_wvalid_o    (c_m_axi_wvalid_o),
    .c_m_axi_wready_i    (c_m_axi_wready_i),
    .c_m_axi_wdata_o     (c_m_axi_wdata_o),
    .c_m_axi_wstrb_o     (c_m_axi_wstrb_o),
    .c_m_axi_wlast_o     (c_m_axi_wlast_o),

    .a_m_axi_fault_o     (m_axi_w_a_fault),
    .b_m_axi_fault_o     (m_axi_w_b_fault),
    .c_m_axi_fault_o     (m_axi_w_c_fault),

    .a_m_axi_fault_i     (a_m_axi_fault),
    .b_m_axi_fault_i     (b_m_axi_fault),
    .c_m_axi_fault_i     (c_m_axi_fault),

    .a_m_axi_fault_clr_i (a_m_axi_fault_clr_i),
    .b_m_axi_fault_clr_i (b_m_axi_fault_clr_i),
    .c_m_axi_fault_clr_i (c_m_axi_fault_clr_i),

    .s_axi_wvalid_i      (s_axi_wvalid_i),
    .s_axi_wready_o      (s_axi_wready_o),
    .s_axi_wdata_i       (s_axi_wdata_i),
    .s_axi_wstrb_i       (s_axi_wstrb_i),
    .s_axi_wlast_i       (s_axi_wlast_i)
  );

  // ......................................................
  // AXI B channel
  el2_mubi_t b_a_m_axi_fault;
  el2_mubi_t b_m_axi_b_fault;
  el2_mubi_t b_m_axi_c_fault;

  el2_tmr_axi_s_ch_b # (
    .IdWidth (IdWidth)

  ) ch_b (

    .clk_i               (clk_i),
    .rst_ni              (rst_ni),

    .a_m_axi_bvalid_i    (a_m_axi_bvalid_i),
    .a_m_axi_bready_o    (a_m_axi_bready_o),
    .a_m_axi_bresp_i     (a_m_axi_bresp_i),
    .a_m_axi_bid_i       (a_m_axi_bid_i),

    .b_m_axi_bvalid_i    (b_m_axi_bvalid_i),
    .b_m_axi_bready_o    (b_m_axi_bready_o),
    .b_m_axi_bresp_i     (b_m_axi_bresp_i),
    .b_m_axi_bid_i       (b_m_axi_bid_i),

    .c_m_axi_bvalid_i    (c_m_axi_bvalid_i),
    .c_m_axi_bready_o    (c_m_axi_bready_o),
    .c_m_axi_bresp_i     (c_m_axi_bresp_i),
    .c_m_axi_bid_i       (c_m_axi_bid_i),

    .a_m_axi_fault_o     (b_a_m_axi_fault),
    .b_m_axi_fault_o     (b_m_axi_b_fault),
    .c_m_axi_fault_o     (b_m_axi_c_fault),

    .a_m_axi_fault_i     (a_m_axi_fault),
    .b_m_axi_fault_i     (b_m_axi_fault),
    .c_m_axi_fault_i     (c_m_axi_fault),

    .a_m_axi_fault_clr_i (a_m_axi_fault_clr_i),
    .b_m_axi_fault_clr_i (b_m_axi_fault_clr_i),
    .c_m_axi_fault_clr_i (c_m_axi_fault_clr_i),

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

    .a_m_axi_axvalid_o   (a_m_axi_arvalid_o),
    .a_m_axi_axready_i   (a_m_axi_arready_i),
    .a_m_axi_axid_o      (a_m_axi_arid_o),
    .a_m_axi_axaddr_o    (a_m_axi_araddr_o),
    .a_m_axi_axregion_o  (a_m_axi_arregion_o),
    .a_m_axi_axlen_o     (a_m_axi_arlen_o),
    .a_m_axi_axsize_o    (a_m_axi_arsize_o),
    .a_m_axi_axburst_o   (a_m_axi_arburst_o),
    .a_m_axi_axlock_o    (a_m_axi_arlock_o),
    .a_m_axi_axcache_o   (a_m_axi_arcache_o),
    .a_m_axi_axprot_o    (a_m_axi_arprot_o),
    .a_m_axi_axqos_o     (a_m_axi_arqos_o),

    .b_m_axi_axvalid_o   (b_m_axi_arvalid_o),
    .b_m_axi_axready_i   (b_m_axi_arready_i),
    .b_m_axi_axid_o      (b_m_axi_arid_o),
    .b_m_axi_axaddr_o    (b_m_axi_araddr_o),
    .b_m_axi_axregion_o  (b_m_axi_arregion_o),
    .b_m_axi_axlen_o     (b_m_axi_arlen_o),
    .b_m_axi_axsize_o    (b_m_axi_arsize_o),
    .b_m_axi_axburst_o   (b_m_axi_arburst_o),
    .b_m_axi_axlock_o    (b_m_axi_arlock_o),
    .b_m_axi_axcache_o   (b_m_axi_arcache_o),
    .b_m_axi_axprot_o    (b_m_axi_arprot_o),
    .b_m_axi_axqos_o     (b_m_axi_arqos_o),

    .c_m_axi_axvalid_o   (c_m_axi_arvalid_o),
    .c_m_axi_axready_i   (c_m_axi_arready_i),
    .c_m_axi_axid_o      (c_m_axi_arid_o),
    .c_m_axi_axaddr_o    (c_m_axi_araddr_o),
    .c_m_axi_axregion_o  (c_m_axi_arregion_o),
    .c_m_axi_axlen_o     (c_m_axi_arlen_o),
    .c_m_axi_axsize_o    (c_m_axi_arsize_o),
    .c_m_axi_axburst_o   (c_m_axi_arburst_o),
    .c_m_axi_axlock_o    (c_m_axi_arlock_o),
    .c_m_axi_axcache_o   (c_m_axi_arcache_o),
    .c_m_axi_axprot_o    (c_m_axi_arprot_o),
    .c_m_axi_axqos_o     (c_m_axi_arqos_o),

    .a_m_axi_fault_o     (m_axi_ar_a_fault),
    .b_m_axi_fault_o     (m_axi_ar_b_fault),
    .c_m_axi_fault_o     (m_axi_ar_c_fault),

    .a_m_axi_fault_i     (a_m_axi_fault),
    .b_m_axi_fault_i     (b_m_axi_fault),
    .c_m_axi_fault_i     (c_m_axi_fault),

    .a_m_axi_fault_clr_i (a_m_axi_fault_clr_i),
    .b_m_axi_fault_clr_i (b_m_axi_fault_clr_i),
    .c_m_axi_fault_clr_i (c_m_axi_fault_clr_i),

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

    .a_m_axi_rvalid_i    (a_m_axi_rvalid_i),
    .a_m_axi_rready_o    (a_m_axi_rready_o),
    .a_m_axi_rid_i       (a_m_axi_rid_i),
    .a_m_axi_rdata_i     (a_m_axi_rdata_i),
    .a_m_axi_rresp_i     (a_m_axi_rresp_i),
    .a_m_axi_rlast_i     (a_m_axi_rlast_i),

    .b_m_axi_rvalid_i    (b_m_axi_rvalid_i),
    .b_m_axi_rready_o    (b_m_axi_rready_o),
    .b_m_axi_rid_i       (b_m_axi_rid_i),
    .b_m_axi_rdata_i     (b_m_axi_rdata_i),
    .b_m_axi_rresp_i     (b_m_axi_rresp_i),
    .b_m_axi_rlast_i     (b_m_axi_rlast_i),

    .c_m_axi_rvalid_i    (c_m_axi_rvalid_i),
    .c_m_axi_rready_o    (c_m_axi_rready_o),
    .c_m_axi_rid_i       (c_m_axi_rid_i),
    .c_m_axi_rdata_i     (c_m_axi_rdata_i),
    .c_m_axi_rresp_i     (c_m_axi_rresp_i),
    .c_m_axi_rlast_i     (c_m_axi_rlast_i),

    .a_m_axi_fault_o     (m_axi_r_a_fault),
    .b_m_axi_fault_o     (m_axi_r_b_fault),
    .c_m_axi_fault_o     (m_axi_r_c_fault),

    .a_m_axi_fault_i     (a_m_axi_fault),
    .b_m_axi_fault_i     (b_m_axi_fault),
    .c_m_axi_fault_i     (c_m_axi_fault),

    .a_m_axi_fault_clr_i (a_m_axi_fault_clr_i),
    .b_m_axi_fault_clr_i (b_m_axi_fault_clr_i),
    .c_m_axi_fault_clr_i (c_m_axi_fault_clr_i),

    .s_axi_rvalid_o      (s_axi_rvalid_o),
    .s_axi_rready_i      (s_axi_rready_i),
    .s_axi_rid_o         (s_axi_rid_o),
    .s_axi_rdata_o       (s_axi_rdata_o),
    .s_axi_rresp_o       (s_axi_rresp_o),
    .s_axi_rlast_o       (s_axi_rlast_o)
  );

  // ......................................................
  // Fault aggregation and loopback

  el2_mubi_t a_m_axi_fault_l0;
  el2_mubi_t a_m_axi_fault_l1;
  el2_mubi_t a_m_axi_fault_l2;

  el2_mubi_t b_m_axi_fault_l0;
  el2_mubi_t b_m_axi_fault_l1;
  el2_mubi_t b_m_axi_fault_l2;

  el2_mubi_t c_m_axi_fault_l0;
  el2_mubi_t c_m_axi_fault_l1;
  el2_mubi_t c_m_axi_fault_l2;

  always_comb begin
    a_m_axi_fault_l0 = mubi_or(m_axi_aw_a_fault, m_axi_w_a_fault);
    a_m_axi_fault_l1 = mubi_or(b_a_m_axi_fault,  m_axi_ar_a_fault);
    a_m_axi_fault_l2 = mubi_or(m_axi_r_a_fault,  a_m_axi_fault_i);

    a_m_axi_fault    = mubi_or3(a_m_axi_fault_l0, a_m_axi_fault_l1, a_m_axi_fault_l2);
  end

  always_comb begin
    b_m_axi_fault_l0 = mubi_or(m_axi_aw_b_fault, m_axi_w_b_fault);
    b_m_axi_fault_l1 = mubi_or(b_m_axi_b_fault,  m_axi_ar_b_fault);
    b_m_axi_fault_l2 = mubi_or(m_axi_r_b_fault,  b_m_axi_fault_i);

    b_m_axi_fault    = mubi_or3(b_m_axi_fault_l0, b_m_axi_fault_l1, b_m_axi_fault_l2);
  end

  always_comb begin
    c_m_axi_fault_l0 = mubi_or(m_axi_aw_c_fault, m_axi_w_c_fault);
    c_m_axi_fault_l1 = mubi_or(b_m_axi_c_fault,  m_axi_ar_c_fault);
    c_m_axi_fault_l2 = mubi_or(m_axi_r_c_fault,  c_m_axi_fault_i);

    c_m_axi_fault    = mubi_or3(c_m_axi_fault_l0, c_m_axi_fault_l1, c_m_axi_fault_l2);
  end

  // ......................................................
  // Fault output

  always_comb begin
    a_m_axi_fault_o = a_m_axi_fault;
    b_m_axi_fault_o = b_m_axi_fault;
    c_m_axi_fault_o = c_m_axi_fault;
  end

endmodule
