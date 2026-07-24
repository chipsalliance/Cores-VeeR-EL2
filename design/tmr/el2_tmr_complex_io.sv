// Copyright 2026 Antmicro <www.antmicro.com>
// //
// // SPDX-License-Identifier: Apache-2.0
//
module el2_tmr_complex_io
  import el2_pkg::*;
  import el2_mubi_pkg::*;
  import el2_lockstep_pkg::*;
#(
    `include "el2_param.vh"
) (
    input  logic free_l2clk,
    input  logic free_clk,
    input  logic core_rst_l,
    input  logic dbg_rst_l,
    input  logic ifu_bus_clk_en,
    input  logic lsu_bus_clk_en,
    input  logic dbg_bus_clk_en,
    input  logic dma_bus_clk_en,
    input  logic dec_tlu_bus_clk_override_int,
    input  logic dec_tlu_force_halt_int,

    // External Buses
    //-------------------------- LSU AXI signals--------------------------
    // AXI Write Channels
    output logic                            lsu_axi_awvalid,
    input  logic                            lsu_axi_awready,
    output logic [pt.LSU_BUS_TAG-1:0]       lsu_axi_awid,
    output logic [31:0]                     lsu_axi_awaddr,
    output logic [3:0]                      lsu_axi_awregion,
    /* exclude signals that are tied to constant value in el2_lsu_bus_buffer.sv */
    /*pragma coverage off*/
    output logic [7:0]                      lsu_axi_awlen,
    /*pragma coverage on*/
    output logic [2:0]                      lsu_axi_awsize,
    /* exclude signals that are tied to constant value in el2_lsu_bus_buffer.sv */
    /*pragma coverage off*/
    output logic [1:0]                      lsu_axi_awburst,
    output logic                            lsu_axi_awlock,
    /*pragma coverage on*/
    output logic [3:0]                      lsu_axi_awcache,
    /* exclude signals that are tied to constant value in el2_lsu_bus_buffer.sv */
    /*pragma coverage off*/
    output logic [2:0]                      lsu_axi_awprot,
    output logic [3:0]                      lsu_axi_awqos,
    /*pragma coverage on*/

    output logic                            lsu_axi_wvalid,
    input  logic                            lsu_axi_wready,
    output logic [63:0]                     lsu_axi_wdata,
    output logic [7:0]                      lsu_axi_wstrb,
    output logic                            lsu_axi_wlast,

    input  logic                            lsu_axi_bvalid,
    /* exclude signals that are tied to constant value in el2_lsu_bus_buffer.sv */
    /*pragma coverage off*/
    output logic                            lsu_axi_bready,
    /*pragma coverage on*/
    input  logic [1:0]                      lsu_axi_bresp,
    input  logic [pt.LSU_BUS_TAG-1:0]       lsu_axi_bid,

    // AXI Read Channels
    output logic                            lsu_axi_arvalid,
    input  logic                            lsu_axi_arready,
    output logic [pt.LSU_BUS_TAG-1:0]       lsu_axi_arid,
    output logic [31:0]                     lsu_axi_araddr,
    output logic [3:0]                      lsu_axi_arregion,
    /* exclude signals that are tied to constant value in el2_lsu_bus_buffer.sv */
    /*pragma coverage off*/
    output logic [7:0]                      lsu_axi_arlen,
    /*pragma coverage on*/
    output logic [2:0]                      lsu_axi_arsize,
    /* exclude signals that are tied to constant value in el2_lsu_bus_buffer.sv */
    /*pragma coverage off*/
    output logic [1:0]                      lsu_axi_arburst,
    output logic                            lsu_axi_arlock,
    /*pragma coverage on*/
    output logic [3:0]                      lsu_axi_arcache,
    /* exclude signals that are tied to constant value in el2_lsu_bus_buffer.sv */
    /*pragma coverage off*/
    output logic [2:0]                      lsu_axi_arprot,
    output logic [3:0]                      lsu_axi_arqos,
    /*pragma coverage on*/

    input  logic                            lsu_axi_rvalid,
    /* exclude signals that are tied to constant value in el2_lsu_bus_buffer.sv */
    /*pragma coverage off*/
    output logic                            lsu_axi_rready,
    /*pragma coverage on*/
    input  logic [pt.LSU_BUS_TAG-1:0]       lsu_axi_rid,
    input  logic [63:0]                     lsu_axi_rdata,
    input  logic [1:0]                      lsu_axi_rresp,
    input  logic                            lsu_axi_rlast,
    //-------------------------- IFU AXI signals--------------------------
    // AXI Write Channels
    /* exclude signals that are tied to constant value in el2_ifu_mem_ctl.sv
       IFU does not use AXI write channel */
    /*pragma coverage off*/
    output logic                            ifu_axi_awvalid,
    input  logic                            ifu_axi_awready,
    output logic [pt.IFU_BUS_TAG-1:0]       ifu_axi_awid,
    output logic [31:0]                     ifu_axi_awaddr,
    output logic [3:0]                      ifu_axi_awregion,
    output logic [7:0]                      ifu_axi_awlen,
    output logic [2:0]                      ifu_axi_awsize,
    output logic [1:0]                      ifu_axi_awburst,
    output logic                            ifu_axi_awlock,
    output logic [3:0]                      ifu_axi_awcache,
    output logic [2:0]                      ifu_axi_awprot,
    output logic [3:0]                      ifu_axi_awqos,

    output logic                            ifu_axi_wvalid,
    input  logic                            ifu_axi_wready,
    output logic [63:0]                     ifu_axi_wdata,
    output logic [7:0]                      ifu_axi_wstrb,
    output logic                            ifu_axi_wlast,

    input  logic                            ifu_axi_bvalid,
    output logic                            ifu_axi_bready,
    input  logic [1:0]                      ifu_axi_bresp,
    input  logic [pt.IFU_BUS_TAG-1:0]       ifu_axi_bid,
    /*pragma coverage on*/

    // AXI Read Channels
    output logic                            ifu_axi_arvalid,
    input  logic                            ifu_axi_arready,
    output logic [pt.IFU_BUS_TAG-1:0]       ifu_axi_arid,
    output logic [31:0]                     ifu_axi_araddr,
    output logic [3:0]                      ifu_axi_arregion,
    /* exclude signals that are tied to constant value in el2_ifu_mem_ctl.sv */
    /*pragma coverage off*/
    output logic [7:0]                      ifu_axi_arlen,
    output logic [2:0]                      ifu_axi_arsize,
    output logic [1:0]                      ifu_axi_arburst,
    output logic                            ifu_axi_arlock,
    output logic [3:0]                      ifu_axi_arcache,
    output logic [2:0]                      ifu_axi_arprot,
    output logic [3:0]                      ifu_axi_arqos,
    /*pragma coverage on*/

    input  logic                            ifu_axi_rvalid,
    /* exclude signals that are tied to constant value in el2_ifu_mem_ctl.sv */
    /*pragma coverage off*/
    output logic                            ifu_axi_rready,
    /*pragma coverage on*/
    input  logic [pt.IFU_BUS_TAG-1:0]       ifu_axi_rid,
    input  logic [63:0]                     ifu_axi_rdata,
    input  logic [1:0]                      ifu_axi_rresp,
    input  logic                            ifu_axi_rlast,

    //-------------------------- SB AXI signals--------------------------
    // AXI Write Channels
    output logic                            sb_axi_awvalid,
    input  logic                            sb_axi_awready,
    /* exclude signals that are tied to constant value in dbg/el2_dbg.sv */
    /*pragma coverage off*/
    output logic [pt.SB_BUS_TAG-1:0]        sb_axi_awid,
    /*pragma coverage on*/
    output logic [31:0]                     sb_axi_awaddr,
    output logic [3:0]                      sb_axi_awregion,
    /* exclude signals that are tied to constant value in dbg/el2_dbg.sv */
    /*pragma coverage off*/
    output logic [7:0]                      sb_axi_awlen,
    /*pragma coverage on*/
    output logic [2:0]                      sb_axi_awsize,
    /* exclude signals that are tied to constant value in dbg/el2_dbg.sv */
    /*pragma coverage off*/
    output logic [1:0]                      sb_axi_awburst,
    output logic                            sb_axi_awlock,
    output logic [3:0]                      sb_axi_awcache,
    output logic [2:0]                      sb_axi_awprot,
    output logic [3:0]                      sb_axi_awqos,
    /*pragma coverage on*/

    output logic                            sb_axi_wvalid,
    input  logic                            sb_axi_wready,
    output logic [63:0]                     sb_axi_wdata,
    output logic [7:0]                      sb_axi_wstrb,
    output logic                            sb_axi_wlast,

    input  logic                            sb_axi_bvalid,
    output logic                            sb_axi_bready,
    input  logic [1:0]                      sb_axi_bresp,
    input  logic [pt.SB_BUS_TAG-1:0]        sb_axi_bid,

    // AXI Read Channels
    output logic                            sb_axi_arvalid,
    input  logic                            sb_axi_arready,
    /* exclude signals that are tied to constant value in dbg/el2_dbg.sv */
    /*pragma coverage off*/
    output logic [pt.SB_BUS_TAG-1:0]        sb_axi_arid,
    /*pragma coverage on*/
    output logic [31:0]                     sb_axi_araddr,
    output logic [3:0]                      sb_axi_arregion,
    /* exclude signals that are tied to constant value in dbg/el2_dbg.sv */
    /*pragma coverage off*/
    output logic [7:0]                      sb_axi_arlen,
    /*pragma coverage on*/
    output logic [2:0]                      sb_axi_arsize,
    /* exclude signals that are tied to constant value in dbg/el2_dbg.sv */
    /*pragma coverage off*/
    output logic [1:0]                      sb_axi_arburst,
    output logic                            sb_axi_arlock,
    output logic [3:0]                      sb_axi_arcache,
    output logic [2:0]                      sb_axi_arprot,
    output logic [3:0]                      sb_axi_arqos,
    /*pragma coverage on*/

    input  logic                            sb_axi_rvalid,
    /* exclude signals that are tied to constant value in dbg/el2_dbg.sv */
    /*pragma coverage off*/
    output logic                            sb_axi_rready,
    /*pragma coverage on*/
    input  logic [pt.SB_BUS_TAG-1:0]        sb_axi_rid,
    input  logic [63:0]                     sb_axi_rdata,
    input  logic [1:0]                      sb_axi_rresp,
    input  logic                            sb_axi_rlast,

    //-------------------------- DMA AXI signals--------------------------
    // AXI Write Channels
    input  logic                         dma_axi_awvalid,
    output logic                         dma_axi_awready,
    input  logic [pt.DMA_BUS_TAG-1:0]    dma_axi_awid,
    input  logic [31:0]                  dma_axi_awaddr,
    input  logic [2:0]                   dma_axi_awsize,
    input  logic [2:0]                   dma_axi_awprot,
    input  logic [7:0]                   dma_axi_awlen,
    input  logic [1:0]                   dma_axi_awburst,


    input  logic                         dma_axi_wvalid,
    output logic                         dma_axi_wready,
    input  logic [63:0]                  dma_axi_wdata,
    input  logic [7:0]                   dma_axi_wstrb,
    input  logic                         dma_axi_wlast,

    output logic                         dma_axi_bvalid,
    input  logic                         dma_axi_bready,
    output logic [1:0]                   dma_axi_bresp,
    output logic [pt.DMA_BUS_TAG-1:0]    dma_axi_bid,

    // AXI Read Channels
    input  logic                         dma_axi_arvalid,
    output logic                         dma_axi_arready,
    input  logic [pt.DMA_BUS_TAG-1:0]    dma_axi_arid,
    input  logic [31:0]                  dma_axi_araddr,
    input  logic [2:0]                   dma_axi_arsize,
    input  logic [2:0]                   dma_axi_arprot,
    input  logic [7:0]                   dma_axi_arlen,
    input  logic [1:0]                   dma_axi_arburst,

    output logic                         dma_axi_rvalid,
    input  logic                         dma_axi_rready,
    output logic [pt.DMA_BUS_TAG-1:0]    dma_axi_rid,
    output logic [63:0]                  dma_axi_rdata,
    output logic [1:0]                   dma_axi_rresp,
    output logic                         dma_axi_rlast,


  //// AHB LITE BUS
    output logic [31:0] haddr,
    /* exclude signals that are tied to constant value in axi4_to_ahb.sv */
    /*pragma coverage off*/
    output logic [2:0]  hburst,
    output logic        hmastlock,
    /*pragma coverage on*/
    output logic [3:0]  hprot,
    output logic [2:0]  hsize,
    output logic [1:0]  htrans,
    output logic        hwrite,

    input  logic [63:0] hrdata,
    input  logic        hready,
    input  logic        hresp,

    // LSU AHB Master
    output logic [31:0] lsu_haddr,
    /* exclude signals that are tied to constant value in axi4_to_ahb.sv */
    /*pragma coverage off*/
    output logic [2:0]  lsu_hburst,
    output logic        lsu_hmastlock,
    /*pragma coverage on*/
    output logic [3:0]  lsu_hprot,
    output logic [2:0]  lsu_hsize,
    output logic [1:0]  lsu_htrans,
    output logic        lsu_hwrite,
    output logic [63:0] lsu_hwdata,

    input  logic [63:0] lsu_hrdata,
    input  logic        lsu_hready,
    input  logic        lsu_hresp,

    //System Bus Debug Master
    output logic [31:0] sb_haddr,
    /* exclude signals that are tied to constant value in axi4_to_ahb.sv */
    /*pragma coverage off*/
    output logic [2:0]  sb_hburst,
    output logic        sb_hmastlock,
    /*pragma coverage on*/
    output logic [3:0]  sb_hprot,
    output logic [2:0]  sb_hsize,
    output logic [1:0]  sb_htrans,
    output logic        sb_hwrite,
    output logic [63:0] sb_hwdata,

    input  logic [63:0] sb_hrdata,
    input  logic        sb_hready,
    input  logic        sb_hresp,

    // DMA Slave
    input  logic        dma_hsel,
    input  logic [31:0] dma_haddr,
    input  logic [2:0]  dma_hburst,
    input  logic        dma_hmastlock,
    input  logic [3:0]  dma_hprot,
    input  logic [2:0]  dma_hsize,
    input  logic [1:0]  dma_htrans,
    input  logic        dma_hwrite,
    input  logic [63:0] dma_hwdata,
    input  logic        dma_hreadyin,

    output logic [63:0] dma_hrdata,
    output logic        dma_hreadyout,
    output logic        dma_hresp,

    // Internal buses
    //-------------------------- LSU AXI signals--------------------------
    // AXI Write Channels
    input  logic                            lsu_axi_awvalid_int,
    output logic                            lsu_axi_awready_int,
    input  logic [pt.LSU_BUS_TAG-1:0]       lsu_axi_awid_int,
    input  logic [31:0]                     lsu_axi_awaddr_int,
    input  logic [3:0]                      lsu_axi_awregion_int,
    /* exclude signals that are tied to constant value in el2_lsu_bus_buffer.sv */
    /*pragma coverage off*/
    input  logic [7:0]                      lsu_axi_awlen_int,
    /*pragma coverage on*/
    input  logic [2:0]                      lsu_axi_awsize_int,
    /* exclude signals that are tied to constant value in el2_lsu_bus_buffer.sv */
    /*pragma coverage off*/
    input  logic [1:0]                      lsu_axi_awburst_int,
    input  logic                            lsu_axi_awlock_int,
    /*pragma coverage on*/
    input  logic [3:0]                      lsu_axi_awcache_int,
    /* exclude signals that are tied to constant value in el2_lsu_bus_buffer.sv */
    /*pragma coverage off*/
    input  logic [2:0]                      lsu_axi_awprot_int,
    input  logic [3:0]                      lsu_axi_awqos_int,
    /*pragma coverage on*/

    input  logic                            lsu_axi_wvalid_int,
    output logic                            lsu_axi_wready_int,
    input  logic [63:0]                     lsu_axi_wdata_int,
    input  logic [7:0]                      lsu_axi_wstrb_int,
    input  logic                            lsu_axi_wlast_int,

    output logic                            lsu_axi_bvalid_int,
    /* exclude signals that are tied to constant value in el2_lsu_bus_buffer.sv */
    /*pragma coverage off*/
    input  logic                            lsu_axi_bready_int,
    /*pragma coverage on*/
    output logic [1:0]                      lsu_axi_bresp_int,
    output logic [pt.LSU_BUS_TAG-1:0]       lsu_axi_bid_int,

    // AXI Read Channels
    input  logic                            lsu_axi_arvalid_int,
    output logic                            lsu_axi_arready_int,
    input  logic [pt.LSU_BUS_TAG-1:0]       lsu_axi_arid_int,
    input  logic [31:0]                     lsu_axi_araddr_int,
    input  logic [3:0]                      lsu_axi_arregion_int,
    /* exclude signals that are tied to constant value in el2_lsu_bus_buffer.sv */
    /*pragma coverage off*/
    input  logic [7:0]                      lsu_axi_arlen_int,
    /*pragma coverage on*/
    input  logic [2:0]                      lsu_axi_arsize_int,
    /* exclude signals that are tied to constant value in el2_lsu_bus_buffer.sv */
    /*pragma coverage off*/
    input  logic [1:0]                      lsu_axi_arburst_int,
    input  logic                            lsu_axi_arlock_int,
    /*pragma coverage on*/
    input  logic [3:0]                      lsu_axi_arcache_int,
    /* exclude signals that are tied to constant value in el2_lsu_bus_buffer.sv */
    /*pragma coverage off*/
    input  logic [2:0]                      lsu_axi_arprot_int,
    input  logic [3:0]                      lsu_axi_arqos_int,
    /*pragma coverage on*/

    output logic                            lsu_axi_rvalid_int,
    /* exclude signals that are tied to constant value in el2_lsu_bus_buffer.sv */
    /*pragma coverage off*/
    input  logic                            lsu_axi_rready_int,
    /*pragma coverage on*/
    output logic [pt.LSU_BUS_TAG-1:0]       lsu_axi_rid_int,
    output logic [63:0]                     lsu_axi_rdata_int,
    output logic [1:0]                      lsu_axi_rresp_int,
    output logic                            lsu_axi_rlast_int,

    //-------------------------- IFU AXI signals--------------------------
    // AXI Write Channels
    /* exclude signals that are tied to constant value in el2_ifu_mem_ctl.sv
       IFU does not use AXI write channel */
    /*pragma coverage off*/
    input  logic                            ifu_axi_awvalid_int,
    output logic                            ifu_axi_awready_int,
    input  logic [pt.IFU_BUS_TAG-1:0]       ifu_axi_awid_int,
    input  logic [31:0]                     ifu_axi_awaddr_int,
    input  logic [3:0]                      ifu_axi_awregion_int,
    input  logic [7:0]                      ifu_axi_awlen_int,
    input  logic [2:0]                      ifu_axi_awsize_int,
    input  logic [1:0]                      ifu_axi_awburst_int,
    input  logic                            ifu_axi_awlock_int,
    input  logic [3:0]                      ifu_axi_awcache_int,
    input  logic [2:0]                      ifu_axi_awprot_int,
    input  logic [3:0]                      ifu_axi_awqos_int,

    input  logic                            ifu_axi_wvalid_int,
    output logic                            ifu_axi_wready_int,
    input  logic [63:0]                     ifu_axi_wdata_int,
    input  logic [7:0]                      ifu_axi_wstrb_int,
    input  logic                            ifu_axi_wlast_int,

    output logic                            ifu_axi_bvalid_int,
    input  logic                            ifu_axi_bready_int,
    output logic [1:0]                      ifu_axi_bresp_int,
    output logic [pt.IFU_BUS_TAG-1:0]       ifu_axi_bid_int,
    /*pragma coverage on*/

    // AXI Read Channels
    input  logic                            ifu_axi_arvalid_int,
    output logic                            ifu_axi_arready_int,
    input  logic [pt.IFU_BUS_TAG-1:0]       ifu_axi_arid_int,
    input  logic [31:0]                     ifu_axi_araddr_int,
    input  logic [3:0]                      ifu_axi_arregion_int,
    /* exclude signals that are tied to constant value in el2_ifu_mem_ctl.sv */
    /*pragma coverage off*/
    input  logic [7:0]                      ifu_axi_arlen_int,
    input  logic [2:0]                      ifu_axi_arsize_int,
    input  logic [1:0]                      ifu_axi_arburst_int,
    input  logic                            ifu_axi_arlock_int,
    input  logic [3:0]                      ifu_axi_arcache_int,
    input  logic [2:0]                      ifu_axi_arprot_int,
    input  logic [3:0]                      ifu_axi_arqos_int,
    /*pragma coverage on*/

    output logic                            ifu_axi_rvalid_int,
    /* exclude signals that are tied to constant value in el2_ifu_mem_ctl.sv */
    /*pragma coverage off*/
    input  logic                            ifu_axi_rready_int,
    /*pragma coverage on*/
    output logic [pt.IFU_BUS_TAG-1:0]       ifu_axi_rid_int,
    output logic [63:0]                     ifu_axi_rdata_int,
    output logic [1:0]                      ifu_axi_rresp_int,
    output logic                            ifu_axi_rlast_int,

    //-------------------------- SB AXI signals--------------------------
    // AXI Write Channels
    input  logic                            sb_axi_awvalid_int,
    output logic                            sb_axi_awready_int,
    /* exclude signals that are tied to constant value in dbg/el2_dbg.sv */
    /*pragma coverage off*/
    input  logic [pt.SB_BUS_TAG-1:0]        sb_axi_awid_int,
    /*pragma coverage on*/
    input  logic [31:0]                     sb_axi_awaddr_int,
    input  logic [3:0]                      sb_axi_awregion_int,
    /* exclude signals that are tied to constant value in dbg/el2_dbg.sv */
    /*pragma coverage off*/
    input  logic [7:0]                      sb_axi_awlen_int,
    /*pragma coverage on*/
    input  logic [2:0]                      sb_axi_awsize_int,
    /* exclude signals that are tied to constant value in dbg/el2_dbg.sv */
    /*pragma coverage off*/
    input  logic [1:0]                      sb_axi_awburst_int,
    input  logic                            sb_axi_awlock_int,
    input  logic [3:0]                      sb_axi_awcache_int,
    input  logic [2:0]                      sb_axi_awprot_int,
    input  logic [3:0]                      sb_axi_awqos_int,
    /*pragma coverage on*/

    input  logic                            sb_axi_wvalid_int,
    output logic                            sb_axi_wready_int,
    input  logic [63:0]                     sb_axi_wdata_int,
    input  logic [7:0]                      sb_axi_wstrb_int,
    input  logic                            sb_axi_wlast_int,

    output logic                            sb_axi_bvalid_int,
    input  logic                            sb_axi_bready_int,
    output logic [1:0]                      sb_axi_bresp_int,
    output logic [pt.SB_BUS_TAG-1:0]        sb_axi_bid_int,

    // AXI Read Channels
    input  logic                            sb_axi_arvalid_int,
    output logic                            sb_axi_arready_int,
    /* exclude signals that are tied to constant value in dbg/el2_dbg.sv */
    /*pragma coverage off*/
    input  logic [pt.SB_BUS_TAG-1:0]        sb_axi_arid_int,
    /*pragma coverage on*/
    input  logic [31:0]                     sb_axi_araddr_int,
    input  logic [3:0]                      sb_axi_arregion_int,
    /* exclude signals that are tied to constant value in dbg/el2_dbg.sv */
    /*pragma coverage off*/
    input  logic [7:0]                      sb_axi_arlen_int,
    /*pragma coverage on*/
    input  logic [2:0]                      sb_axi_arsize_int,
    /* exclude signals that are tied to constant value in dbg/el2_dbg.sv */
    /*pragma coverage off*/
    input  logic [1:0]                      sb_axi_arburst_int,
    input  logic                            sb_axi_arlock_int,
    input  logic [3:0]                      sb_axi_arcache_int,
    input  logic [2:0]                      sb_axi_arprot_int,
    input  logic [3:0]                      sb_axi_arqos_int,
    /*pragma coverage on*/

    output logic                            sb_axi_rvalid_int,
    /* exclude signals that are tied to constant value in dbg/el2_dbg.sv */
    /*pragma coverage off*/
    input  logic                            sb_axi_rready_int,
    /*pragma coverage on*/
    output logic [pt.SB_BUS_TAG-1:0]        sb_axi_rid_int,
    output logic [63:0]                     sb_axi_rdata_int,
    output logic [1:0]                      sb_axi_rresp_int,
    output logic                            sb_axi_rlast_int,

    //-------------------------- DMA AXI signals--------------------------
    // AXI Write Channels
    output logic                         dma_axi_awvalid_int,
    input  logic                         dma_axi_awready_int,
    output logic [pt.DMA_BUS_TAG-1:0]    dma_axi_awid_int,
    output logic [31:0]                  dma_axi_awaddr_int,
    output logic [2:0]                   dma_axi_awsize_int,
    output logic [2:0]                   dma_axi_awprot_int,
    output logic [7:0]                   dma_axi_awlen_int,
    output logic [1:0]                   dma_axi_awburst_int,

    output logic                         dma_axi_wvalid_int,
    input  logic                         dma_axi_wready_int,
    output logic [63:0]                  dma_axi_wdata_int,
    output logic [7:0]                   dma_axi_wstrb_int,
    output logic                         dma_axi_wlast_int,

    input  logic                         dma_axi_bvalid_int,
    output logic                         dma_axi_bready_int,
    input  logic [1:0]                   dma_axi_bresp_int,
    input  logic [pt.DMA_BUS_TAG-1:0]    dma_axi_bid_int,

    // AXI Read Channels
    output logic                         dma_axi_arvalid_int,
    input  logic                         dma_axi_arready_int,
    output logic [pt.DMA_BUS_TAG-1:0]    dma_axi_arid_int,
    output logic [31:0]                  dma_axi_araddr_int,
    output logic [2:0]                   dma_axi_arsize_int,
    output logic [2:0]                   dma_axi_arprot_int,
    output logic [7:0]                   dma_axi_arlen_int,
    output logic [1:0]                   dma_axi_arburst_int,

    input  logic                         dma_axi_rvalid_int,
    output logic                         dma_axi_rready_int,
    input  logic [pt.DMA_BUS_TAG-1:0]    dma_axi_rid_int,
    input  logic [63:0]                  dma_axi_rdata_int,
    input  logic [1:0]                   dma_axi_rresp_int,
    input  logic                         dma_axi_rlast_int,
    // Excluding scan_mode from coverage as its usage is determined by the integrator of the VeeR core.
    // /*pragma coverage off*/
    input  logic scan_mode
    /*pragma coverage on*/
);

  // AHB LITE BUS 2 AXI signals
  logic [63:0]               hwdata_nc;

  logic                      lsu_axi_awready_ahb;
  logic                      lsu_axi_wready_ahb;
  logic                      lsu_axi_bvalid_ahb;
  logic                      lsu_axi_bready_ahb;
  logic [1:0]                lsu_axi_bresp_ahb;
  logic [pt.LSU_BUS_TAG-1:0] lsu_axi_bid_ahb;
  logic                      lsu_axi_arready_ahb;
  logic                      lsu_axi_rvalid_ahb;
  logic [pt.LSU_BUS_TAG-1:0] lsu_axi_rid_ahb;
  logic [63:0]               lsu_axi_rdata_ahb;
  logic [1:0]                lsu_axi_rresp_ahb;
  logic                      lsu_axi_rlast_ahb;

  logic                      ifu_axi_awready_ahb;
  logic                      ifu_axi_wready_ahb;
  logic                      ifu_axi_bvalid_ahb;
  logic                      ifu_axi_bready_ahb;
  logic [1:0]                ifu_axi_bresp_ahb;
  logic [pt.IFU_BUS_TAG-1:0] ifu_axi_bid_ahb;
  logic                      ifu_axi_arready_ahb;
  logic                      ifu_axi_rvalid_ahb;
  logic [pt.IFU_BUS_TAG-1:0] ifu_axi_rid_ahb;
  logic [63:0]               ifu_axi_rdata_ahb;
  logic [1:0]                ifu_axi_rresp_ahb;
  logic                      ifu_axi_rlast_ahb;

  logic                     sb_axi_awready_ahb;
  logic                     sb_axi_wready_ahb;
  logic                     sb_axi_bvalid_ahb;
  logic                     sb_axi_bready_ahb;
  logic [1:0]               sb_axi_bresp_ahb;
  logic [pt.SB_BUS_TAG-1:0] sb_axi_bid_ahb;
  logic                     sb_axi_arready_ahb;
  logic                     sb_axi_rvalid_ahb;
  logic [pt.SB_BUS_TAG-1:0] sb_axi_rid_ahb;
  logic [63:0]              sb_axi_rdata_ahb;
  logic [1:0]               sb_axi_rresp_ahb;
  logic                     sb_axi_rlast_ahb;

  logic                      dma_axi_awvalid_ahb;
  logic [pt.DMA_BUS_TAG-1:0] dma_axi_awid_ahb;
  logic [31:0]               dma_axi_awaddr_ahb;
  logic [2:0]                dma_axi_awsize_ahb;
  logic [2:0]                dma_axi_awprot_ahb;
  logic [7:0]                dma_axi_awlen_ahb;
  logic [1:0]                dma_axi_awburst_ahb;
  logic                      dma_axi_wvalid_ahb;
  logic [63:0]               dma_axi_wdata_ahb;
  logic [7:0]                dma_axi_wstrb_ahb;
  logic                      dma_axi_wlast_ahb;
  logic                      dma_axi_bready_ahb;
  logic                      dma_axi_arvalid_ahb;
  logic [pt.DMA_BUS_TAG-1:0] dma_axi_arid_ahb;
  logic [31:0]               dma_axi_araddr_ahb;
  logic [2:0]                dma_axi_arsize_ahb;
  logic [2:0]                dma_axi_arprot_ahb;
  logic [7:0]                dma_axi_arlen_ahb;
  logic [1:0]                dma_axi_arburst_ahb;
  logic                      dma_axi_rready_ahb;

  // Drive the external AXI with the post TMR AXI bus or the AHB translation
  assign lsu_axi_awvalid                     = lsu_axi_awvalid_int;
  assign lsu_axi_awready_int                 = pt.BUILD_AHB_LITE ? lsu_axi_awready_ahb : lsu_axi_awready;
  assign lsu_axi_awid                        = lsu_axi_awid_int;
  assign lsu_axi_awaddr                      = lsu_axi_awaddr_int;
  assign lsu_axi_awregion                    = lsu_axi_awregion_int;
  assign lsu_axi_awlen                       = lsu_axi_awlen_int;
  assign lsu_axi_awsize                      = lsu_axi_awsize_int;
  assign lsu_axi_awburst                     = lsu_axi_awburst_int;
  assign lsu_axi_awlock                      = lsu_axi_awlock_int;
  assign lsu_axi_awcache                     = lsu_axi_awcache_int;
  assign lsu_axi_awprot                      = lsu_axi_awprot_int;
  assign lsu_axi_awqos                       = lsu_axi_awqos_int;
  assign lsu_axi_wvalid                      = lsu_axi_wvalid_int;
  assign lsu_axi_wready_int                  = pt.BUILD_AHB_LITE ? lsu_axi_wready_ahb : lsu_axi_wready;
  assign lsu_axi_wdata                       = lsu_axi_wdata_int;
  assign lsu_axi_wstrb                       = lsu_axi_wstrb_int;
  assign lsu_axi_wlast                       = lsu_axi_wlast_int;
  assign lsu_axi_bvalid_int                  = pt.BUILD_AHB_LITE ? lsu_axi_bvalid_ahb : lsu_axi_bvalid;
  assign lsu_axi_bready                      = lsu_axi_bready_int;
  assign lsu_axi_bresp_int[1:0]              = pt.BUILD_AHB_LITE ? lsu_axi_bresp_ahb[1:0] : lsu_axi_bresp[1:0];
  assign lsu_axi_bid_int[pt.LSU_BUS_TAG-1:0] = pt.BUILD_AHB_LITE ? lsu_axi_bid_ahb[pt.LSU_BUS_TAG-1:0] : lsu_axi_bid[pt.LSU_BUS_TAG-1:0];
  assign lsu_axi_arvalid                     = lsu_axi_arvalid_int;
  assign lsu_axi_arready_int                 = pt.BUILD_AHB_LITE ? lsu_axi_arready_ahb : lsu_axi_arready;
  assign lsu_axi_arid                        = lsu_axi_arid_int;
  assign lsu_axi_araddr                      = lsu_axi_araddr_int;
  assign lsu_axi_arregion                    = lsu_axi_arregion_int;
  assign lsu_axi_arlen                       = lsu_axi_arlen_int;
  assign lsu_axi_arsize                      = lsu_axi_arsize_int;
  assign lsu_axi_arburst                     = lsu_axi_arburst_int;
  assign lsu_axi_arlock                      = lsu_axi_arlock_int;
  assign lsu_axi_arcache                     = lsu_axi_arcache_int;
  assign lsu_axi_arprot                      = lsu_axi_arprot_int;
  assign lsu_axi_arqos                       = lsu_axi_arqos_int;
  assign lsu_axi_rvalid_int                  = pt.BUILD_AHB_LITE ? lsu_axi_rvalid_ahb : lsu_axi_rvalid;
  assign lsu_axi_rready                      = lsu_axi_rready_int;
  assign lsu_axi_rid_int[pt.LSU_BUS_TAG-1:0] = pt.BUILD_AHB_LITE ? lsu_axi_rid_ahb[pt.LSU_BUS_TAG-1:0] : lsu_axi_rid[pt.LSU_BUS_TAG-1:0];
  assign lsu_axi_rdata_int[63:0]             = pt.BUILD_AHB_LITE ? lsu_axi_rdata_ahb[63:0] : lsu_axi_rdata[63:0];
  assign lsu_axi_rresp_int[1:0]              = pt.BUILD_AHB_LITE ? lsu_axi_rresp_ahb[1:0] : lsu_axi_rresp[1:0];
  assign lsu_axi_rlast_int                   = pt.BUILD_AHB_LITE ? lsu_axi_rlast_ahb : lsu_axi_rlast;

  assign ifu_axi_awvalid                     = ifu_axi_awvalid_int;
  assign ifu_axi_awready_int                 = pt.BUILD_AHB_LITE ? ifu_axi_awready_ahb : ifu_axi_awready;
  assign ifu_axi_awid                        = ifu_axi_awid_int;
  assign ifu_axi_awaddr                      = ifu_axi_awaddr_int;
  assign ifu_axi_awregion                    = ifu_axi_awregion_int;
  assign ifu_axi_awlen                       = ifu_axi_awlen_int;
  assign ifu_axi_awsize                      = ifu_axi_awsize_int;
  assign ifu_axi_awburst                     = ifu_axi_awburst_int;
  assign ifu_axi_awlock                      = ifu_axi_awlock_int;
  assign ifu_axi_awcache                     = ifu_axi_awcache_int;
  assign ifu_axi_awprot                      = ifu_axi_awprot_int;
  assign ifu_axi_awqos                       = ifu_axi_awqos_int;
  assign ifu_axi_wvalid                      = ifu_axi_wvalid_int;
  assign ifu_axi_wready_int                  = pt.BUILD_AHB_LITE ? ifu_axi_wready_ahb : ifu_axi_wready;
  assign ifu_axi_wdata                       = ifu_axi_wdata_int;
  assign ifu_axi_wstrb                       = ifu_axi_wstrb_int;
  assign ifu_axi_wlast                       = ifu_axi_wlast_int;
  assign ifu_axi_bvalid_int                  = pt.BUILD_AHB_LITE ? ifu_axi_bvalid_ahb : ifu_axi_bvalid;
  assign ifu_axi_bready                      = ifu_axi_bready_int;
  assign ifu_axi_bresp_int[1:0]              = pt.BUILD_AHB_LITE ? ifu_axi_bresp_ahb[1:0] : ifu_axi_bresp[1:0];
  assign ifu_axi_bid_int[pt.IFU_BUS_TAG-1:0] = pt.BUILD_AHB_LITE ? ifu_axi_bid_ahb[pt.IFU_BUS_TAG-1:0] : ifu_axi_bid[pt.IFU_BUS_TAG-1:0];
  assign ifu_axi_arvalid                     = ifu_axi_arvalid_int;
  assign ifu_axi_arready_int                 = pt.BUILD_AHB_LITE ? ifu_axi_arready_ahb : ifu_axi_arready;
  assign ifu_axi_arid                        = ifu_axi_arid_int;
  assign ifu_axi_araddr                      = ifu_axi_araddr_int;
  assign ifu_axi_arregion                    = ifu_axi_arregion_int;
  assign ifu_axi_arlen                       = ifu_axi_arlen_int;
  assign ifu_axi_arsize                      = ifu_axi_arsize_int;
  assign ifu_axi_arburst                     = ifu_axi_arburst_int;
  assign ifu_axi_arlock                      = ifu_axi_arlock_int;
  assign ifu_axi_arcache                     = ifu_axi_arcache_int;
  assign ifu_axi_arprot                      = ifu_axi_arprot_int;
  assign ifu_axi_arqos                       = ifu_axi_arqos_int;
  assign ifu_axi_rvalid_int                  = pt.BUILD_AHB_LITE ? ifu_axi_rvalid_ahb : ifu_axi_rvalid;
  assign ifu_axi_rready                      = ifu_axi_rready_int;
  assign ifu_axi_rid_int[pt.IFU_BUS_TAG-1:0] = pt.BUILD_AHB_LITE ? ifu_axi_rid_ahb[pt.IFU_BUS_TAG-1:0] : ifu_axi_rid[pt.IFU_BUS_TAG-1:0];
  assign ifu_axi_rdata_int[63:0]             = pt.BUILD_AHB_LITE ? ifu_axi_rdata_ahb[63:0] : ifu_axi_rdata[63:0];
  assign ifu_axi_rresp_int[1:0]              = pt.BUILD_AHB_LITE ? ifu_axi_rresp_ahb[1:0] : ifu_axi_rresp[1:0];
  assign ifu_axi_rlast_int                   = pt.BUILD_AHB_LITE ? ifu_axi_rlast_ahb : ifu_axi_rlast;

  assign sb_axi_awvalid                      = sb_axi_awvalid_int;
  assign sb_axi_awready_int                  = pt.BUILD_AHB_LITE ? sb_axi_awready_ahb : sb_axi_awready;
  assign sb_axi_awid                         = sb_axi_awid_int;
  assign sb_axi_awaddr                       = sb_axi_awaddr_int;
  assign sb_axi_awregion                     = sb_axi_awregion_int;
  assign sb_axi_awlen                        = sb_axi_awlen_int;
  assign sb_axi_awsize                       = sb_axi_awsize_int;
  assign sb_axi_awburst                      = sb_axi_awburst_int;
  assign sb_axi_awlock                       = sb_axi_awlock_int;
  assign sb_axi_awcache                      = sb_axi_awcache_int;
  assign sb_axi_awprot                       = sb_axi_awprot_int;
  assign sb_axi_awqos                        = sb_axi_awqos_int;
  assign sb_axi_wvalid                       = sb_axi_wvalid_int;
  assign sb_axi_wready_int                   = pt.BUILD_AHB_LITE ? sb_axi_wready_ahb : sb_axi_wready;
  assign sb_axi_wdata                        = sb_axi_wdata_int;
  assign sb_axi_wstrb                        = sb_axi_wstrb_int;
  assign sb_axi_wlast                        = sb_axi_wlast_int;
  assign sb_axi_bvalid_int                   = pt.BUILD_AHB_LITE ? sb_axi_bvalid_ahb : sb_axi_bvalid;
  assign sb_axi_bready                       = sb_axi_bready_int;
  assign sb_axi_bresp_int[1:0]               = pt.BUILD_AHB_LITE ? sb_axi_bresp_ahb[1:0] : sb_axi_bresp[1:0];
  assign sb_axi_bid_int[pt.SB_BUS_TAG-1:0]   = pt.BUILD_AHB_LITE ? sb_axi_bid_ahb[pt.SB_BUS_TAG-1:0] : sb_axi_bid[pt.SB_BUS_TAG-1:0];
  assign sb_axi_arvalid                      = sb_axi_arvalid_int;
  assign sb_axi_arready_int                  = pt.BUILD_AHB_LITE ? sb_axi_arready_ahb : sb_axi_arready;
  assign sb_axi_arid                         = sb_axi_arid_int;
  assign sb_axi_araddr                       = sb_axi_araddr_int;
  assign sb_axi_arregion                     = sb_axi_arregion_int;
  assign sb_axi_arlen                        = sb_axi_arlen_int;
  assign sb_axi_arsize                       = sb_axi_arsize_int;
  assign sb_axi_arburst                      = sb_axi_arburst_int;
  assign sb_axi_arlock                       = sb_axi_arlock_int;
  assign sb_axi_arcache                      = sb_axi_arcache_int;
  assign sb_axi_arprot                       = sb_axi_arprot_int;
  assign sb_axi_arqos                        = sb_axi_arqos_int;
  assign sb_axi_rvalid_int                   = pt.BUILD_AHB_LITE ? sb_axi_rvalid_ahb : sb_axi_rvalid;
  assign sb_axi_rready                       = sb_axi_rready_int;
  assign sb_axi_rid_int[pt.SB_BUS_TAG-1:0]   = pt.BUILD_AHB_LITE ? sb_axi_rid_ahb[pt.SB_BUS_TAG-1:0] : sb_axi_rid[pt.SB_BUS_TAG-1:0];
  assign sb_axi_rdata_int[63:0]              = pt.BUILD_AHB_LITE ? sb_axi_rdata_ahb[63:0] : sb_axi_rdata[63:0];
  assign sb_axi_rresp_int[1:0]               = pt.BUILD_AHB_LITE ? sb_axi_rresp_ahb[1:0] : sb_axi_rresp[1:0];
  assign sb_axi_rlast_int                    = pt.BUILD_AHB_LITE ? sb_axi_rlast_ahb : sb_axi_rlast;

  assign dma_axi_awvalid_int                  = pt.BUILD_AHB_LITE ? dma_axi_awvalid_ahb : dma_axi_awvalid;
  assign dma_axi_awready                      = dma_axi_awready_int;
  assign dma_axi_awid_int[pt.DMA_BUS_TAG-1:0] = pt.BUILD_AHB_LITE ? dma_axi_awid_ahb[pt.DMA_BUS_TAG-1:0] : dma_axi_awid[pt.DMA_BUS_TAG-1:0];
  assign dma_axi_awaddr_int[31:0]             = pt.BUILD_AHB_LITE ? dma_axi_awaddr_ahb[31:0] : dma_axi_awaddr[31:0];
  assign dma_axi_awsize_int[2:0]              = pt.BUILD_AHB_LITE ? dma_axi_awsize_ahb[2:0] : dma_axi_awsize[2:0];
  assign dma_axi_awprot_int[2:0]              = pt.BUILD_AHB_LITE ? dma_axi_awprot_ahb[2:0] : dma_axi_awprot[2:0];
  assign dma_axi_awlen_int[7:0]               = pt.BUILD_AHB_LITE ? dma_axi_awlen_ahb[7:0] : dma_axi_awlen[7:0];
  assign dma_axi_awburst_int[1:0]             = pt.BUILD_AHB_LITE ? dma_axi_awburst_ahb[1:0] : dma_axi_awburst[1:0];
  assign dma_axi_wvalid_int                   = pt.BUILD_AHB_LITE ? dma_axi_wvalid_ahb : dma_axi_wvalid;
  assign dma_axi_wready                       = dma_axi_wready_int;
  assign dma_axi_wdata_int[63:0]              = pt.BUILD_AHB_LITE ? dma_axi_wdata_ahb[63:0] : dma_axi_wdata;
  assign dma_axi_wstrb_int[7:0]               = pt.BUILD_AHB_LITE ? dma_axi_wstrb_ahb[7:0] : dma_axi_wstrb[7:0];
  assign dma_axi_wlast_int                    = pt.BUILD_AHB_LITE ? dma_axi_wlast_ahb : dma_axi_wlast;
  assign dma_axi_bvalid                       = dma_axi_bvalid_int;
  assign dma_axi_bready_int                   = pt.BUILD_AHB_LITE ? dma_axi_bready_ahb : dma_axi_bready;
  assign dma_axi_bresp                        = dma_axi_bresp_int;
  assign dma_axi_bid                          = dma_axi_bid_int;
  assign dma_axi_arvalid_int                  = pt.BUILD_AHB_LITE ? dma_axi_arvalid_ahb : dma_axi_arvalid;
  assign dma_axi_arready                      = dma_axi_arready_int;
  assign dma_axi_arid_int[pt.DMA_BUS_TAG-1:0] = pt.BUILD_AHB_LITE ? dma_axi_arid_ahb[pt.DMA_BUS_TAG-1:0] : dma_axi_arid[pt.DMA_BUS_TAG-1:0];
  assign dma_axi_araddr_int[31:0]             = pt.BUILD_AHB_LITE ? dma_axi_araddr_ahb[31:0] : dma_axi_araddr[31:0];
  assign dma_axi_arsize_int[2:0]              = pt.BUILD_AHB_LITE ? dma_axi_arsize_ahb[2:0] : dma_axi_arsize[2:0];
  assign dma_axi_arprot_int[2:0]              = pt.BUILD_AHB_LITE ? dma_axi_arprot_ahb[2:0] : dma_axi_arprot[2:0];
  assign dma_axi_arlen_int[7:0]               = pt.BUILD_AHB_LITE ? dma_axi_arlen_ahb[7:0] : dma_axi_arlen[7:0];
  assign dma_axi_arburst_int[1:0]             = pt.BUILD_AHB_LITE ? dma_axi_arburst_ahb[1:0] : dma_axi_arburst[1:0];
  assign dma_axi_rvalid                       = dma_axi_rvalid_int;
  assign dma_axi_rready_int                   = pt.BUILD_AHB_LITE ? dma_axi_rready_ahb : dma_axi_rready;
  assign dma_axi_rid                          = dma_axi_rid_int;
  assign dma_axi_rdata                        = dma_axi_rdata_int;
  assign dma_axi_rresp                        = dma_axi_rresp_int;
  assign dma_axi_rlast                        = dma_axi_rlast_int;

  if (pt.BUILD_AHB_LITE == 1) begin: Gen_AXI_To_AHB
     // AXI4 -> AHB Gasket for LSU
     axi4_to_ahb #(.pt(pt),
                   .TAG(pt.LSU_BUS_TAG)) lsu_axi4_to_ahb (
       .clk(free_l2clk),
       .free_clk(free_clk),
       .rst_l(core_rst_l),
       .clk_override(dec_tlu_bus_clk_override_int),
       .bus_clk_en(lsu_bus_clk_en),
       .dec_tlu_force_halt(dec_tlu_force_halt_int),
       // AXI Write Channels
       .axi_awvalid(lsu_axi_awvalid),
       .axi_awready(lsu_axi_awready_ahb),
       .axi_awid(lsu_axi_awid[pt.LSU_BUS_TAG-1:0]),
       .axi_awaddr(lsu_axi_awaddr[31:0]),
       .axi_awsize(lsu_axi_awsize[2:0]),
       .axi_awprot(lsu_axi_awprot[2:0]),
       .axi_wvalid(lsu_axi_wvalid),
       .axi_wready(lsu_axi_wready_ahb),
       .axi_wdata(lsu_axi_wdata[63:0]),
       .axi_wstrb(lsu_axi_wstrb[7:0]),
       .axi_wlast(lsu_axi_wlast),
       .axi_bvalid(lsu_axi_bvalid_ahb),
       .axi_bready(lsu_axi_bready),
       .axi_bresp(lsu_axi_bresp_ahb[1:0]),
       .axi_bid(lsu_axi_bid_ahb[pt.LSU_BUS_TAG-1:0]),
       // AXI Read Channels
       .axi_arvalid(lsu_axi_arvalid),
       .axi_arready(lsu_axi_arready_ahb),
       .axi_arid(lsu_axi_arid[pt.LSU_BUS_TAG-1:0]),
       .axi_araddr(lsu_axi_araddr[31:0]),
       .axi_arsize(lsu_axi_arsize[2:0]),
       .axi_arprot(lsu_axi_arprot[2:0]),
       .axi_rvalid(lsu_axi_rvalid_ahb),
       .axi_rready(lsu_axi_rready),
       .axi_rid(lsu_axi_rid_ahb[pt.LSU_BUS_TAG-1:0]),
       .axi_rdata(lsu_axi_rdata_ahb[63:0]),
       .axi_rresp(lsu_axi_rresp_ahb[1:0]),
       .axi_rlast(lsu_axi_rlast_ahb),
       // AHB-LITE signals
       .ahb_haddr(lsu_haddr[31:0]),
       .ahb_hburst(lsu_hburst),
       .ahb_hmastlock(lsu_hmastlock),
       .ahb_hprot(lsu_hprot[3:0]),
       .ahb_hsize(lsu_hsize[2:0]),
       .ahb_htrans(lsu_htrans[1:0]),
       .ahb_hwrite(lsu_hwrite),
       .ahb_hwdata(lsu_hwdata[63:0]),
       .ahb_hrdata(lsu_hrdata[63:0]),
       .ahb_hready(lsu_hready),
       .ahb_hresp(lsu_hresp),
       .*
     );
     axi4_to_ahb #(.pt(pt),
                   .TAG(pt.IFU_BUS_TAG)) ifu_axi4_to_ahb (
       .clk(free_l2clk),
       .free_clk(free_clk),
       .rst_l(core_rst_l),
       .clk_override(dec_tlu_bus_clk_override_int),
       .bus_clk_en(ifu_bus_clk_en),
       .dec_tlu_force_halt(dec_tlu_force_halt_int),
        // AHB-Lite signals
       .ahb_haddr(haddr[31:0]),
       .ahb_hburst(hburst),
       .ahb_hmastlock(hmastlock),
       .ahb_hprot(hprot[3:0]),
       .ahb_hsize(hsize[2:0]),
       .ahb_htrans(htrans[1:0]),
       .ahb_hwrite(hwrite),
       .ahb_hwdata(hwdata_nc[63:0]),
       .ahb_hrdata(hrdata[63:0]),
       .ahb_hready(hready),
       .ahb_hresp(hresp),
       // AXI Write Channels
       .axi_awvalid(ifu_axi_awvalid),
       .axi_awready(ifu_axi_awready_ahb),
       .axi_awid(ifu_axi_awid[pt.IFU_BUS_TAG-1:0]),
       .axi_awaddr(ifu_axi_awaddr[31:0]),
       .axi_awsize(ifu_axi_awsize[2:0]),
       .axi_awprot(ifu_axi_awprot[2:0]),
       .axi_wvalid(ifu_axi_wvalid),
       .axi_wready(ifu_axi_wready_ahb),
       .axi_wdata(ifu_axi_wdata[63:0]),
       .axi_wstrb(ifu_axi_wstrb[7:0]),
       .axi_wlast(ifu_axi_wlast),
       .axi_bvalid(ifu_axi_bvalid_ahb),
       .axi_bready(1'b1),
       .axi_bresp(ifu_axi_bresp_ahb[1:0]),
       .axi_bid(ifu_axi_bid_ahb[pt.IFU_BUS_TAG-1:0]),
       // AXI Read Channels
       .axi_arvalid(ifu_axi_arvalid),
       .axi_arready(ifu_axi_arready_ahb),
       .axi_arid(ifu_axi_arid[pt.IFU_BUS_TAG-1:0]),
       .axi_araddr(ifu_axi_araddr[31:0]),
       .axi_arsize(ifu_axi_arsize[2:0]),
       .axi_arprot(ifu_axi_arprot[2:0]),
       .axi_rvalid(ifu_axi_rvalid_ahb),
       .axi_rready(ifu_axi_rready),
       .axi_rid(ifu_axi_rid_ahb[pt.IFU_BUS_TAG-1:0]),
       .axi_rdata(ifu_axi_rdata_ahb[63:0]),
       .axi_rresp(ifu_axi_rresp_ahb[1:0]),
       .axi_rlast(ifu_axi_rlast_ahb),
       .*
     );
     // AXI4 -> AHB Gasket for System Bus
     axi4_to_ahb #(.pt(pt),
                   .TAG(pt.SB_BUS_TAG)) sb_axi4_to_ahb (
       .clk(free_l2clk),
       .free_clk(free_clk),
       .rst_l(dbg_rst_l),
       .clk_override(dec_tlu_bus_clk_override_int),
       .bus_clk_en(dbg_bus_clk_en),
       .dec_tlu_force_halt(1'b0),
       // AXI Write Channels
       .axi_awvalid(sb_axi_awvalid),
       .axi_awready(sb_axi_awready_ahb),
       .axi_awid(sb_axi_awid[pt.SB_BUS_TAG-1:0]),
       .axi_awaddr(sb_axi_awaddr[31:0]),
       .axi_awsize(sb_axi_awsize[2:0]),
       .axi_awprot(sb_axi_awprot[2:0]),
       .axi_wvalid(sb_axi_wvalid),
       .axi_wready(sb_axi_wready_ahb),
       .axi_wdata(sb_axi_wdata[63:0]),
       .axi_wstrb(sb_axi_wstrb[7:0]),
       .axi_wlast(sb_axi_wlast),
       .axi_bvalid(sb_axi_bvalid_ahb),
       .axi_bready(sb_axi_bready),
       .axi_bresp(sb_axi_bresp_ahb[1:0]),
       .axi_bid(sb_axi_bid_ahb[pt.SB_BUS_TAG-1:0]),
       // AXI Read Channels
       .axi_arvalid(sb_axi_arvalid),
       .axi_arready(sb_axi_arready_ahb),
       .axi_arid(sb_axi_arid[pt.SB_BUS_TAG-1:0]),
       .axi_araddr(sb_axi_araddr[31:0]),
       .axi_arsize(sb_axi_arsize[2:0]),
       .axi_arprot(sb_axi_arprot[2:0]),
       .axi_rvalid(sb_axi_rvalid_ahb),
       .axi_rready(sb_axi_rready),
       .axi_rid(sb_axi_rid_ahb[pt.SB_BUS_TAG-1:0]),
       .axi_rdata(sb_axi_rdata_ahb[63:0]),
       .axi_rresp(sb_axi_rresp_ahb[1:0]),
       .axi_rlast(sb_axi_rlast_ahb),
       // AHB-LITE signals
       .ahb_haddr(sb_haddr[31:0]),
       .ahb_hburst(sb_hburst),
       .ahb_hmastlock(sb_hmastlock),
       .ahb_hprot(sb_hprot[3:0]),
       .ahb_hsize(sb_hsize[2:0]),
       .ahb_htrans(sb_htrans[1:0]),
       .ahb_hwrite(sb_hwrite),
       .ahb_hwdata(sb_hwdata[63:0]),
       .ahb_hrdata(sb_hrdata[63:0]),
       .ahb_hready(sb_hready),
       .ahb_hresp(sb_hresp),

       .*
     );
     //AHB -> AXI4 Gasket for DMA
     ahb_to_axi4 #(.pt(pt),
                   .TAG(pt.DMA_BUS_TAG)) dma_ahb_to_axi4 (
       .clk(free_l2clk),
       .rst_l(core_rst_l),
       .clk_override(dec_tlu_bus_clk_override_int),
       .bus_clk_en(dma_bus_clk_en),
       // AXI Write Channels
       .axi_awvalid(dma_axi_awvalid_ahb),
       .axi_awready(dma_axi_awready),
       .axi_awid(dma_axi_awid_ahb[pt.DMA_BUS_TAG-1:0]),
       .axi_awaddr(dma_axi_awaddr_ahb[31:0]),
       .axi_awsize(dma_axi_awsize_ahb[2:0]),
       .axi_awprot(dma_axi_awprot_ahb[2:0]),
       .axi_awlen(dma_axi_awlen_ahb[7:0]),
       .axi_awburst(dma_axi_awburst_ahb[1:0]),
       .axi_wvalid(dma_axi_wvalid_ahb),
       .axi_wready(dma_axi_wready),
       .axi_wdata(dma_axi_wdata_ahb[63:0]),
       .axi_wstrb(dma_axi_wstrb_ahb[7:0]),
       .axi_wlast(dma_axi_wlast_ahb),
       .axi_bvalid(dma_axi_bvalid),
       .axi_bready(dma_axi_bready_ahb),
       .axi_bresp(dma_axi_bresp[1:0]),
       .axi_bid(dma_axi_bid[pt.DMA_BUS_TAG-1:0]),
       // AXI Read Channels
       .axi_arvalid(dma_axi_arvalid_ahb),
       .axi_arready(dma_axi_arready),
       .axi_arid(dma_axi_arid_ahb[pt.DMA_BUS_TAG-1:0]),
       .axi_araddr(dma_axi_araddr_ahb[31:0]),
       .axi_arsize(dma_axi_arsize_ahb[2:0]),
       .axi_arprot(dma_axi_arprot_ahb[2:0]),
       .axi_arlen(dma_axi_arlen_ahb[7:0]),
       .axi_arburst(dma_axi_arburst_ahb[1:0]),
       .axi_rvalid(dma_axi_rvalid),
       .axi_rready(dma_axi_rready_ahb),
       .axi_rid(dma_axi_rid[pt.DMA_BUS_TAG-1:0]),
       .axi_rdata(dma_axi_rdata[63:0]),
       .axi_rresp(dma_axi_rresp[1:0]),
        // AHB signals
       .ahb_haddr(dma_haddr[31:0]),
       .ahb_hburst(dma_hburst),
       .ahb_hmastlock(dma_hmastlock),
       .ahb_hprot(dma_hprot[3:0]),
       .ahb_hsize(dma_hsize[2:0]),
       .ahb_htrans(dma_htrans[1:0]),
       .ahb_hwrite(dma_hwrite),
       .ahb_hwdata(dma_hwdata[63:0]),
       .ahb_hrdata(dma_hrdata[63:0]),
       .ahb_hreadyout(dma_hreadyout),
       .ahb_hresp(dma_hresp),
       .ahb_hreadyin(dma_hreadyin),
       .ahb_hsel(dma_hsel),
       .*
     );

  end else begin : g_tie_unused_ahb
    always_comb begin
      haddr = '0;
      hburst = '0;
      hmastlock = '0;
      hprot = '0;
      hsize = '0;
      htrans = '0;
      hwrite = '0;

      lsu_haddr = '0;
      lsu_hburst = '0;
      lsu_hmastlock = '0;
      lsu_hprot = '0;
      lsu_hsize = '0;
      lsu_htrans = '0;
      lsu_hwrite = '0;
      lsu_hwdata = '0;

      sb_haddr = '0;
      sb_hburst = '0;
      sb_hmastlock = '0;
      sb_hprot = '0;
      sb_hsize = '0;
      sb_htrans = '0;
      sb_hwrite = '0;
      sb_hwdata = '0;

      dma_hrdata = '0;
      dma_hreadyout = '0;
      dma_hresp = '0;
    end
  end

  if  (pt.BUILD_AHB_LITE == 1) begin
`ifdef RV_ASSERT_ON
    property ahb_trxn_aligned;
      @(posedge clk) disable iff(~rst_l) (lsu_htrans[1:0] != 2'b0)  |-> ((lsu_hsize[2:0] == 3'h0)                             |
                                                                        ((lsu_hsize[2:0] == 3'h1) & (lsu_haddr[0] == 1'b0))   |
                                                                        ((lsu_hsize[2:0] == 3'h2) & (lsu_haddr[1:0] == 2'b0)) |
                                                                        ((lsu_hsize[2:0] == 3'h3) & (lsu_haddr[2:0] == 3'b0)));
    endproperty
    assert_ahb_trxn_aligned: assert property (ahb_trxn_aligned) else
    $display("Assertion ahb_trxn_aligned failed: lsu_htrans=2'h%h, lsu_hsize=3'h%h, lsu_haddr=32'h%h",lsu_htrans[1:0], lsu_hsize[2:0], lsu_haddr[31:0]);

    property dma_trxn_aligned;
      @(posedge clk) disable iff(~rst_l) (dma_htrans[1:0] != 2'b0)  |-> ((dma_hsize[2:0] == 3'h0)                             |
                                                                        ((dma_hsize[2:0] == 3'h1) & (dma_haddr[0] == 1'b0))   |
                                                                        ((dma_hsize[2:0] == 3'h2) & (dma_haddr[1:0] == 2'b0)) |
                                                                        ((dma_hsize[2:0] == 3'h3) & (dma_haddr[2:0] == 3'b0)));
    endproperty
`endif
  end // if (pt.BUILD_AHB_LITE == 1)

endmodule
