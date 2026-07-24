// Copyright 2026 Antmicro <www.antmicro.com>
// //
// // SPDX-License-Identifier: Apache-2.0
//
module el2_tmr_axi
  import el2_pkg::*;
  import el2_mubi_pkg::*;
  import el2_lockstep_pkg::*;
#(
    `include "el2_param.vh"
) (
    //-------------------------- LSU AXI signals--------------------------
    // AXI Write Channels
    output logic                            lsu_axi_awvalid_int,
    input  logic                            lsu_axi_awready_int,
    output logic [pt.LSU_BUS_TAG-1:0]       lsu_axi_awid_int,
    output logic [31:0]                     lsu_axi_awaddr_int,
    output logic [3:0]                      lsu_axi_awregion_int,
    /* exclude signals that are tied to constant value in el2_lsu_bus_buffer.sv */
    /*pragma coverage off*/
    output logic [7:0]                      lsu_axi_awlen_int,
    /*pragma coverage on*/
    output logic [2:0]                      lsu_axi_awsize_int,
    /* exclude signals that are tied to constant value in el2_lsu_bus_buffer.sv */
    /*pragma coverage off*/
    output logic [1:0]                      lsu_axi_awburst_int,
    output logic                            lsu_axi_awlock_int,
    /*pragma coverage on*/
    output logic [3:0]                      lsu_axi_awcache_int,
    /* exclude signals that are tied to constant value in el2_lsu_bus_buffer.sv */
    /*pragma coverage off*/
    output logic [2:0]                      lsu_axi_awprot_int,
    output logic [3:0]                      lsu_axi_awqos_int,
    /*pragma coverage on*/

    output logic                            lsu_axi_wvalid_int,
    input  logic                            lsu_axi_wready_int,
    output logic [63:0]                     lsu_axi_wdata_int,
    output logic [7:0]                      lsu_axi_wstrb_int,
    output logic                            lsu_axi_wlast_int,

    input  logic                            lsu_axi_bvalid_int,
    /* exclude signals that are tied to constant value in el2_lsu_bus_buffer.sv */
    /*pragma coverage off*/
    output logic                            lsu_axi_bready_int,
    /*pragma coverage on*/
    input  logic [1:0]                      lsu_axi_bresp_int,
    input  logic [pt.LSU_BUS_TAG-1:0]       lsu_axi_bid_int,

    // AXI Read Channels
    output logic                            lsu_axi_arvalid_int,
    input  logic                            lsu_axi_arready_int,
    output logic [pt.LSU_BUS_TAG-1:0]       lsu_axi_arid_int,
    output logic [31:0]                     lsu_axi_araddr_int,
    output logic [3:0]                      lsu_axi_arregion_int,
    /* exclude signals that are tied to constant value in el2_lsu_bus_buffer.sv */
    /*pragma coverage off*/
    output logic [7:0]                      lsu_axi_arlen_int,
    /*pragma coverage on*/
    output logic [2:0]                      lsu_axi_arsize_int,
    /* exclude signals that are tied to constant value in el2_lsu_bus_buffer.sv */
    /*pragma coverage off*/
    output logic [1:0]                      lsu_axi_arburst_int,
    output logic                            lsu_axi_arlock_int,
    /*pragma coverage on*/
    output logic [3:0]                      lsu_axi_arcache_int,
    /* exclude signals that are tied to constant value in el2_lsu_bus_buffer.sv */
    /*pragma coverage off*/
    output logic [2:0]                      lsu_axi_arprot_int,
    output logic [3:0]                      lsu_axi_arqos_int,
    /*pragma coverage on*/

    input  logic                            lsu_axi_rvalid_int,
    /* exclude signals that are tied to constant value in el2_lsu_bus_buffer.sv */
    /*pragma coverage off*/
    output logic                            lsu_axi_rready_int,
    /*pragma coverage on*/
    input  logic [pt.LSU_BUS_TAG-1:0]       lsu_axi_rid_int,
    input  logic [63:0]                     lsu_axi_rdata_int,
    input  logic [1:0]                      lsu_axi_rresp_int,
    input  logic                            lsu_axi_rlast_int,

    //-------------------------- IFU AXI signals--------------------------
    // AXI Write Channels
    /* exclude signals that are tied to constant value in el2_ifu_mem_ctl.sv
       IFU does not use AXI write channel */
    /*pragma coverage off*/
    output logic                            ifu_axi_awvalid_int,
    input  logic                            ifu_axi_awready_int,
    output logic [pt.IFU_BUS_TAG-1:0]       ifu_axi_awid_int,
    output logic [31:0]                     ifu_axi_awaddr_int,
    output logic [3:0]                      ifu_axi_awregion_int,
    output logic [7:0]                      ifu_axi_awlen_int,
    output logic [2:0]                      ifu_axi_awsize_int,
    output logic [1:0]                      ifu_axi_awburst_int,
    output logic                            ifu_axi_awlock_int,
    output logic [3:0]                      ifu_axi_awcache_int,
    output logic [2:0]                      ifu_axi_awprot_int,
    output logic [3:0]                      ifu_axi_awqos_int,

    output logic                            ifu_axi_wvalid_int,
    input  logic                            ifu_axi_wready_int,
    output logic [63:0]                     ifu_axi_wdata_int,
    output logic [7:0]                      ifu_axi_wstrb_int,
    output logic                            ifu_axi_wlast_int,

    input  logic                            ifu_axi_bvalid_int,
    output logic                            ifu_axi_bready_int,
    input  logic [1:0]                      ifu_axi_bresp_int,
    input  logic [pt.IFU_BUS_TAG-1:0]       ifu_axi_bid_int,
    /*pragma coverage on*/

    // AXI Read Channels
    output logic                            ifu_axi_arvalid_int,
    input  logic                            ifu_axi_arready_int,
    output logic [pt.IFU_BUS_TAG-1:0]       ifu_axi_arid_int,
    output logic [31:0]                     ifu_axi_araddr_int,
    output logic [3:0]                      ifu_axi_arregion_int,
    /* exclude signals that are tied to constant value in el2_ifu_mem_ctl.sv */
    /*pragma coverage off*/
    output logic [7:0]                      ifu_axi_arlen_int,
    output logic [2:0]                      ifu_axi_arsize_int,
    output logic [1:0]                      ifu_axi_arburst_int,
    output logic                            ifu_axi_arlock_int,
    output logic [3:0]                      ifu_axi_arcache_int,
    output logic [2:0]                      ifu_axi_arprot_int,
    output logic [3:0]                      ifu_axi_arqos_int,
    /*pragma coverage on*/

    input  logic                            ifu_axi_rvalid_int,
    /* exclude signals that are tied to constant value in el2_ifu_mem_ctl.sv */
    /*pragma coverage off*/
    output logic                            ifu_axi_rready_int,
    /*pragma coverage on*/
    input  logic [pt.IFU_BUS_TAG-1:0]       ifu_axi_rid_int,
    input  logic [63:0]                     ifu_axi_rdata_int,
    input  logic [1:0]                      ifu_axi_rresp_int,
    input  logic                            ifu_axi_rlast_int,

    //-------------------------- SB AXI signals--------------------------
    // AXI Write Channels
    output logic                            sb_axi_awvalid_int,
    input  logic                            sb_axi_awready_int,
    /* exclude signals that are tied to constant value in dbg/el2_dbg.sv */
    /*pragma coverage off*/
    output logic [pt.SB_BUS_TAG-1:0]        sb_axi_awid_int,
    /*pragma coverage on*/
    output logic [31:0]                     sb_axi_awaddr_int,
    output logic [3:0]                      sb_axi_awregion_int,
    /* exclude signals that are tied to constant value in dbg/el2_dbg.sv */
    /*pragma coverage off*/
    output logic [7:0]                      sb_axi_awlen_int,
    /*pragma coverage on*/
    output logic [2:0]                      sb_axi_awsize_int,
    /* exclude signals that are tied to constant value in dbg/el2_dbg.sv */
    /*pragma coverage off*/
    output logic [1:0]                      sb_axi_awburst_int,
    output logic                            sb_axi_awlock_int,
    output logic [3:0]                      sb_axi_awcache_int,
    output logic [2:0]                      sb_axi_awprot_int,
    output logic [3:0]                      sb_axi_awqos_int,
    /*pragma coverage on*/

    output logic                            sb_axi_wvalid_int,
    input  logic                            sb_axi_wready_int,
    output logic [63:0]                     sb_axi_wdata_int,
    output logic [7:0]                      sb_axi_wstrb_int,
    output logic                            sb_axi_wlast_int,

    input  logic                            sb_axi_bvalid_int,
    output logic                            sb_axi_bready_int,
    input  logic [1:0]                      sb_axi_bresp_int,
    input  logic [pt.SB_BUS_TAG-1:0]        sb_axi_bid_int,

    // AXI Read Channels
    output logic                            sb_axi_arvalid_int,
    input  logic                            sb_axi_arready_int,
    /* exclude signals that are tied to constant value in dbg/el2_dbg.sv */
    /*pragma coverage off*/
    output logic [pt.SB_BUS_TAG-1:0]        sb_axi_arid_int,
    /*pragma coverage on*/
    output logic [31:0]                     sb_axi_araddr_int,
    output logic [3:0]                      sb_axi_arregion_int,
    /* exclude signals that are tied to constant value in dbg/el2_dbg.sv */
    /*pragma coverage off*/
    output logic [7:0]                      sb_axi_arlen_int,
    /*pragma coverage on*/
    output logic [2:0]                      sb_axi_arsize_int,
    /* exclude signals that are tied to constant value in dbg/el2_dbg.sv */
    /*pragma coverage off*/
    output logic [1:0]                      sb_axi_arburst_int,
    output logic                            sb_axi_arlock_int,
    output logic [3:0]                      sb_axi_arcache_int,
    output logic [2:0]                      sb_axi_arprot_int,
    output logic [3:0]                      sb_axi_arqos_int,
    /*pragma coverage on*/

    input  logic                            sb_axi_rvalid_int,
    /* exclude signals that are tied to constant value in dbg/el2_dbg.sv */
    /*pragma coverage off*/
    output logic                            sb_axi_rready_int,
    /*pragma coverage on*/
    input  logic [pt.SB_BUS_TAG-1:0]        sb_axi_rid_int,
    input  logic [63:0]                     sb_axi_rdata_int,
    input  logic [1:0]                      sb_axi_rresp_int,
    input  logic                            sb_axi_rlast_int,

    //-------------------------- DMA AXI signals--------------------------
    // AXI Write Channels
    input  logic                         dma_axi_awvalid_int,
    output logic                         dma_axi_awready_int,
    input  logic [pt.DMA_BUS_TAG-1:0]    dma_axi_awid_int,
    input  logic [31:0]                  dma_axi_awaddr_int,
    input  logic [2:0]                   dma_axi_awsize_int,
    input  logic [2:0]                   dma_axi_awprot_int,
    input  logic [7:0]                   dma_axi_awlen_int,
    input  logic [1:0]                   dma_axi_awburst_int,

    input  logic                         dma_axi_wvalid_int,
    output logic                         dma_axi_wready_int,
    input  logic [63:0]                  dma_axi_wdata_int,
    input  logic [7:0]                   dma_axi_wstrb_int,
    input  logic                         dma_axi_wlast_int,

    output logic                         dma_axi_bvalid_int,
    input  logic                         dma_axi_bready_int,
    output logic [1:0]                   dma_axi_bresp_int,
    output logic [pt.DMA_BUS_TAG-1:0]    dma_axi_bid_int,

    // AXI Read Channels
    input  logic                         dma_axi_arvalid_int,
    output logic                         dma_axi_arready_int,
    input  logic [pt.DMA_BUS_TAG-1:0]    dma_axi_arid_int,
    input  logic [31:0]                  dma_axi_araddr_int,
    input  logic [2:0]                   dma_axi_arsize_int,
    input  logic [2:0]                   dma_axi_arprot_int,
    input  logic [7:0]                   dma_axi_arlen_int,
    input  logic [1:0]                   dma_axi_arburst_int,

    output logic                         dma_axi_rvalid_int,
    input  logic                         dma_axi_rready_int,
    output logic [pt.DMA_BUS_TAG-1:0]    dma_axi_rid_int,
    output logic [63:0]                  dma_axi_rdata_int,
    output logic [1:0]                   dma_axi_rresp_int,
    output logic                         dma_axi_rlast_int,
    //-------------------------- TMR VEER Signal--------------------------
    //-------------------------- LSU AXI signals--------------------------
    // AXI Write Channels
    input  logic                      lsu_axi_awvalid_veer[3],
    output logic                      lsu_axi_awready_veer[3],
    input  logic [pt.LSU_BUS_TAG-1:0] lsu_axi_awid_veer[3],
    input  logic [31:0]               lsu_axi_awaddr_veer[3],
    input  logic [3:0]                lsu_axi_awregion_veer[3],
    input  logic [7:0]                lsu_axi_awlen_veer[3],
    input  logic [2:0]                lsu_axi_awsize_veer[3],
    input  logic [1:0]                lsu_axi_awburst_veer[3],
    input  logic                      lsu_axi_awlock_veer[3],
    input  logic [3:0]                lsu_axi_awcache_veer[3],
    input  logic [2:0]                lsu_axi_awprot_veer[3],
    input  logic [3:0]                lsu_axi_awqos_veer[3],

    input  logic                      lsu_axi_wvalid_veer[3],
    output logic                      lsu_axi_wready_veer[3],
    input  logic [63:0]               lsu_axi_wdata_veer[3],
    input  logic [7:0]                lsu_axi_wstrb_veer[3],
    input  logic                      lsu_axi_wlast_veer[3],

    output logic                      lsu_axi_bvalid_veer[3],
    input  logic                      lsu_axi_bready_veer[3],
    output logic [1:0]                lsu_axi_bresp_veer[3],
    output logic [pt.LSU_BUS_TAG-1:0] lsu_axi_bid_veer[3],

    // AXI Read Channels
    input  logic                      lsu_axi_arvalid_veer[3],
    output logic                      lsu_axi_arready_veer[3],
    input  logic [pt.LSU_BUS_TAG-1:0] lsu_axi_arid_veer[3],
    input  logic [31:0]               lsu_axi_araddr_veer[3],
    input  logic [3:0]                lsu_axi_arregion_veer[3],
    input  logic [7:0]                lsu_axi_arlen_veer[3],
    input  logic [2:0]                lsu_axi_arsize_veer[3],
    input  logic [1:0]                lsu_axi_arburst_veer[3],
    input  logic                      lsu_axi_arlock_veer[3],
    input  logic [3:0]                lsu_axi_arcache_veer[3],
    input  logic [2:0]                lsu_axi_arprot_veer[3],
    input  logic [3:0]                lsu_axi_arqos_veer[3],

    output logic                      lsu_axi_rvalid_veer[3],
    input  logic                      lsu_axi_rready_veer[3],
    output logic [pt.LSU_BUS_TAG-1:0] lsu_axi_rid_veer[3],
    output logic [63:0]               lsu_axi_rdata_veer[3],
    output logic [1:0]                lsu_axi_rresp_veer[3],
    output logic                      lsu_axi_rlast_veer[3],

    //-------------------------- IFU AXI signals--------------------------
    // AXI Write Channels
    input  logic                      ifu_axi_awvalid_veer[3],
    output logic                      ifu_axi_awready_veer[3],
    input  logic [pt.IFU_BUS_TAG-1:0] ifu_axi_awid_veer[3],
    input  logic [31:0]               ifu_axi_awaddr_veer[3],
    input  logic [3:0]                ifu_axi_awregion_veer[3],
    input  logic [7:0]                ifu_axi_awlen_veer[3],
    input  logic [2:0]                ifu_axi_awsize_veer[3],
    input  logic [1:0]                ifu_axi_awburst_veer[3],
    input  logic                      ifu_axi_awlock_veer[3],
    input  logic [3:0]                ifu_axi_awcache_veer[3],
    input  logic [2:0]                ifu_axi_awprot_veer[3],
    input  logic [3:0]                ifu_axi_awqos_veer[3],

    input  logic                      ifu_axi_wvalid_veer[3],
    output logic                      ifu_axi_wready_veer[3],
    input  logic [63:0]               ifu_axi_wdata_veer[3],
    input  logic [7:0]                ifu_axi_wstrb_veer[3],
    input  logic                      ifu_axi_wlast_veer[3],

    output logic                      ifu_axi_bvalid_veer[3],
    input  logic                      ifu_axi_bready_veer[3],
    output logic [1:0]                ifu_axi_bresp_veer[3],
    output logic [pt.IFU_BUS_TAG-1:0] ifu_axi_bid_veer[3],

    // AXI Read Channels
    input  logic                      ifu_axi_arvalid_veer[3],
    output logic                      ifu_axi_arready_veer[3],
    input  logic [pt.IFU_BUS_TAG-1:0] ifu_axi_arid_veer[3],
    input  logic [31:0]               ifu_axi_araddr_veer[3],
    input  logic [3:0]                ifu_axi_arregion_veer[3],
    input  logic [7:0]                ifu_axi_arlen_veer[3],
    input  logic [2:0]                ifu_axi_arsize_veer[3],
    input  logic [1:0]                ifu_axi_arburst_veer[3],
    input  logic                      ifu_axi_arlock_veer[3],
    input  logic [3:0]                ifu_axi_arcache_veer[3],
    input  logic [2:0]                ifu_axi_arprot_veer[3],
    input  logic [3:0]                ifu_axi_arqos_veer[3],

    output logic                      ifu_axi_rvalid_veer[3],
    input  logic                      ifu_axi_rready_veer[3],
    output logic [pt.IFU_BUS_TAG-1:0] ifu_axi_rid_veer[3],
    output logic [63:0]               ifu_axi_rdata_veer[3],
    output logic [1:0]                ifu_axi_rresp_veer[3],
    output logic                      ifu_axi_rlast_veer[3],

    //-------------------------- SB AXI signals--------------------------
    // AXI Write Channels
    input  logic                     sb_axi_awvalid_veer[3],
    output logic                     sb_axi_awready_veer[3],
    input  logic [pt.SB_BUS_TAG-1:0] sb_axi_awid_veer[3],
    input  logic [31:0]              sb_axi_awaddr_veer[3],
    input  logic [3:0]               sb_axi_awregion_veer[3],
    input  logic [7:0]               sb_axi_awlen_veer[3],
    input  logic [2:0]               sb_axi_awsize_veer[3],
    input  logic [1:0]               sb_axi_awburst_veer[3],
    input  logic                     sb_axi_awlock_veer[3],
    input  logic [3:0]               sb_axi_awcache_veer[3],
    input  logic [2:0]               sb_axi_awprot_veer[3],
    input  logic [3:0]               sb_axi_awqos_veer[3],

    input  logic                     sb_axi_wvalid_veer[3],
    output logic                     sb_axi_wready_veer[3],
    input  logic [63:0]              sb_axi_wdata_veer[3],
    input  logic [7:0]               sb_axi_wstrb_veer[3],
    input  logic                     sb_axi_wlast_veer[3],

    output logic                     sb_axi_bvalid_veer[3],
    input  logic                     sb_axi_bready_veer[3],
    output logic [1:0]               sb_axi_bresp_veer[3],
    output logic [pt.SB_BUS_TAG-1:0] sb_axi_bid_veer[3],

    // AXI Read Channels
    input  logic                     sb_axi_arvalid_veer[3],
    output logic                     sb_axi_arready_veer[3],
    input  logic [pt.SB_BUS_TAG-1:0] sb_axi_arid_veer[3],
    input  logic [31:0]              sb_axi_araddr_veer[3],
    input  logic [3:0]               sb_axi_arregion_veer[3],
    input  logic [7:0]               sb_axi_arlen_veer[3],
    input  logic [2:0]               sb_axi_arsize_veer[3],
    input  logic [1:0]               sb_axi_arburst_veer[3],
    input  logic                     sb_axi_arlock_veer[3],
    input  logic [3:0]               sb_axi_arcache_veer[3],
    input  logic [2:0]               sb_axi_arprot_veer[3],
    input  logic [3:0]               sb_axi_arqos_veer[3],

    output logic                     sb_axi_rvalid_veer[3],
    input  logic                     sb_axi_rready_veer[3],
    output logic [pt.SB_BUS_TAG-1:0] sb_axi_rid_veer[3],
    output logic [63:0]              sb_axi_rdata_veer[3],
    output logic [1:0]               sb_axi_rresp_veer[3],
    output logic                     sb_axi_rlast_veer[3],

    //-------------------------- DMA AXI signals--------------------------
    // AXI Write Channels
    output logic                      dma_axi_awvalid_veer[3],
    input  logic                      dma_axi_awready_veer[3],
    output logic [pt.DMA_BUS_TAG-1:0] dma_axi_awid_veer[3],
    output logic [31:0]               dma_axi_awaddr_veer[3],
    output logic [2:0]                dma_axi_awsize_veer[3],
    output logic [2:0]                dma_axi_awprot_veer[3],
    output logic [7:0]                dma_axi_awlen_veer[3],
    output logic [1:0]                dma_axi_awburst_veer[3],

    output logic                      dma_axi_wvalid_veer[3],
    input  logic                      dma_axi_wready_veer[3],
    output logic [63:0]               dma_axi_wdata_veer[3],
    output logic [7:0]                dma_axi_wstrb_veer[3],
    output logic                      dma_axi_wlast_veer[3],

    input  logic                      dma_axi_bvalid_veer[3],
    output logic                      dma_axi_bready_veer[3],
    input  logic [1:0]                dma_axi_bresp_veer[3],
    input  logic [pt.DMA_BUS_TAG-1:0] dma_axi_bid_veer[3],

    // AXI Read Channels
    output logic                      dma_axi_arvalid_veer[3],
    input  logic                      dma_axi_arready_veer[3],
    output logic [pt.DMA_BUS_TAG-1:0] dma_axi_arid_veer[3],
    output logic [31:0]               dma_axi_araddr_veer[3],
    output logic [2:0]                dma_axi_arsize_veer[3],
    output logic [2:0]                dma_axi_arprot_veer[3],
    output logic [7:0]                dma_axi_arlen_veer[3],
    output logic [1:0]                dma_axi_arburst_veer[3],

    input  logic                      dma_axi_rvalid_veer[3],
    output logic                      dma_axi_rready_veer[3],
    input  logic [pt.DMA_BUS_TAG-1:0] dma_axi_rid_veer[3],
    input  logic [63:0]               dma_axi_rdata_veer[3],
    input  logic [1:0]                dma_axi_rresp_veer[3],
    input  logic                      dma_axi_rlast_veer[3]
);

//TODO: Change it to use voters
  always_comb begin
    // Propagate response to Cores
    for (int i=0;i < 3; i+=1) begin
      lsu_axi_awready_veer[i] = lsu_axi_awready_int;
      lsu_axi_wready_veer[i] = lsu_axi_wready_int;
      lsu_axi_bvalid_veer[i] = lsu_axi_bvalid_int;
      lsu_axi_bresp_veer[i] = lsu_axi_bresp_int;
      lsu_axi_bid_veer[i] = lsu_axi_bid_int;
      lsu_axi_arready_veer[i] = lsu_axi_arready_int;
      lsu_axi_rvalid_veer[i] = lsu_axi_rvalid_int;
      lsu_axi_rid_veer[i] = lsu_axi_rid_int;
      lsu_axi_rdata_veer[i] = lsu_axi_rdata_int;
      lsu_axi_rresp_veer[i] = lsu_axi_rresp_int;
      lsu_axi_rlast_veer[i] = lsu_axi_rlast_int;

      ifu_axi_awready_veer[i] = ifu_axi_awready_int;
      ifu_axi_wready_veer[i] = ifu_axi_wready_int;
      ifu_axi_bvalid_veer[i] = ifu_axi_bvalid_int;
      ifu_axi_bvalid_veer[i] = ifu_axi_bvalid_int;
      ifu_axi_arready_veer[i] = ifu_axi_arready_int;
      ifu_axi_rvalid_veer[i] = ifu_axi_rvalid_int;
      ifu_axi_rid_veer[i] = ifu_axi_rid_int;
      ifu_axi_rdata_veer[i] = ifu_axi_rdata_int;
      ifu_axi_rresp_veer[i] = ifu_axi_rresp_int;
      ifu_axi_rlast_veer[i] = ifu_axi_rlast_int;

      sb_axi_awready_veer[i] = sb_axi_awready_int;
      sb_axi_wready_veer[i] = sb_axi_wready_int;
      sb_axi_bvalid_veer[i] = sb_axi_bvalid_int;
      sb_axi_bresp_veer[i] = sb_axi_bresp_int;
      sb_axi_bid_veer[i] = sb_axi_bid_int;
      sb_axi_arready_veer[i] = sb_axi_arready_int;
      sb_axi_rvalid_veer[i] = sb_axi_rvalid_int;
      sb_axi_rid_veer[i] = sb_axi_rid_int;
      sb_axi_rdata_veer[i] = sb_axi_rdata_int;
      sb_axi_rresp_veer[i] = sb_axi_rresp_int;
      sb_axi_rlast_veer[i] = sb_axi_rlast_int;

      dma_axi_awvalid_veer[i] = dma_axi_awvalid_int;
      dma_axi_awid_veer[i] = dma_axi_awid_int;
      dma_axi_awaddr_veer[i] = dma_axi_awaddr_int;
      dma_axi_awsize_veer[i] = dma_axi_awsize_int;
      dma_axi_awprot_veer[i] = dma_axi_awprot_int;
      dma_axi_awlen_veer[i] = dma_axi_awlen_int;
      dma_axi_awburst_veer[i] = dma_axi_awburst_int;
      dma_axi_wvalid_veer[i] = dma_axi_wvalid_int;
      dma_axi_wdata_veer[i] = dma_axi_wdata_int;
      dma_axi_wstrb_veer[i] = dma_axi_wstrb_int;
      dma_axi_wlast_veer[i] = dma_axi_wlast_int;
      dma_axi_bready_veer[i] = dma_axi_bready_int;
      dma_axi_arvalid_veer[i] = dma_axi_arvalid_int;
      dma_axi_arid_veer[i] = dma_axi_arid_int;
      dma_axi_araddr_veer[i] = dma_axi_araddr_int;
      dma_axi_arsize_veer[i] = dma_axi_arsize_int;
      dma_axi_arprot_veer[i] = dma_axi_arprot_int;
      dma_axi_arlen_veer[i] = dma_axi_arlen_int;
      dma_axi_arburst_veer[i] = dma_axi_arburst_int;
      dma_axi_rready_veer[i] = dma_axi_rready_int;
    end
    // Get value from Core 0 for the time being
    lsu_axi_awvalid_int = lsu_axi_awvalid_veer[0];
    lsu_axi_awid_int = lsu_axi_awid_veer[0];
    lsu_axi_awaddr_int = lsu_axi_awaddr_veer[0];
    lsu_axi_awregion_int = lsu_axi_awregion_veer[0];
    lsu_axi_awlen_int = lsu_axi_awlen_veer[0];
    lsu_axi_awsize_int = lsu_axi_awsize_veer[0];
    lsu_axi_awburst_int = lsu_axi_awburst_veer[0];
    lsu_axi_awlock_int = lsu_axi_awlock_veer[0];
    lsu_axi_awcache_int = lsu_axi_awcache_veer[0];
    lsu_axi_awprot_int = lsu_axi_awprot_veer[0];
    lsu_axi_awqos_int = lsu_axi_awqos_veer[0];
    lsu_axi_wvalid_int = lsu_axi_wvalid_veer[0];
    lsu_axi_wdata_int = lsu_axi_wdata_veer[0];
    lsu_axi_wstrb_int = lsu_axi_wstrb_veer[0];
    lsu_axi_wlast_int = lsu_axi_wlast_veer[0];
    lsu_axi_bready_int = lsu_axi_bready_veer[0];
    lsu_axi_arvalid_int = lsu_axi_arvalid_veer[0];
    lsu_axi_arid_int = lsu_axi_arid_veer[0];
    lsu_axi_araddr_int = lsu_axi_araddr_veer[0];
    lsu_axi_arregion_int = lsu_axi_arregion_veer[0];
    lsu_axi_arlen_int = lsu_axi_arlen_veer[0];
    lsu_axi_arsize_int = lsu_axi_arsize_veer[0];
    lsu_axi_arburst_int = lsu_axi_arburst_veer[0];
    lsu_axi_arlock_int = lsu_axi_arlock_veer[0];
    lsu_axi_arcache_int = lsu_axi_arcache_veer[0];
    lsu_axi_arprot_int = lsu_axi_arprot_veer[0];
    lsu_axi_arqos_int = lsu_axi_arqos_veer[0];
    lsu_axi_rready_int = lsu_axi_rready_veer[0];

    ifu_axi_awvalid_int = ifu_axi_awvalid_veer[0];
    ifu_axi_awid_int = ifu_axi_awid_veer[0];
    ifu_axi_awaddr_int = ifu_axi_awaddr_veer[0];
    ifu_axi_awregion_int = ifu_axi_awregion_veer[0];
    ifu_axi_awlen_int = ifu_axi_awlen_veer[0];
    ifu_axi_awsize_int = ifu_axi_awsize_veer[0];
    ifu_axi_awburst_int = ifu_axi_awburst_veer[0];
    ifu_axi_awlock_int = ifu_axi_awlock_veer[0];
    ifu_axi_awcache_int = ifu_axi_awcache_veer[0];
    ifu_axi_awprot_int = ifu_axi_awprot_veer[0];
    ifu_axi_awqos_int = ifu_axi_awqos_veer[0];
    ifu_axi_wvalid_int = ifu_axi_wvalid_veer[0];
    ifu_axi_wdata_int = ifu_axi_wdata_veer[0];
    ifu_axi_wstrb_int = ifu_axi_wstrb_veer[0];
    ifu_axi_wlast_int = ifu_axi_wlast_veer[0];
    ifu_axi_bready_int = ifu_axi_bready_veer[0];
    ifu_axi_arvalid_int = ifu_axi_arvalid_veer[0];
    ifu_axi_arid_int = ifu_axi_arid_veer[0];
    ifu_axi_araddr_int = ifu_axi_araddr_veer[0];
    ifu_axi_arregion_int = ifu_axi_arregion_veer[0];
    ifu_axi_arlen_int = ifu_axi_arlen_veer[0];
    ifu_axi_arsize_int = ifu_axi_arsize_veer[0];
    ifu_axi_arburst_int = ifu_axi_arburst_veer[0];
    ifu_axi_arlock_int = ifu_axi_arlock_veer[0];
    ifu_axi_arcache_int = ifu_axi_arcache_veer[0];
    ifu_axi_arprot_int = ifu_axi_arprot_veer[0];
    ifu_axi_arqos_int = ifu_axi_arqos_veer[0];
    ifu_axi_rready_int = ifu_axi_rready_veer[0];

    sb_axi_awvalid_int = sb_axi_awvalid_veer[0];
    sb_axi_awid_int = sb_axi_awid_veer[0];
    sb_axi_awaddr_int = sb_axi_awaddr_veer[0];
    sb_axi_awregion_int = sb_axi_awregion_veer[0];
    sb_axi_awlen_int = sb_axi_awlen_veer[0];
    sb_axi_awsize_int = sb_axi_awsize_veer[0];
    sb_axi_awburst_int = sb_axi_awburst_veer[0];
    sb_axi_awlock_int = sb_axi_awlock_veer[0];
    sb_axi_awcache_int = sb_axi_awcache_veer[0];
    sb_axi_awprot_int = sb_axi_awprot_veer[0];
    sb_axi_awqos_int = sb_axi_awqos_veer[0];
    sb_axi_wvalid_int = sb_axi_wvalid_veer[0];
    sb_axi_wdata_int = sb_axi_wdata_veer[0];
    sb_axi_wstrb_int = sb_axi_wstrb_veer[0];
    sb_axi_wlast_int = sb_axi_wlast_veer[0];
    sb_axi_bready_int = sb_axi_bready_veer[0];
    sb_axi_arvalid_int = sb_axi_arvalid_veer[0];
    sb_axi_arid_int = sb_axi_arid_veer[0];
    sb_axi_araddr_int = sb_axi_araddr_veer[0];
    sb_axi_arregion_int = sb_axi_arregion_veer[0];
    sb_axi_arlen_int = sb_axi_arlen_veer[0];
    sb_axi_arsize_int = sb_axi_arsize_veer[0];
    sb_axi_arburst_int = sb_axi_arburst_veer[0];
    sb_axi_arlock_int = sb_axi_arlock_veer[0];
    sb_axi_arcache_int = sb_axi_arcache_veer[0];
    sb_axi_arprot_int = sb_axi_arprot_veer[0];
    sb_axi_arqos_int = sb_axi_arqos_veer[0];
    sb_axi_rready_int = sb_axi_rready_veer[0];

    dma_axi_awready_int = dma_axi_awready_veer[0];
    dma_axi_wready_int = dma_axi_wready_veer[0];
    dma_axi_bvalid_int = dma_axi_bvalid_veer[0];
    dma_axi_bresp_int = dma_axi_bresp_veer[0];
    dma_axi_bid_int = dma_axi_bid_veer[0];
    dma_axi_arready_int = dma_axi_arready_veer[0];
    dma_axi_rvalid_int = dma_axi_rvalid_veer[0];
    dma_axi_rid_int = dma_axi_rid_veer[0];
    dma_axi_rdata_int = dma_axi_rdata_veer[0];
    dma_axi_rresp_int = dma_axi_rresp_veer[0];
    dma_axi_rlast_int = dma_axi_rlast_veer[0];
  end
endmodule
