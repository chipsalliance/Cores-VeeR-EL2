// Copyright 2026 Antmicro <www.antmicro.com>
// //
// // SPDX-License-Identifier: Apache-2.0
//
`ifdef RV_TRIPLE_MODULAR_REDUNDANCY_ENABLE
module el2_tmr_axi
  import el2_pkg::*;
  import el2_mubi_pkg::*;
#(
    `include "el2_param.vh"
) (
    input  logic                            rst_l,
    output logic                            free_l2clk,

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
    input  logic                      dma_axi_rlast_veer[3],

    // Fault inputs
    input  el2_mubi_pkg::el2_mubi_t axi_fault_d[3],
    // Fault outputs
    output el2_mubi_pkg::el2_mubi_t axi_fault_q[3],
    // Fault clear inputs
    input  el2_mubi_pkg::el2_mubi_t axi_fault_clr[3]
);

  // ......................................................

  el2_mubi_t  lsu_axi_fault_d[3];
  el2_mubi_t  lsu_axi_fault_q[3];
  el2_mubi_t  lsu_axi_fault_clr[3];

  el2_mubi_t  ifu_axi_fault_d[3];
  el2_mubi_t  ifu_axi_fault_q[3];
  el2_mubi_t  ifu_axi_fault_clr[3];

  el2_mubi_t  sb_axi_fault_d[3];
  el2_mubi_t  sb_axi_fault_q[3];
  el2_mubi_t  sb_axi_fault_clr[3];

  el2_mubi_t  dma_axi_fault_d[3];
  el2_mubi_t  dma_axi_fault_q[3];
  el2_mubi_t  dma_axi_fault_clr[3];

  generate for (genvar i=0; i<3; i=i+1) begin
    el2_mubi_t axi_fault_q_l0;
    el2_mubi_t axi_fault_q_l1;

    // Aggregate fault output
    assign axi_fault_q_l0 = mubi_or(lsu_axi_fault_q[i], ifu_axi_fault_q[i]);
    assign axi_fault_q_l1 = mubi_or(sb_axi_fault_q[i],  dma_axi_fault_q[i]);
    assign axi_fault_q[i] = mubi_or(axi_fault_q_l0, axi_fault_q_l1);

    // Distribute fault and clear input
    assign lsu_axi_fault_d[i] = axi_fault_d[i];
    assign ifu_axi_fault_d[i] = axi_fault_d[i];
    assign sb_axi_fault_d[i]  = axi_fault_d[i];
    assign dma_axi_fault_d[i] = axi_fault_d[i];

    assign lsu_axi_fault_clr[i] = axi_fault_clr[i];
    assign ifu_axi_fault_clr[i] = axi_fault_clr[i];
    assign sb_axi_fault_clr[i]  = axi_fault_clr[i];
    assign dma_axi_fault_clr[i] = axi_fault_clr[i];

  end endgenerate

  // ......................................................

  // LSU AXI
  el2_tmr_axi_m #(
    .AddrWidth  (32),
    .DataWidth  (64),
    .IdWidth    (pt.LSU_BUS_TAG)

  ) x_lsu_axi (
    .clk_i  (free_l2clk),
    .rst_ni (rst_l),

    .a_s_axi_awvalid_i   (lsu_axi_awvalid_veer  [0]),
    .a_s_axi_awready_o   (lsu_axi_awready_veer  [0]),
    .a_s_axi_awid_i      (lsu_axi_awid_veer     [0]),
    .a_s_axi_awaddr_i    (lsu_axi_awaddr_veer   [0]),
    .a_s_axi_awregion_i  (lsu_axi_awregion_veer [0]),
    .a_s_axi_awlen_i     (lsu_axi_awlen_veer    [0]),
    .a_s_axi_awsize_i    (lsu_axi_awsize_veer   [0]),
    .a_s_axi_awburst_i   (lsu_axi_awburst_veer  [0]),
    .a_s_axi_awlock_i    (lsu_axi_awlock_veer   [0]),
    .a_s_axi_awcache_i   (lsu_axi_awcache_veer  [0]),
    .a_s_axi_awprot_i    (lsu_axi_awprot_veer   [0]),
    .a_s_axi_awqos_i     (lsu_axi_awqos_veer    [0]),

    .a_s_axi_wvalid_i    (lsu_axi_wvalid_veer   [0]),
    .a_s_axi_wready_o    (lsu_axi_wready_veer   [0]),
    .a_s_axi_wdata_i     (lsu_axi_wdata_veer    [0]),
    .a_s_axi_wstrb_i     (lsu_axi_wstrb_veer    [0]),
    .a_s_axi_wlast_i     (lsu_axi_wlast_veer    [0]),

    .a_s_axi_bvalid_o    (lsu_axi_bvalid_veer   [0]),
    .a_s_axi_bready_i    (lsu_axi_bready_veer   [0]),
    .a_s_axi_bresp_o     (lsu_axi_bresp_veer    [0]),
    .a_s_axi_bid_o       (lsu_axi_bid_veer      [0]),

    .a_s_axi_arvalid_i   (lsu_axi_arvalid_veer  [0]),
    .a_s_axi_arready_o   (lsu_axi_arready_veer  [0]),
    .a_s_axi_arid_i      (lsu_axi_arid_veer     [0]),
    .a_s_axi_araddr_i    (lsu_axi_araddr_veer   [0]),
    .a_s_axi_arregion_i  (lsu_axi_arregion_veer [0]),
    .a_s_axi_arlen_i     (lsu_axi_arlen_veer    [0]),
    .a_s_axi_arsize_i    (lsu_axi_arsize_veer   [0]),
    .a_s_axi_arburst_i   (lsu_axi_arburst_veer  [0]),
    .a_s_axi_arlock_i    (lsu_axi_arlock_veer   [0]),
    .a_s_axi_arcache_i   (lsu_axi_arcache_veer  [0]),
    .a_s_axi_arprot_i    (lsu_axi_arprot_veer   [0]),
    .a_s_axi_arqos_i     (lsu_axi_arqos_veer    [0]),

    .a_s_axi_rvalid_o    (lsu_axi_rvalid_veer   [0]),
    .a_s_axi_rready_i    (lsu_axi_rready_veer   [0]),
    .a_s_axi_rid_o       (lsu_axi_rid_veer      [0]),
    .a_s_axi_rdata_o     (lsu_axi_rdata_veer    [0]),
    .a_s_axi_rresp_o     (lsu_axi_rresp_veer    [0]),
    .a_s_axi_rlast_o     (lsu_axi_rlast_veer    [0]),


    .b_s_axi_awvalid_i   (lsu_axi_awvalid_veer  [1]),
    .b_s_axi_awready_o   (lsu_axi_awready_veer  [1]),
    .b_s_axi_awid_i      (lsu_axi_awid_veer     [1]),
    .b_s_axi_awaddr_i    (lsu_axi_awaddr_veer   [1]),
    .b_s_axi_awregion_i  (lsu_axi_awregion_veer [1]),
    .b_s_axi_awlen_i     (lsu_axi_awlen_veer    [1]),
    .b_s_axi_awsize_i    (lsu_axi_awsize_veer   [1]),
    .b_s_axi_awburst_i   (lsu_axi_awburst_veer  [1]),
    .b_s_axi_awlock_i    (lsu_axi_awlock_veer   [1]),
    .b_s_axi_awcache_i   (lsu_axi_awcache_veer  [1]),
    .b_s_axi_awprot_i    (lsu_axi_awprot_veer   [1]),
    .b_s_axi_awqos_i     (lsu_axi_awqos_veer    [1]),

    .b_s_axi_wvalid_i    (lsu_axi_wvalid_veer   [1]),
    .b_s_axi_wready_o    (lsu_axi_wready_veer   [1]),
    .b_s_axi_wdata_i     (lsu_axi_wdata_veer    [1]),
    .b_s_axi_wstrb_i     (lsu_axi_wstrb_veer    [1]),
    .b_s_axi_wlast_i     (lsu_axi_wlast_veer    [1]),

    .b_s_axi_bvalid_o    (lsu_axi_bvalid_veer   [1]),
    .b_s_axi_bready_i    (lsu_axi_bready_veer   [1]),
    .b_s_axi_bresp_o     (lsu_axi_bresp_veer    [1]),
    .b_s_axi_bid_o       (lsu_axi_bid_veer      [1]),

    .b_s_axi_arvalid_i   (lsu_axi_arvalid_veer  [1]),
    .b_s_axi_arready_o   (lsu_axi_arready_veer  [1]),
    .b_s_axi_arid_i      (lsu_axi_arid_veer     [1]),
    .b_s_axi_araddr_i    (lsu_axi_araddr_veer   [1]),
    .b_s_axi_arregion_i  (lsu_axi_arregion_veer [1]),
    .b_s_axi_arlen_i     (lsu_axi_arlen_veer    [1]),
    .b_s_axi_arsize_i    (lsu_axi_arsize_veer   [1]),
    .b_s_axi_arburst_i   (lsu_axi_arburst_veer  [1]),
    .b_s_axi_arlock_i    (lsu_axi_arlock_veer   [1]),
    .b_s_axi_arcache_i   (lsu_axi_arcache_veer  [1]),
    .b_s_axi_arprot_i    (lsu_axi_arprot_veer   [1]),
    .b_s_axi_arqos_i     (lsu_axi_arqos_veer    [1]),

    .b_s_axi_rvalid_o    (lsu_axi_rvalid_veer   [1]),
    .b_s_axi_rready_i    (lsu_axi_rready_veer   [1]),
    .b_s_axi_rid_o       (lsu_axi_rid_veer      [1]),
    .b_s_axi_rdata_o     (lsu_axi_rdata_veer    [1]),
    .b_s_axi_rresp_o     (lsu_axi_rresp_veer    [1]),
    .b_s_axi_rlast_o     (lsu_axi_rlast_veer    [1]),


    .c_s_axi_awvalid_i   (lsu_axi_awvalid_veer  [2]),
    .c_s_axi_awready_o   (lsu_axi_awready_veer  [2]),
    .c_s_axi_awid_i      (lsu_axi_awid_veer     [2]),
    .c_s_axi_awaddr_i    (lsu_axi_awaddr_veer   [2]),
    .c_s_axi_awregion_i  (lsu_axi_awregion_veer [2]),
    .c_s_axi_awlen_i     (lsu_axi_awlen_veer    [2]),
    .c_s_axi_awsize_i    (lsu_axi_awsize_veer   [2]),
    .c_s_axi_awburst_i   (lsu_axi_awburst_veer  [2]),
    .c_s_axi_awlock_i    (lsu_axi_awlock_veer   [2]),
    .c_s_axi_awcache_i   (lsu_axi_awcache_veer  [2]),
    .c_s_axi_awprot_i    (lsu_axi_awprot_veer   [2]),
    .c_s_axi_awqos_i     (lsu_axi_awqos_veer    [2]),

    .c_s_axi_wvalid_i    (lsu_axi_wvalid_veer   [2]),
    .c_s_axi_wready_o    (lsu_axi_wready_veer   [2]),
    .c_s_axi_wdata_i     (lsu_axi_wdata_veer    [2]),
    .c_s_axi_wstrb_i     (lsu_axi_wstrb_veer    [2]),
    .c_s_axi_wlast_i     (lsu_axi_wlast_veer    [2]),

    .c_s_axi_bvalid_o    (lsu_axi_bvalid_veer   [2]),
    .c_s_axi_bready_i    (lsu_axi_bready_veer   [2]),
    .c_s_axi_bresp_o     (lsu_axi_bresp_veer    [2]),
    .c_s_axi_bid_o       (lsu_axi_bid_veer      [2]),

    .c_s_axi_arvalid_i   (lsu_axi_arvalid_veer  [2]),
    .c_s_axi_arready_o   (lsu_axi_arready_veer  [2]),
    .c_s_axi_arid_i      (lsu_axi_arid_veer     [2]),
    .c_s_axi_araddr_i    (lsu_axi_araddr_veer   [2]),
    .c_s_axi_arregion_i  (lsu_axi_arregion_veer [2]),
    .c_s_axi_arlen_i     (lsu_axi_arlen_veer    [2]),
    .c_s_axi_arsize_i    (lsu_axi_arsize_veer   [2]),
    .c_s_axi_arburst_i   (lsu_axi_arburst_veer  [2]),
    .c_s_axi_arlock_i    (lsu_axi_arlock_veer   [2]),
    .c_s_axi_arcache_i   (lsu_axi_arcache_veer  [2]),
    .c_s_axi_arprot_i    (lsu_axi_arprot_veer   [2]),
    .c_s_axi_arqos_i     (lsu_axi_arqos_veer    [2]),

    .c_s_axi_rvalid_o    (lsu_axi_rvalid_veer   [2]),
    .c_s_axi_rready_i    (lsu_axi_rready_veer   [2]),
    .c_s_axi_rid_o       (lsu_axi_rid_veer      [2]),
    .c_s_axi_rdata_o     (lsu_axi_rdata_veer    [2]),
    .c_s_axi_rresp_o     (lsu_axi_rresp_veer    [2]),
    .c_s_axi_rlast_o     (lsu_axi_rlast_veer    [2]),


    .m_axi_awvalid_o     (lsu_axi_awvalid_int),
    .m_axi_awready_i     (lsu_axi_awready_int),
    .m_axi_awid_o        (lsu_axi_awid_int),
    .m_axi_awaddr_o      (lsu_axi_awaddr_int),
    .m_axi_awregion_o    (lsu_axi_awregion_int),
    .m_axi_awlen_o       (lsu_axi_awlen_int),
    .m_axi_awsize_o      (lsu_axi_awsize_int),
    .m_axi_awburst_o     (lsu_axi_awburst_int),
    .m_axi_awlock_o      (lsu_axi_awlock_int),
    .m_axi_awcache_o     (lsu_axi_awcache_int),
    .m_axi_awprot_o      (lsu_axi_awprot_int),
    .m_axi_awqos_o       (lsu_axi_awqos_int),

    .m_axi_wvalid_o      (lsu_axi_wvalid_int),
    .m_axi_wready_i      (lsu_axi_wready_int),
    .m_axi_wdata_o       (lsu_axi_wdata_int),
    .m_axi_wstrb_o       (lsu_axi_wstrb_int),
    .m_axi_wlast_o       (lsu_axi_wlast_int),

    .m_axi_bvalid_i      (lsu_axi_bvalid_int),
    .m_axi_bready_o      (lsu_axi_bready_int),
    .m_axi_bresp_i       (lsu_axi_bresp_int),
    .m_axi_bid_i         (lsu_axi_bid_int),

    .m_axi_arvalid_o     (lsu_axi_arvalid_int),
    .m_axi_arready_i     (lsu_axi_arready_int),
    .m_axi_arid_o        (lsu_axi_arid_int),
    .m_axi_araddr_o      (lsu_axi_araddr_int),
    .m_axi_arregion_o    (lsu_axi_arregion_int),
    .m_axi_arlen_o       (lsu_axi_arlen_int),
    .m_axi_arsize_o      (lsu_axi_arsize_int),
    .m_axi_arburst_o     (lsu_axi_arburst_int),
    .m_axi_arlock_o      (lsu_axi_arlock_int),
    .m_axi_arcache_o     (lsu_axi_arcache_int),
    .m_axi_arprot_o      (lsu_axi_arprot_int),
    .m_axi_arqos_o       (lsu_axi_arqos_int),

    .m_axi_rvalid_i      (lsu_axi_rvalid_int),
    .m_axi_rready_o      (lsu_axi_rready_int),
    .m_axi_rid_i         (lsu_axi_rid_int),
    .m_axi_rdata_i       (lsu_axi_rdata_int),
    .m_axi_rresp_i       (lsu_axi_rresp_int),
    .m_axi_rlast_i       (lsu_axi_rlast_int),


    .a_s_axi_fault_o     (lsu_axi_fault_q[0]),
    .b_s_axi_fault_o     (lsu_axi_fault_q[1]),
    .c_s_axi_fault_o     (lsu_axi_fault_q[2]),

    .a_s_axi_fault_i     (lsu_axi_fault_d[0]),
    .b_s_axi_fault_i     (lsu_axi_fault_d[1]),
    .c_s_axi_fault_i     (lsu_axi_fault_d[2]),

    .a_s_axi_fault_clr_i (lsu_axi_fault_clr[0]),
    .b_s_axi_fault_clr_i (lsu_axi_fault_clr[1]),
    .c_s_axi_fault_clr_i (lsu_axi_fault_clr[2])
  );

  // IFU AXI
  el2_tmr_axi_m #(
    .AddrWidth  (32),
    .DataWidth  (64),
    .IdWidth    (pt.IFU_BUS_TAG)

  ) x_ifu_axi (
    .clk_i  (free_l2clk),
    .rst_ni (rst_l),

    .a_s_axi_awvalid_i   (ifu_axi_awvalid_veer  [0]),
    .a_s_axi_awready_o   (ifu_axi_awready_veer  [0]),
    .a_s_axi_awid_i      (ifu_axi_awid_veer     [0]),
    .a_s_axi_awaddr_i    (ifu_axi_awaddr_veer   [0]),
    .a_s_axi_awregion_i  (ifu_axi_awregion_veer [0]),
    .a_s_axi_awlen_i     (ifu_axi_awlen_veer    [0]),
    .a_s_axi_awsize_i    (ifu_axi_awsize_veer   [0]),
    .a_s_axi_awburst_i   (ifu_axi_awburst_veer  [0]),
    .a_s_axi_awlock_i    (ifu_axi_awlock_veer   [0]),
    .a_s_axi_awcache_i   (ifu_axi_awcache_veer  [0]),
    .a_s_axi_awprot_i    (ifu_axi_awprot_veer   [0]),
    .a_s_axi_awqos_i     (ifu_axi_awqos_veer    [0]),

    .a_s_axi_wvalid_i    (ifu_axi_wvalid_veer   [0]),
    .a_s_axi_wready_o    (ifu_axi_wready_veer   [0]),
    .a_s_axi_wdata_i     (ifu_axi_wdata_veer    [0]),
    .a_s_axi_wstrb_i     (ifu_axi_wstrb_veer    [0]),
    .a_s_axi_wlast_i     (ifu_axi_wlast_veer    [0]),

    .a_s_axi_bvalid_o    (ifu_axi_bvalid_veer   [0]),
    .a_s_axi_bready_i    (ifu_axi_bready_veer   [0]),
    .a_s_axi_bresp_o     (ifu_axi_bresp_veer    [0]),
    .a_s_axi_bid_o       (ifu_axi_bid_veer      [0]),

    .a_s_axi_arvalid_i   (ifu_axi_arvalid_veer  [0]),
    .a_s_axi_arready_o   (ifu_axi_arready_veer  [0]),
    .a_s_axi_arid_i      (ifu_axi_arid_veer     [0]),
    .a_s_axi_araddr_i    (ifu_axi_araddr_veer   [0]),
    .a_s_axi_arregion_i  (ifu_axi_arregion_veer [0]),
    .a_s_axi_arlen_i     (ifu_axi_arlen_veer    [0]),
    .a_s_axi_arsize_i    (ifu_axi_arsize_veer   [0]),
    .a_s_axi_arburst_i   (ifu_axi_arburst_veer  [0]),
    .a_s_axi_arlock_i    (ifu_axi_arlock_veer   [0]),
    .a_s_axi_arcache_i   (ifu_axi_arcache_veer  [0]),
    .a_s_axi_arprot_i    (ifu_axi_arprot_veer   [0]),
    .a_s_axi_arqos_i     (ifu_axi_arqos_veer    [0]),

    .a_s_axi_rvalid_o    (ifu_axi_rvalid_veer   [0]),
    .a_s_axi_rready_i    (ifu_axi_rready_veer   [0]),
    .a_s_axi_rid_o       (ifu_axi_rid_veer      [0]),
    .a_s_axi_rdata_o     (ifu_axi_rdata_veer    [0]),
    .a_s_axi_rresp_o     (ifu_axi_rresp_veer    [0]),
    .a_s_axi_rlast_o     (ifu_axi_rlast_veer    [0]),


    .b_s_axi_awvalid_i   (ifu_axi_awvalid_veer  [1]),
    .b_s_axi_awready_o   (ifu_axi_awready_veer  [1]),
    .b_s_axi_awid_i      (ifu_axi_awid_veer     [1]),
    .b_s_axi_awaddr_i    (ifu_axi_awaddr_veer   [1]),
    .b_s_axi_awregion_i  (ifu_axi_awregion_veer [1]),
    .b_s_axi_awlen_i     (ifu_axi_awlen_veer    [1]),
    .b_s_axi_awsize_i    (ifu_axi_awsize_veer   [1]),
    .b_s_axi_awburst_i   (ifu_axi_awburst_veer  [1]),
    .b_s_axi_awlock_i    (ifu_axi_awlock_veer   [1]),
    .b_s_axi_awcache_i   (ifu_axi_awcache_veer  [1]),
    .b_s_axi_awprot_i    (ifu_axi_awprot_veer   [1]),
    .b_s_axi_awqos_i     (ifu_axi_awqos_veer    [1]),

    .b_s_axi_wvalid_i    (ifu_axi_wvalid_veer   [1]),
    .b_s_axi_wready_o    (ifu_axi_wready_veer   [1]),
    .b_s_axi_wdata_i     (ifu_axi_wdata_veer    [1]),
    .b_s_axi_wstrb_i     (ifu_axi_wstrb_veer    [1]),
    .b_s_axi_wlast_i     (ifu_axi_wlast_veer    [1]),

    .b_s_axi_bvalid_o    (ifu_axi_bvalid_veer   [1]),
    .b_s_axi_bready_i    (ifu_axi_bready_veer   [1]),
    .b_s_axi_bresp_o     (ifu_axi_bresp_veer    [1]),
    .b_s_axi_bid_o       (ifu_axi_bid_veer      [1]),

    .b_s_axi_arvalid_i   (ifu_axi_arvalid_veer  [1]),
    .b_s_axi_arready_o   (ifu_axi_arready_veer  [1]),
    .b_s_axi_arid_i      (ifu_axi_arid_veer     [1]),
    .b_s_axi_araddr_i    (ifu_axi_araddr_veer   [1]),
    .b_s_axi_arregion_i  (ifu_axi_arregion_veer [1]),
    .b_s_axi_arlen_i     (ifu_axi_arlen_veer    [1]),
    .b_s_axi_arsize_i    (ifu_axi_arsize_veer   [1]),
    .b_s_axi_arburst_i   (ifu_axi_arburst_veer  [1]),
    .b_s_axi_arlock_i    (ifu_axi_arlock_veer   [1]),
    .b_s_axi_arcache_i   (ifu_axi_arcache_veer  [1]),
    .b_s_axi_arprot_i    (ifu_axi_arprot_veer   [1]),
    .b_s_axi_arqos_i     (ifu_axi_arqos_veer    [1]),

    .b_s_axi_rvalid_o    (ifu_axi_rvalid_veer   [1]),
    .b_s_axi_rready_i    (ifu_axi_rready_veer   [1]),
    .b_s_axi_rid_o       (ifu_axi_rid_veer      [1]),
    .b_s_axi_rdata_o     (ifu_axi_rdata_veer    [1]),
    .b_s_axi_rresp_o     (ifu_axi_rresp_veer    [1]),
    .b_s_axi_rlast_o     (ifu_axi_rlast_veer    [1]),


    .c_s_axi_awvalid_i   (ifu_axi_awvalid_veer  [2]),
    .c_s_axi_awready_o   (ifu_axi_awready_veer  [2]),
    .c_s_axi_awid_i      (ifu_axi_awid_veer     [2]),
    .c_s_axi_awaddr_i    (ifu_axi_awaddr_veer   [2]),
    .c_s_axi_awregion_i  (ifu_axi_awregion_veer [2]),
    .c_s_axi_awlen_i     (ifu_axi_awlen_veer    [2]),
    .c_s_axi_awsize_i    (ifu_axi_awsize_veer   [2]),
    .c_s_axi_awburst_i   (ifu_axi_awburst_veer  [2]),
    .c_s_axi_awlock_i    (ifu_axi_awlock_veer   [2]),
    .c_s_axi_awcache_i   (ifu_axi_awcache_veer  [2]),
    .c_s_axi_awprot_i    (ifu_axi_awprot_veer   [2]),
    .c_s_axi_awqos_i     (ifu_axi_awqos_veer    [2]),

    .c_s_axi_wvalid_i    (ifu_axi_wvalid_veer   [2]),
    .c_s_axi_wready_o    (ifu_axi_wready_veer   [2]),
    .c_s_axi_wdata_i     (ifu_axi_wdata_veer    [2]),
    .c_s_axi_wstrb_i     (ifu_axi_wstrb_veer    [2]),
    .c_s_axi_wlast_i     (ifu_axi_wlast_veer    [2]),

    .c_s_axi_bvalid_o    (ifu_axi_bvalid_veer   [2]),
    .c_s_axi_bready_i    (ifu_axi_bready_veer   [2]),
    .c_s_axi_bresp_o     (ifu_axi_bresp_veer    [2]),
    .c_s_axi_bid_o       (ifu_axi_bid_veer      [2]),

    .c_s_axi_arvalid_i   (ifu_axi_arvalid_veer  [2]),
    .c_s_axi_arready_o   (ifu_axi_arready_veer  [2]),
    .c_s_axi_arid_i      (ifu_axi_arid_veer     [2]),
    .c_s_axi_araddr_i    (ifu_axi_araddr_veer   [2]),
    .c_s_axi_arregion_i  (ifu_axi_arregion_veer [2]),
    .c_s_axi_arlen_i     (ifu_axi_arlen_veer    [2]),
    .c_s_axi_arsize_i    (ifu_axi_arsize_veer   [2]),
    .c_s_axi_arburst_i   (ifu_axi_arburst_veer  [2]),
    .c_s_axi_arlock_i    (ifu_axi_arlock_veer   [2]),
    .c_s_axi_arcache_i   (ifu_axi_arcache_veer  [2]),
    .c_s_axi_arprot_i    (ifu_axi_arprot_veer   [2]),
    .c_s_axi_arqos_i     (ifu_axi_arqos_veer    [2]),

    .c_s_axi_rvalid_o    (ifu_axi_rvalid_veer   [2]),
    .c_s_axi_rready_i    (ifu_axi_rready_veer   [2]),
    .c_s_axi_rid_o       (ifu_axi_rid_veer      [2]),
    .c_s_axi_rdata_o     (ifu_axi_rdata_veer    [2]),
    .c_s_axi_rresp_o     (ifu_axi_rresp_veer    [2]),
    .c_s_axi_rlast_o     (ifu_axi_rlast_veer    [2]),


    .m_axi_awvalid_o     (ifu_axi_awvalid_int),
    .m_axi_awready_i     (ifu_axi_awready_int),
    .m_axi_awid_o        (ifu_axi_awid_int),
    .m_axi_awaddr_o      (ifu_axi_awaddr_int),
    .m_axi_awregion_o    (ifu_axi_awregion_int),
    .m_axi_awlen_o       (ifu_axi_awlen_int),
    .m_axi_awsize_o      (ifu_axi_awsize_int),
    .m_axi_awburst_o     (ifu_axi_awburst_int),
    .m_axi_awlock_o      (ifu_axi_awlock_int),
    .m_axi_awcache_o     (ifu_axi_awcache_int),
    .m_axi_awprot_o      (ifu_axi_awprot_int),
    .m_axi_awqos_o       (ifu_axi_awqos_int),

    .m_axi_wvalid_o      (ifu_axi_wvalid_int),
    .m_axi_wready_i      (ifu_axi_wready_int),
    .m_axi_wdata_o       (ifu_axi_wdata_int),
    .m_axi_wstrb_o       (ifu_axi_wstrb_int),
    .m_axi_wlast_o       (ifu_axi_wlast_int),

    .m_axi_bvalid_i      (ifu_axi_bvalid_int),
    .m_axi_bready_o      (ifu_axi_bready_int),
    .m_axi_bresp_i       (ifu_axi_bresp_int),
    .m_axi_bid_i         (ifu_axi_bid_int),

    .m_axi_arvalid_o     (ifu_axi_arvalid_int),
    .m_axi_arready_i     (ifu_axi_arready_int),
    .m_axi_arid_o        (ifu_axi_arid_int),
    .m_axi_araddr_o      (ifu_axi_araddr_int),
    .m_axi_arregion_o    (ifu_axi_arregion_int),
    .m_axi_arlen_o       (ifu_axi_arlen_int),
    .m_axi_arsize_o      (ifu_axi_arsize_int),
    .m_axi_arburst_o     (ifu_axi_arburst_int),
    .m_axi_arlock_o      (ifu_axi_arlock_int),
    .m_axi_arcache_o     (ifu_axi_arcache_int),
    .m_axi_arprot_o      (ifu_axi_arprot_int),
    .m_axi_arqos_o       (ifu_axi_arqos_int),

    .m_axi_rvalid_i      (ifu_axi_rvalid_int),
    .m_axi_rready_o      (ifu_axi_rready_int),
    .m_axi_rid_i         (ifu_axi_rid_int),
    .m_axi_rdata_i       (ifu_axi_rdata_int),
    .m_axi_rresp_i       (ifu_axi_rresp_int),
    .m_axi_rlast_i       (ifu_axi_rlast_int),


    .a_s_axi_fault_o     (ifu_axi_fault_q[0]),
    .b_s_axi_fault_o     (ifu_axi_fault_q[1]),
    .c_s_axi_fault_o     (ifu_axi_fault_q[2]),

    .a_s_axi_fault_i     (ifu_axi_fault_d[0]),
    .b_s_axi_fault_i     (ifu_axi_fault_d[1]),
    .c_s_axi_fault_i     (ifu_axi_fault_d[2]),

    .a_s_axi_fault_clr_i (ifu_axi_fault_clr[0]),
    .b_s_axi_fault_clr_i (ifu_axi_fault_clr[1]),
    .c_s_axi_fault_clr_i (ifu_axi_fault_clr[2])
  );

  // SB AXI
  el2_tmr_axi_m #(
    .AddrWidth  (32),
    .DataWidth  (64),
    .IdWidth    (pt.SB_BUS_TAG)

  ) x_sb_axi (
    .clk_i  (free_l2clk),
    .rst_ni (rst_l),

    .a_s_axi_awvalid_i   (sb_axi_awvalid_veer  [0]),
    .a_s_axi_awready_o   (sb_axi_awready_veer  [0]),
    .a_s_axi_awid_i      (sb_axi_awid_veer     [0]),
    .a_s_axi_awaddr_i    (sb_axi_awaddr_veer   [0]),
    .a_s_axi_awregion_i  (sb_axi_awregion_veer [0]),
    .a_s_axi_awlen_i     (sb_axi_awlen_veer    [0]),
    .a_s_axi_awsize_i    (sb_axi_awsize_veer   [0]),
    .a_s_axi_awburst_i   (sb_axi_awburst_veer  [0]),
    .a_s_axi_awlock_i    (sb_axi_awlock_veer   [0]),
    .a_s_axi_awcache_i   (sb_axi_awcache_veer  [0]),
    .a_s_axi_awprot_i    (sb_axi_awprot_veer   [0]),
    .a_s_axi_awqos_i     (sb_axi_awqos_veer    [0]),

    .a_s_axi_wvalid_i    (sb_axi_wvalid_veer   [0]),
    .a_s_axi_wready_o    (sb_axi_wready_veer   [0]),
    .a_s_axi_wdata_i     (sb_axi_wdata_veer    [0]),
    .a_s_axi_wstrb_i     (sb_axi_wstrb_veer    [0]),
    .a_s_axi_wlast_i     (sb_axi_wlast_veer    [0]),

    .a_s_axi_bvalid_o    (sb_axi_bvalid_veer   [0]),
    .a_s_axi_bready_i    (sb_axi_bready_veer   [0]),
    .a_s_axi_bresp_o     (sb_axi_bresp_veer    [0]),
    .a_s_axi_bid_o       (sb_axi_bid_veer      [0]),

    .a_s_axi_arvalid_i   (sb_axi_arvalid_veer  [0]),
    .a_s_axi_arready_o   (sb_axi_arready_veer  [0]),
    .a_s_axi_arid_i      (sb_axi_arid_veer     [0]),
    .a_s_axi_araddr_i    (sb_axi_araddr_veer   [0]),
    .a_s_axi_arregion_i  (sb_axi_arregion_veer [0]),
    .a_s_axi_arlen_i     (sb_axi_arlen_veer    [0]),
    .a_s_axi_arsize_i    (sb_axi_arsize_veer   [0]),
    .a_s_axi_arburst_i   (sb_axi_arburst_veer  [0]),
    .a_s_axi_arlock_i    (sb_axi_arlock_veer   [0]),
    .a_s_axi_arcache_i   (sb_axi_arcache_veer  [0]),
    .a_s_axi_arprot_i    (sb_axi_arprot_veer   [0]),
    .a_s_axi_arqos_i     (sb_axi_arqos_veer    [0]),

    .a_s_axi_rvalid_o    (sb_axi_rvalid_veer   [0]),
    .a_s_axi_rready_i    (sb_axi_rready_veer   [0]),
    .a_s_axi_rid_o       (sb_axi_rid_veer      [0]),
    .a_s_axi_rdata_o     (sb_axi_rdata_veer    [0]),
    .a_s_axi_rresp_o     (sb_axi_rresp_veer    [0]),
    .a_s_axi_rlast_o     (sb_axi_rlast_veer    [0]),


    .b_s_axi_awvalid_i   (sb_axi_awvalid_veer  [1]),
    .b_s_axi_awready_o   (sb_axi_awready_veer  [1]),
    .b_s_axi_awid_i      (sb_axi_awid_veer     [1]),
    .b_s_axi_awaddr_i    (sb_axi_awaddr_veer   [1]),
    .b_s_axi_awregion_i  (sb_axi_awregion_veer [1]),
    .b_s_axi_awlen_i     (sb_axi_awlen_veer    [1]),
    .b_s_axi_awsize_i    (sb_axi_awsize_veer   [1]),
    .b_s_axi_awburst_i   (sb_axi_awburst_veer  [1]),
    .b_s_axi_awlock_i    (sb_axi_awlock_veer   [1]),
    .b_s_axi_awcache_i   (sb_axi_awcache_veer  [1]),
    .b_s_axi_awprot_i    (sb_axi_awprot_veer   [1]),
    .b_s_axi_awqos_i     (sb_axi_awqos_veer    [1]),

    .b_s_axi_wvalid_i    (sb_axi_wvalid_veer   [1]),
    .b_s_axi_wready_o    (sb_axi_wready_veer   [1]),
    .b_s_axi_wdata_i     (sb_axi_wdata_veer    [1]),
    .b_s_axi_wstrb_i     (sb_axi_wstrb_veer    [1]),
    .b_s_axi_wlast_i     (sb_axi_wlast_veer    [1]),

    .b_s_axi_bvalid_o    (sb_axi_bvalid_veer   [1]),
    .b_s_axi_bready_i    (sb_axi_bready_veer   [1]),
    .b_s_axi_bresp_o     (sb_axi_bresp_veer    [1]),
    .b_s_axi_bid_o       (sb_axi_bid_veer      [1]),

    .b_s_axi_arvalid_i   (sb_axi_arvalid_veer  [1]),
    .b_s_axi_arready_o   (sb_axi_arready_veer  [1]),
    .b_s_axi_arid_i      (sb_axi_arid_veer     [1]),
    .b_s_axi_araddr_i    (sb_axi_araddr_veer   [1]),
    .b_s_axi_arregion_i  (sb_axi_arregion_veer [1]),
    .b_s_axi_arlen_i     (sb_axi_arlen_veer    [1]),
    .b_s_axi_arsize_i    (sb_axi_arsize_veer   [1]),
    .b_s_axi_arburst_i   (sb_axi_arburst_veer  [1]),
    .b_s_axi_arlock_i    (sb_axi_arlock_veer   [1]),
    .b_s_axi_arcache_i   (sb_axi_arcache_veer  [1]),
    .b_s_axi_arprot_i    (sb_axi_arprot_veer   [1]),
    .b_s_axi_arqos_i     (sb_axi_arqos_veer    [1]),

    .b_s_axi_rvalid_o    (sb_axi_rvalid_veer   [1]),
    .b_s_axi_rready_i    (sb_axi_rready_veer   [1]),
    .b_s_axi_rid_o       (sb_axi_rid_veer      [1]),
    .b_s_axi_rdata_o     (sb_axi_rdata_veer    [1]),
    .b_s_axi_rresp_o     (sb_axi_rresp_veer    [1]),
    .b_s_axi_rlast_o     (sb_axi_rlast_veer    [1]),


    .c_s_axi_awvalid_i   (sb_axi_awvalid_veer  [2]),
    .c_s_axi_awready_o   (sb_axi_awready_veer  [2]),
    .c_s_axi_awid_i      (sb_axi_awid_veer     [2]),
    .c_s_axi_awaddr_i    (sb_axi_awaddr_veer   [2]),
    .c_s_axi_awregion_i  (sb_axi_awregion_veer [2]),
    .c_s_axi_awlen_i     (sb_axi_awlen_veer    [2]),
    .c_s_axi_awsize_i    (sb_axi_awsize_veer   [2]),
    .c_s_axi_awburst_i   (sb_axi_awburst_veer  [2]),
    .c_s_axi_awlock_i    (sb_axi_awlock_veer   [2]),
    .c_s_axi_awcache_i   (sb_axi_awcache_veer  [2]),
    .c_s_axi_awprot_i    (sb_axi_awprot_veer   [2]),
    .c_s_axi_awqos_i     (sb_axi_awqos_veer    [2]),

    .c_s_axi_wvalid_i    (sb_axi_wvalid_veer   [2]),
    .c_s_axi_wready_o    (sb_axi_wready_veer   [2]),
    .c_s_axi_wdata_i     (sb_axi_wdata_veer    [2]),
    .c_s_axi_wstrb_i     (sb_axi_wstrb_veer    [2]),
    .c_s_axi_wlast_i     (sb_axi_wlast_veer    [2]),

    .c_s_axi_bvalid_o    (sb_axi_bvalid_veer   [2]),
    .c_s_axi_bready_i    (sb_axi_bready_veer   [2]),
    .c_s_axi_bresp_o     (sb_axi_bresp_veer    [2]),
    .c_s_axi_bid_o       (sb_axi_bid_veer      [2]),

    .c_s_axi_arvalid_i   (sb_axi_arvalid_veer  [2]),
    .c_s_axi_arready_o   (sb_axi_arready_veer  [2]),
    .c_s_axi_arid_i      (sb_axi_arid_veer     [2]),
    .c_s_axi_araddr_i    (sb_axi_araddr_veer   [2]),
    .c_s_axi_arregion_i  (sb_axi_arregion_veer [2]),
    .c_s_axi_arlen_i     (sb_axi_arlen_veer    [2]),
    .c_s_axi_arsize_i    (sb_axi_arsize_veer   [2]),
    .c_s_axi_arburst_i   (sb_axi_arburst_veer  [2]),
    .c_s_axi_arlock_i    (sb_axi_arlock_veer   [2]),
    .c_s_axi_arcache_i   (sb_axi_arcache_veer  [2]),
    .c_s_axi_arprot_i    (sb_axi_arprot_veer   [2]),
    .c_s_axi_arqos_i     (sb_axi_arqos_veer    [2]),

    .c_s_axi_rvalid_o    (sb_axi_rvalid_veer   [2]),
    .c_s_axi_rready_i    (sb_axi_rready_veer   [2]),
    .c_s_axi_rid_o       (sb_axi_rid_veer      [2]),
    .c_s_axi_rdata_o     (sb_axi_rdata_veer    [2]),
    .c_s_axi_rresp_o     (sb_axi_rresp_veer    [2]),
    .c_s_axi_rlast_o     (sb_axi_rlast_veer    [2]),


    .m_axi_awvalid_o     (sb_axi_awvalid_int),
    .m_axi_awready_i     (sb_axi_awready_int),
    .m_axi_awid_o        (sb_axi_awid_int),
    .m_axi_awaddr_o      (sb_axi_awaddr_int),
    .m_axi_awregion_o    (sb_axi_awregion_int),
    .m_axi_awlen_o       (sb_axi_awlen_int),
    .m_axi_awsize_o      (sb_axi_awsize_int),
    .m_axi_awburst_o     (sb_axi_awburst_int),
    .m_axi_awlock_o      (sb_axi_awlock_int),
    .m_axi_awcache_o     (sb_axi_awcache_int),
    .m_axi_awprot_o      (sb_axi_awprot_int),
    .m_axi_awqos_o       (sb_axi_awqos_int),

    .m_axi_wvalid_o      (sb_axi_wvalid_int),
    .m_axi_wready_i      (sb_axi_wready_int),
    .m_axi_wdata_o       (sb_axi_wdata_int),
    .m_axi_wstrb_o       (sb_axi_wstrb_int),
    .m_axi_wlast_o       (sb_axi_wlast_int),

    .m_axi_bvalid_i      (sb_axi_bvalid_int),
    .m_axi_bready_o      (sb_axi_bready_int),
    .m_axi_bresp_i       (sb_axi_bresp_int),
    .m_axi_bid_i         (sb_axi_bid_int),

    .m_axi_arvalid_o     (sb_axi_arvalid_int),
    .m_axi_arready_i     (sb_axi_arready_int),
    .m_axi_arid_o        (sb_axi_arid_int),
    .m_axi_araddr_o      (sb_axi_araddr_int),
    .m_axi_arregion_o    (sb_axi_arregion_int),
    .m_axi_arlen_o       (sb_axi_arlen_int),
    .m_axi_arsize_o      (sb_axi_arsize_int),
    .m_axi_arburst_o     (sb_axi_arburst_int),
    .m_axi_arlock_o      (sb_axi_arlock_int),
    .m_axi_arcache_o     (sb_axi_arcache_int),
    .m_axi_arprot_o      (sb_axi_arprot_int),
    .m_axi_arqos_o       (sb_axi_arqos_int),

    .m_axi_rvalid_i      (sb_axi_rvalid_int),
    .m_axi_rready_o      (sb_axi_rready_int),
    .m_axi_rid_i         (sb_axi_rid_int),
    .m_axi_rdata_i       (sb_axi_rdata_int),
    .m_axi_rresp_i       (sb_axi_rresp_int),
    .m_axi_rlast_i       (sb_axi_rlast_int),


    .a_s_axi_fault_o     (sb_axi_fault_q[0]),
    .b_s_axi_fault_o     (sb_axi_fault_q[1]),
    .c_s_axi_fault_o     (sb_axi_fault_q[2]),

    .a_s_axi_fault_i     (sb_axi_fault_d[0]),
    .b_s_axi_fault_i     (sb_axi_fault_d[1]),
    .c_s_axi_fault_i     (sb_axi_fault_d[2]),

    .a_s_axi_fault_clr_i (sb_axi_fault_clr[0]),
    .b_s_axi_fault_clr_i (sb_axi_fault_clr[1]),
    .c_s_axi_fault_clr_i (sb_axi_fault_clr[2])
  );

  // DMA AXI
  el2_tmr_axi_s #(
    .AddrWidth  (32),
    .DataWidth  (64),
    .IdWidth    (pt.DMA_BUS_TAG)

  ) x_dma_axi (
    .clk_i  (free_l2clk),
    .rst_ni (rst_l),

    .a_m_axi_awvalid_o   (dma_axi_awvalid_veer  [0]),
    .a_m_axi_awready_i   (dma_axi_awready_veer  [0]),
    .a_m_axi_awid_o      (dma_axi_awid_veer     [0]),
    .a_m_axi_awaddr_o    (dma_axi_awaddr_veer   [0]),
    .a_m_axi_awregion_o  (),
    .a_m_axi_awlen_o     (dma_axi_awlen_veer    [0]),
    .a_m_axi_awsize_o    (dma_axi_awsize_veer   [0]),
    .a_m_axi_awburst_o   (dma_axi_awburst_veer  [0]),
    .a_m_axi_awlock_o    (),
    .a_m_axi_awcache_o   (),
    .a_m_axi_awprot_o    (dma_axi_awprot_veer   [0]),
    .a_m_axi_awqos_o     (),

    .a_m_axi_wvalid_o    (dma_axi_wvalid_veer   [0]),
    .a_m_axi_wready_i    (dma_axi_wready_veer   [0]),
    .a_m_axi_wdata_o     (dma_axi_wdata_veer    [0]),
    .a_m_axi_wstrb_o     (dma_axi_wstrb_veer    [0]),
    .a_m_axi_wlast_o     (dma_axi_wlast_veer    [0]),

    .a_m_axi_bvalid_i    (dma_axi_bvalid_veer   [0]),
    .a_m_axi_bready_o    (dma_axi_bready_veer   [0]),
    .a_m_axi_bresp_i     (dma_axi_bresp_veer    [0]),
    .a_m_axi_bid_i       (dma_axi_bid_veer      [0]),

    .a_m_axi_arvalid_o   (dma_axi_arvalid_veer  [0]),
    .a_m_axi_arready_i   (dma_axi_arready_veer  [0]),
    .a_m_axi_arid_o      (dma_axi_arid_veer     [0]),
    .a_m_axi_araddr_o    (dma_axi_araddr_veer   [0]),
    .a_m_axi_arregion_o  (),
    .a_m_axi_arlen_o     (dma_axi_arlen_veer    [0]),
    .a_m_axi_arsize_o    (dma_axi_arsize_veer   [0]),
    .a_m_axi_arburst_o   (dma_axi_arburst_veer  [0]),
    .a_m_axi_arlock_o    (),
    .a_m_axi_arcache_o   (),
    .a_m_axi_arprot_o    (dma_axi_arprot_veer   [0]),
    .a_m_axi_arqos_o     (),

    .a_m_axi_rvalid_i    (dma_axi_rvalid_veer   [0]),
    .a_m_axi_rready_o    (dma_axi_rready_veer   [0]),
    .a_m_axi_rid_i       (dma_axi_rid_veer      [0]),
    .a_m_axi_rdata_i     (dma_axi_rdata_veer    [0]),
    .a_m_axi_rresp_i     (dma_axi_rresp_veer    [0]),
    .a_m_axi_rlast_i     (dma_axi_rlast_veer    [0]),


    .b_m_axi_awvalid_o   (dma_axi_awvalid_veer  [1]),
    .b_m_axi_awready_i   (dma_axi_awready_veer  [1]),
    .b_m_axi_awid_o      (dma_axi_awid_veer     [1]),
    .b_m_axi_awaddr_o    (dma_axi_awaddr_veer   [1]),
    .b_m_axi_awregion_o  (),
    .b_m_axi_awlen_o     (dma_axi_awlen_veer    [1]),
    .b_m_axi_awsize_o    (dma_axi_awsize_veer   [1]),
    .b_m_axi_awburst_o   (dma_axi_awburst_veer  [1]),
    .b_m_axi_awlock_o    (),
    .b_m_axi_awcache_o   (),
    .b_m_axi_awprot_o    (dma_axi_awprot_veer   [1]),
    .b_m_axi_awqos_o     (),

    .b_m_axi_wvalid_o    (dma_axi_wvalid_veer   [1]),
    .b_m_axi_wready_i    (dma_axi_wready_veer   [1]),
    .b_m_axi_wdata_o     (dma_axi_wdata_veer    [1]),
    .b_m_axi_wstrb_o     (dma_axi_wstrb_veer    [1]),
    .b_m_axi_wlast_o     (dma_axi_wlast_veer    [1]),

    .b_m_axi_bvalid_i    (dma_axi_bvalid_veer   [1]),
    .b_m_axi_bready_o    (dma_axi_bready_veer   [1]),
    .b_m_axi_bresp_i     (dma_axi_bresp_veer    [1]),
    .b_m_axi_bid_i       (dma_axi_bid_veer      [1]),

    .b_m_axi_arvalid_o   (dma_axi_arvalid_veer  [1]),
    .b_m_axi_arready_i   (dma_axi_arready_veer  [1]),
    .b_m_axi_arid_o      (dma_axi_arid_veer     [1]),
    .b_m_axi_araddr_o    (dma_axi_araddr_veer   [1]),
    .b_m_axi_arregion_o  (),
    .b_m_axi_arlen_o     (dma_axi_arlen_veer    [1]),
    .b_m_axi_arsize_o    (dma_axi_arsize_veer   [1]),
    .b_m_axi_arburst_o   (dma_axi_arburst_veer  [1]),
    .b_m_axi_arlock_o    (),
    .b_m_axi_arcache_o   (),
    .b_m_axi_arprot_o    (dma_axi_arprot_veer   [1]),
    .b_m_axi_arqos_o     (),

    .b_m_axi_rvalid_i    (dma_axi_rvalid_veer   [1]),
    .b_m_axi_rready_o    (dma_axi_rready_veer   [1]),
    .b_m_axi_rid_i       (dma_axi_rid_veer      [1]),
    .b_m_axi_rdata_i     (dma_axi_rdata_veer    [1]),
    .b_m_axi_rresp_i     (dma_axi_rresp_veer    [1]),
    .b_m_axi_rlast_i     (dma_axi_rlast_veer    [1]),


    .c_m_axi_awvalid_o   (dma_axi_awvalid_veer  [2]),
    .c_m_axi_awready_i   (dma_axi_awready_veer  [2]),
    .c_m_axi_awid_o      (dma_axi_awid_veer     [2]),
    .c_m_axi_awaddr_o    (dma_axi_awaddr_veer   [2]),
    .c_m_axi_awregion_o  (),
    .c_m_axi_awlen_o     (dma_axi_awlen_veer    [2]),
    .c_m_axi_awsize_o    (dma_axi_awsize_veer   [2]),
    .c_m_axi_awburst_o   (dma_axi_awburst_veer  [2]),
    .c_m_axi_awlock_o    (),
    .c_m_axi_awcache_o   (),
    .c_m_axi_awprot_o    (dma_axi_awprot_veer   [2]),
    .c_m_axi_awqos_o     (),

    .c_m_axi_wvalid_o    (dma_axi_wvalid_veer   [2]),
    .c_m_axi_wready_i    (dma_axi_wready_veer   [2]),
    .c_m_axi_wdata_o     (dma_axi_wdata_veer    [2]),
    .c_m_axi_wstrb_o     (dma_axi_wstrb_veer    [2]),
    .c_m_axi_wlast_o     (dma_axi_wlast_veer    [2]),

    .c_m_axi_bvalid_i    (dma_axi_bvalid_veer   [2]),
    .c_m_axi_bready_o    (dma_axi_bready_veer   [2]),
    .c_m_axi_bresp_i     (dma_axi_bresp_veer    [2]),
    .c_m_axi_bid_i       (dma_axi_bid_veer      [2]),

    .c_m_axi_arvalid_o   (dma_axi_arvalid_veer  [2]),
    .c_m_axi_arready_i   (dma_axi_arready_veer  [2]),
    .c_m_axi_arid_o      (dma_axi_arid_veer     [2]),
    .c_m_axi_araddr_o    (dma_axi_araddr_veer   [2]),
    .c_m_axi_arregion_o  (),
    .c_m_axi_arlen_o     (dma_axi_arlen_veer    [2]),
    .c_m_axi_arsize_o    (dma_axi_arsize_veer   [2]),
    .c_m_axi_arburst_o   (dma_axi_arburst_veer  [2]),
    .c_m_axi_arlock_o    (),
    .c_m_axi_arcache_o   (),
    .c_m_axi_arprot_o    (dma_axi_arprot_veer   [2]),
    .c_m_axi_arqos_o     (),

    .c_m_axi_rvalid_i    (dma_axi_rvalid_veer   [2]),
    .c_m_axi_rready_o    (dma_axi_rready_veer   [2]),
    .c_m_axi_rid_i       (dma_axi_rid_veer      [2]),
    .c_m_axi_rdata_i     (dma_axi_rdata_veer    [2]),
    .c_m_axi_rresp_i     (dma_axi_rresp_veer    [2]),
    .c_m_axi_rlast_i     (dma_axi_rlast_veer    [2]),


    .s_axi_awvalid_i     (dma_axi_awvalid_int),
    .s_axi_awready_o     (dma_axi_awready_int),
    .s_axi_awid_i        (dma_axi_awid_int),
    .s_axi_awaddr_i      (dma_axi_awaddr_int),
    .s_axi_awregion_i    ('0),
    .s_axi_awlen_i       (dma_axi_awlen_int),
    .s_axi_awsize_i      (dma_axi_awsize_int),
    .s_axi_awburst_i     (dma_axi_awburst_int),
    .s_axi_awlock_i      ('0),
    .s_axi_awcache_i     ('0),
    .s_axi_awprot_i      (dma_axi_awprot_int),
    .s_axi_awqos_i       ('0),

    .s_axi_wvalid_i      (dma_axi_wvalid_int),
    .s_axi_wready_o      (dma_axi_wready_int),
    .s_axi_wdata_i       (dma_axi_wdata_int),
    .s_axi_wstrb_i       (dma_axi_wstrb_int),
    .s_axi_wlast_i       (dma_axi_wlast_int),

    .s_axi_bvalid_o      (dma_axi_bvalid_int),
    .s_axi_bready_i      (dma_axi_bready_int),
    .s_axi_bresp_o       (dma_axi_bresp_int),
    .s_axi_bid_o         (dma_axi_bid_int),

    .s_axi_arvalid_i     (dma_axi_arvalid_int),
    .s_axi_arready_o     (dma_axi_arready_int),
    .s_axi_arid_i        (dma_axi_arid_int),
    .s_axi_araddr_i      (dma_axi_araddr_int),
    .s_axi_arregion_i    ('0),
    .s_axi_arlen_i       (dma_axi_arlen_int),
    .s_axi_arsize_i      (dma_axi_arsize_int),
    .s_axi_arburst_i     (dma_axi_arburst_int),
    .s_axi_arlock_i      ('0),
    .s_axi_arcache_i     ('0),
    .s_axi_arprot_i      (dma_axi_arprot_int),
    .s_axi_arqos_i       ('0),

    .s_axi_rvalid_o      (dma_axi_rvalid_int),
    .s_axi_rready_i      (dma_axi_rready_int),
    .s_axi_rid_o         (dma_axi_rid_int),
    .s_axi_rdata_o       (dma_axi_rdata_int),
    .s_axi_rresp_o       (dma_axi_rresp_int),
    .s_axi_rlast_o       (dma_axi_rlast_int),


    .a_m_axi_fault_o     (dma_axi_fault_q[0]),
    .b_m_axi_fault_o     (dma_axi_fault_q[1]),
    .c_m_axi_fault_o     (dma_axi_fault_q[2]),

    .a_m_axi_fault_i     (dma_axi_fault_d[0]),
    .b_m_axi_fault_i     (dma_axi_fault_d[1]),
    .c_m_axi_fault_i     (dma_axi_fault_d[2]),

    .a_m_axi_fault_clr_i (dma_axi_fault_clr[0]),
    .b_m_axi_fault_clr_i (dma_axi_fault_clr[1]),
    .c_m_axi_fault_clr_i (dma_axi_fault_clr[2])
  );

endmodule
`endif
