// SPDX-License-Identifier: Apache-2.0
// Copyright 2020 Western Digital Corporation or its affiliates.
// Copyright (c) 2023 Antmicro <www.antmicro.com>
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//********************************************************************************
// $Id$
//
// Function: Top wrapper file with el2_veer/mem instantiated inside
// Comments:
//
//********************************************************************************
module el2_veer_wrapper
import el2_pkg::*;
 #(
`include "el2_param.vh"
)
(
   input logic                             clk,
   input logic                             rst_l,
   input logic                             dbg_rst_l,
   input logic [31:1]                      rst_vec,
   input logic                             nmi_int,
   input logic [31:1]                      nmi_vec,
   input logic [31:1]                      jtag_id,


   output logic [31:0]                     trace_rv_i_insn_ip,
   output logic [31:0]                     trace_rv_i_address_ip,
   output logic                            trace_rv_i_valid_ip,
   output logic                            trace_rv_i_exception_ip,
   output logic [4:0]                      trace_rv_i_ecause_ip,
   output logic                            trace_rv_i_interrupt_ip,
   output logic [31:0]                     trace_rv_i_tval_ip,

   // Bus signals
`ifdef RV_BUILD_AXI4
   //-------------------------- LSU AXI signals--------------------------
   // AXI Write Channels
   output logic                            lsu_axi_awvalid,
   input  logic                            lsu_axi_awready,
   output logic [pt.LSU_BUS_TAG-1:0]       lsu_axi_awid,
   output logic [31:0]                     lsu_axi_awaddr,
   output logic [3:0]                      lsu_axi_awregion,
   output logic [7:0]                      lsu_axi_awlen,
   output logic [2:0]                      lsu_axi_awsize,
   output logic [1:0]                      lsu_axi_awburst,
   output logic                            lsu_axi_awlock,
   output logic [3:0]                      lsu_axi_awcache,
   output logic [2:0]                      lsu_axi_awprot,
   output logic [3:0]                      lsu_axi_awqos,

   output logic                            lsu_axi_wvalid,
   input  logic                            lsu_axi_wready,
   output logic [63:0]                     lsu_axi_wdata,
   output logic [7:0]                      lsu_axi_wstrb,
   output logic                            lsu_axi_wlast,

   input  logic                            lsu_axi_bvalid,
   output logic                            lsu_axi_bready,
   input  logic [1:0]                      lsu_axi_bresp,
   input  logic [pt.LSU_BUS_TAG-1:0]       lsu_axi_bid,

   // AXI Read Channels
   output logic                            lsu_axi_arvalid,
   input  logic                            lsu_axi_arready,
   output logic [pt.LSU_BUS_TAG-1:0]       lsu_axi_arid,
   output logic [31:0]                     lsu_axi_araddr,
   output logic [3:0]                      lsu_axi_arregion,
   output logic [7:0]                      lsu_axi_arlen,
   output logic [2:0]                      lsu_axi_arsize,
   output logic [1:0]                      lsu_axi_arburst,
   output logic                            lsu_axi_arlock,
   output logic [3:0]                      lsu_axi_arcache,
   output logic [2:0]                      lsu_axi_arprot,
   output logic [3:0]                      lsu_axi_arqos,

   input  logic                            lsu_axi_rvalid,
   output logic                            lsu_axi_rready,
   input  logic [pt.LSU_BUS_TAG-1:0]       lsu_axi_rid,
   input  logic [63:0]                     lsu_axi_rdata,
   input  logic [1:0]                      lsu_axi_rresp,
   input  logic                            lsu_axi_rlast,

   //-------------------------- IFU AXI signals--------------------------
   // AXI Write Channels
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

   // AXI Read Channels
   output logic                            ifu_axi_arvalid,
   input  logic                            ifu_axi_arready,
   output logic [pt.IFU_BUS_TAG-1:0]       ifu_axi_arid,
   output logic [31:0]                     ifu_axi_araddr,
   output logic [3:0]                      ifu_axi_arregion,
   output logic [7:0]                      ifu_axi_arlen,
   output logic [2:0]                      ifu_axi_arsize,
   output logic [1:0]                      ifu_axi_arburst,
   output logic                            ifu_axi_arlock,
   output logic [3:0]                      ifu_axi_arcache,
   output logic [2:0]                      ifu_axi_arprot,
   output logic [3:0]                      ifu_axi_arqos,

   input  logic                            ifu_axi_rvalid,
   output logic                            ifu_axi_rready,
   input  logic [pt.IFU_BUS_TAG-1:0]       ifu_axi_rid,
   input  logic [63:0]                     ifu_axi_rdata,
   input  logic [1:0]                      ifu_axi_rresp,
   input  logic                            ifu_axi_rlast,

   //-------------------------- SB AXI signals--------------------------
   // AXI Write Channels
   output logic                            sb_axi_awvalid,
   input  logic                            sb_axi_awready,
   output logic [pt.SB_BUS_TAG-1:0]        sb_axi_awid,
   output logic [31:0]                     sb_axi_awaddr,
   output logic [3:0]                      sb_axi_awregion,
   output logic [7:0]                      sb_axi_awlen,
   output logic [2:0]                      sb_axi_awsize,
   output logic [1:0]                      sb_axi_awburst,
   output logic                            sb_axi_awlock,
   output logic [3:0]                      sb_axi_awcache,
   output logic [2:0]                      sb_axi_awprot,
   output logic [3:0]                      sb_axi_awqos,

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
   output logic [pt.SB_BUS_TAG-1:0]        sb_axi_arid,
   output logic [31:0]                     sb_axi_araddr,
   output logic [3:0]                      sb_axi_arregion,
   output logic [7:0]                      sb_axi_arlen,
   output logic [2:0]                      sb_axi_arsize,
   output logic [1:0]                      sb_axi_arburst,
   output logic                            sb_axi_arlock,
   output logic [3:0]                      sb_axi_arcache,
   output logic [2:0]                      sb_axi_arprot,
   output logic [3:0]                      sb_axi_arqos,

   input  logic                            sb_axi_rvalid,
   output logic                            sb_axi_rready,
   input  logic [pt.SB_BUS_TAG-1:0]        sb_axi_rid,
   input  logic [63:0]                     sb_axi_rdata,
   input  logic [1:0]                      sb_axi_rresp,
   input  logic                            sb_axi_rlast,

   //-------------------------- DMA AXI signals--------------------------
   // AXI Write Channels
   input  logic                            dma_axi_awvalid,
   output logic                            dma_axi_awready,
   input  logic [pt.DMA_BUS_TAG-1:0]       dma_axi_awid,
   input  logic [31:0]                     dma_axi_awaddr,
   input  logic [2:0]                      dma_axi_awsize,
   input  logic [2:0]                      dma_axi_awprot,
   input  logic [7:0]                      dma_axi_awlen,
   input  logic [1:0]                      dma_axi_awburst,


   input  logic                            dma_axi_wvalid,
   output logic                            dma_axi_wready,
   input  logic [63:0]                     dma_axi_wdata,
   input  logic [7:0]                      dma_axi_wstrb,
   input  logic                            dma_axi_wlast,

   output logic                            dma_axi_bvalid,
   input  logic                            dma_axi_bready,
   output logic [1:0]                      dma_axi_bresp,
   output logic [pt.DMA_BUS_TAG-1:0]       dma_axi_bid,

   // AXI Read Channels
   input  logic                            dma_axi_arvalid,
   output logic                            dma_axi_arready,
   input  logic [pt.DMA_BUS_TAG-1:0]       dma_axi_arid,
   input  logic [31:0]                     dma_axi_araddr,
   input  logic [2:0]                      dma_axi_arsize,
   input  logic [2:0]                      dma_axi_arprot,
   input  logic [7:0]                      dma_axi_arlen,
   input  logic [1:0]                      dma_axi_arburst,

   output logic                            dma_axi_rvalid,
   input  logic                            dma_axi_rready,
   output logic [pt.DMA_BUS_TAG-1:0]       dma_axi_rid,
   output logic [63:0]                     dma_axi_rdata,
   output logic [1:0]                      dma_axi_rresp,
   output logic                            dma_axi_rlast,
`endif

`ifdef RV_BUILD_AHB_LITE
 //// AHB LITE BUS
   output logic [31:0]                     haddr,
   output logic [2:0]                      hburst,
   output logic                            hmastlock,
   output logic [3:0]                      hprot,
   output logic [2:0]                      hsize,
   output logic [1:0]                      htrans,
   output logic                            hwrite,

   input logic [63:0]                      hrdata,
   input logic                             hready,
   input logic                             hresp,

   // LSU AHB Master
   output logic [31:0]                     lsu_haddr,
   output logic [2:0]                      lsu_hburst,
   output logic                            lsu_hmastlock,
   output logic [3:0]                      lsu_hprot,
   output logic [2:0]                      lsu_hsize,
   output logic [1:0]                      lsu_htrans,
   output logic                            lsu_hwrite,
   output logic [63:0]                     lsu_hwdata,

   input logic [63:0]                      lsu_hrdata,
   input logic                             lsu_hready,
   input logic                             lsu_hresp,
   // Debug Syster Bus AHB
   output logic [31:0]                     sb_haddr,
   output logic [2:0]                      sb_hburst,
   output logic                            sb_hmastlock,
   output logic [3:0]                      sb_hprot,
   output logic [2:0]                      sb_hsize,
   output logic [1:0]                      sb_htrans,
   output logic                            sb_hwrite,
   output logic [63:0]                     sb_hwdata,

   input  logic [63:0]                     sb_hrdata,
   input  logic                            sb_hready,
   input  logic                            sb_hresp,

   // DMA Slave
   input logic                             dma_hsel,
   input logic [31:0]                      dma_haddr,
   input logic [2:0]                       dma_hburst,
   input logic                             dma_hmastlock,
   input logic [3:0]                       dma_hprot,
   input logic [2:0]                       dma_hsize,
   input logic [1:0]                       dma_htrans,
   input logic                             dma_hwrite,
   input logic [63:0]                      dma_hwdata,
   input logic                             dma_hreadyin,

   output logic [63:0]                     dma_hrdata,
   output logic                            dma_hreadyout,
   output logic                            dma_hresp,
`endif
   // clk ratio signals
   input logic                             lsu_bus_clk_en, // Clock ratio b/w cpu core clk & AHB master interface
   input logic                             ifu_bus_clk_en, // Clock ratio b/w cpu core clk & AHB master interface
   input logic                             dbg_bus_clk_en, // Clock ratio b/w cpu core clk & AHB master interface
   input logic                             dma_bus_clk_en, // Clock ratio b/w cpu core clk & AHB slave interface

   // ICCM/DCCM ECC status
   output logic                            iccm_ecc_single_error,
   output logic                            iccm_ecc_double_error,
   output logic                            dccm_ecc_single_error,
   output logic                            dccm_ecc_double_error,

 // all of these test inputs are brought to top-level; must be tied off based on usage by physical design (ie. icache or not, iccm or not, dccm or not)

   input                                   el2_ic_data_ext_in_pkt_t  [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0] ic_data_ext_in_pkt,
   input                                   el2_ic_tag_ext_in_pkt_t  [pt.ICACHE_NUM_WAYS-1:0] ic_tag_ext_in_pkt,

   input logic                             timer_int,
   input logic                             soft_int,
   input logic [pt.PIC_TOTAL_INT:1]        extintsrc_req,

   output logic                            dec_tlu_perfcnt0, // toggles when slot0 perf counter 0 has an event inc
   output logic                            dec_tlu_perfcnt1,
   output logic                            dec_tlu_perfcnt2,
   output logic                            dec_tlu_perfcnt3,

   // ports added by the soc team
   input logic                             jtag_tck,    // JTAG clk
   input logic                             jtag_tms,    // JTAG TMS
   input logic                             jtag_tdi,    // JTAG tdi
   input logic                             jtag_trst_n, // JTAG Reset
   output logic                            jtag_tdo,    // JTAG TDO
   output logic                            jtag_tdoEn,  // JTAG Test Data Output enable

   input logic [31:4] core_id,

   // Memory Export Interface
   el2_mem_if.veer_sram_src                el2_mem_export,

   // external MPC halt/run interface
   input logic                             mpc_debug_halt_req, // Async halt request
   input logic                             mpc_debug_run_req,  // Async run request
   input logic                             mpc_reset_run_req,  // Run/halt after reset
   output logic                            mpc_debug_halt_ack, // Halt ack
   output logic                            mpc_debug_run_ack,  // Run ack
   output logic                            debug_brkpt_status, // debug breakpoint

   input logic                             i_cpu_halt_req,      // Async halt req to CPU
   output logic                            o_cpu_halt_ack,      // core response to halt
   output logic                            o_cpu_halt_status,   // 1'b1 indicates core is halted
   output logic                            o_debug_mode_status, // Core to the PMU that core is in debug mode. When core is in debug mode, the PMU should refrain from sendng a halt or run request
   input logic                             i_cpu_run_req, // Async restart req to CPU
   output logic                            o_cpu_run_ack, // Core response to run req
   input logic                             scan_mode,     // To enable scan mode
   input logic                             mbist_mode,    // to enable mbist

   // DMI port for uncore
   input logic                             dmi_uncore_enable,
   output logic                            dmi_uncore_en,
   output logic                            dmi_uncore_wr_en,
   output logic                     [ 6:0] dmi_uncore_addr,
   output logic                     [31:0] dmi_uncore_wdata,
   input logic                      [31:0] dmi_uncore_rdata
);

   logic                             active_l2clk;
   logic                             free_l2clk;

   // DCCM ports
   logic         dccm_wren;
   logic         dccm_rden;
   logic [pt.DCCM_BITS-1:0]         dccm_wr_addr_lo;
   logic [pt.DCCM_BITS-1:0]         dccm_wr_addr_hi;
   logic [pt.DCCM_BITS-1:0]         dccm_rd_addr_lo;
   logic [pt.DCCM_BITS-1:0]         dccm_rd_addr_hi;
   logic [pt.DCCM_FDATA_WIDTH-1:0]  dccm_wr_data_lo;
   logic [pt.DCCM_FDATA_WIDTH-1:0]  dccm_wr_data_hi;

   logic [pt.DCCM_FDATA_WIDTH-1:0]  dccm_rd_data_lo;
   logic [pt.DCCM_FDATA_WIDTH-1:0]  dccm_rd_data_hi;

   // PIC ports

   // Icache & Itag ports
   logic [31:1]  ic_rw_addr;
   logic [pt.ICACHE_NUM_WAYS-1:0]   ic_wr_en  ;     // Which way to write
   logic         ic_rd_en ;


   logic [pt.ICACHE_NUM_WAYS-1:0]   ic_tag_valid;   // Valid from the I$ tag valid outside (in flops).

   logic [pt.ICACHE_NUM_WAYS-1:0]   ic_rd_hit;      // ic_rd_hit[3:0]
   logic         ic_tag_perr;                       // Ic tag parity error

   logic [pt.ICACHE_INDEX_HI:3]  ic_debug_addr;     // Read/Write addresss to the Icache.
   logic         ic_debug_rd_en;                    // Icache debug rd
   logic         ic_debug_wr_en;                    // Icache debug wr
   logic         ic_debug_tag_array;                // Debug tag array
   logic [pt.ICACHE_NUM_WAYS-1:0]   ic_debug_way;   // Debug way. Rd or Wr.

   logic [25:0]  ictag_debug_rd_data;               // Debug icache tag.
   logic [pt.ICACHE_BANKS_WAY-1:0][70:0]  ic_wr_data;
   logic [63:0]  ic_rd_data;
   logic [70:0]  ic_debug_rd_data;                  // Data read from Icache. 2x64bits + parity bits. F2 stage. With ECC
   logic [70:0]  ic_debug_wr_data;                  // Debug wr cache.

   logic [pt.ICACHE_BANKS_WAY-1:0] ic_eccerr;       // ecc error per bank
   logic [pt.ICACHE_BANKS_WAY-1:0] ic_parerr;       // parity error per bank

   logic [63:0]  ic_premux_data;
   logic         ic_sel_premux_data;

   // ICCM ports
   logic [pt.ICCM_BITS-1:1]    iccm_rw_addr;
   logic           iccm_wren;
   logic           iccm_rden;
   logic [2:0]     iccm_wr_size;
   logic [77:0]    iccm_wr_data;
   logic           iccm_buf_correct_ecc;
   logic           iccm_correction_state;

   logic [63:0]    iccm_rd_data;
   logic [77:0]    iccm_rd_data_ecc;

   logic        core_rst_l;                         // Core reset including rst_l and dbg_rst_l

   logic        dccm_clk_override;
   logic        icm_clk_override;
   logic        dec_tlu_core_ecc_disable;


   // zero out the signals not presented at the wrapper instantiation level
`ifdef RV_BUILD_AXI4

 //// AHB LITE BUS
   logic [31:0]              haddr;
   logic [2:0]               hburst;
   logic                     hmastlock;
   logic [3:0]               hprot;
   logic [2:0]               hsize;
   logic [1:0]               htrans;
   logic                     hwrite;

   logic [63:0]              hrdata;
   logic                     hready;
   logic                     hresp;

   // LSU AHB Master
   logic [31:0]              lsu_haddr;
   logic [2:0]               lsu_hburst;
   logic                     lsu_hmastlock;
   logic [3:0]               lsu_hprot;
   logic [2:0]               lsu_hsize;
   logic [1:0]               lsu_htrans;
   logic                     lsu_hwrite;
   logic [63:0]              lsu_hwdata;

   logic [63:0]              lsu_hrdata;
   logic                     lsu_hready;
   logic                     lsu_hresp;
   // Debug Syster Bus AHB
   logic [31:0]              sb_haddr;
   logic [2:0]               sb_hburst;
   logic                     sb_hmastlock;
   logic [3:0]               sb_hprot;
   logic [2:0]               sb_hsize;
   logic [1:0]               sb_htrans;
   logic                     sb_hwrite;
   logic [63:0]              sb_hwdata;

    logic [63:0]             sb_hrdata;
    logic                    sb_hready;
    logic                    sb_hresp;

   // DMA Slave
   logic                     dma_hsel;
   logic [31:0]              dma_haddr;
   logic [2:0]               dma_hburst;
   logic                     dma_hmastlock;
   logic [3:0]               dma_hprot;
   logic [2:0]               dma_hsize;
   logic [1:0]               dma_htrans;
   logic                     dma_hwrite;
   logic [63:0]              dma_hwdata;
   logic                     dma_hreadyin;

   logic [63:0]              dma_hrdata;
   logic                     dma_hreadyout;
   logic                     dma_hresp;



   // AHB
   assign  hrdata[63:0]                           = '0;
   assign  hready                                 = '0;
   assign  hresp                                  = '0;
   // LSU
   assign  lsu_hrdata[63:0]                       = '0;
   assign  lsu_hready                             = '0;
   assign  lsu_hresp                              = '0;
   // Debu
   assign  sb_hrdata[63:0]                        = '0;
   assign  sb_hready                              = '0;
   assign  sb_hresp                               = '0;

   // DMA
   assign  dma_hsel                               = '0;
   assign  dma_haddr[31:0]                        = '0;
   assign  dma_hburst[2:0]                        = '0;
   assign  dma_hmastlock                          = '0;
   assign  dma_hprot[3:0]                         = '0;
   assign  dma_hsize[2:0]                         = '0;
   assign  dma_htrans[1:0]                        = '0;
   assign  dma_hwrite                             = '0;
   assign  dma_hwdata[63:0]                       = '0;
   assign  dma_hreadyin                           = '0;

`endif //  `ifdef RV_BUILD_AXI4


`ifdef RV_BUILD_AHB_LITE
   wire                            lsu_axi_awvalid;
   wire                            lsu_axi_awready;
   wire [pt.LSU_BUS_TAG-1:0]       lsu_axi_awid;
   wire [31:0]                     lsu_axi_awaddr;
   wire [3:0]                      lsu_axi_awregion;
   wire [7:0]                      lsu_axi_awlen;
   wire [2:0]                      lsu_axi_awsize;
   wire [1:0]                      lsu_axi_awburst;
   wire                            lsu_axi_awlock;
   wire [3:0]                      lsu_axi_awcache;
   wire [2:0]                      lsu_axi_awprot;
   wire [3:0]                      lsu_axi_awqos;


   wire                            lsu_axi_wvalid;
   wire                            lsu_axi_wready;
   wire [63:0]                     lsu_axi_wdata;
   wire [7:0]                      lsu_axi_wstrb;
   wire                            lsu_axi_wlast;

   wire                            lsu_axi_bvalid;
   wire                            lsu_axi_bready;
   wire [1:0]                      lsu_axi_bresp;
   wire [pt.LSU_BUS_TAG-1:0]       lsu_axi_bid;

   // AXI Read Channels
   wire                            lsu_axi_arvalid;
   wire                            lsu_axi_arready;
   wire [pt.LSU_BUS_TAG-1:0]       lsu_axi_arid;
   wire [31:0]                     lsu_axi_araddr;
   wire [3:0]                      lsu_axi_arregion;
   wire [7:0]                      lsu_axi_arlen;
   wire [2:0]                      lsu_axi_arsize;
   wire [1:0]                      lsu_axi_arburst;
   wire                            lsu_axi_arlock;
   wire [3:0]                      lsu_axi_arcache;
   wire [2:0]                      lsu_axi_arprot;
   wire [3:0]                      lsu_axi_arqos;

   wire                            lsu_axi_rvalid;
   wire                            lsu_axi_rready;
   wire [pt.LSU_BUS_TAG-1:0]       lsu_axi_rid;
   wire [63:0]                     lsu_axi_rdata;
   wire [1:0]                      lsu_axi_rresp;
   wire                            lsu_axi_rlast;

   assign                          lsu_axi_awready = '0;
   assign                          lsu_axi_wready = '0;
   assign                          lsu_axi_bvalid = '0;
   assign                          lsu_axi_bresp = '0;
   assign                          lsu_axi_bid = {pt.LSU_BUS_TAG{1'b0}};
   assign                          lsu_axi_arready = '0;
   assign                          lsu_axi_rvalid = '0;
   assign                          lsu_axi_rid = {pt.LSU_BUS_TAG{1'b0}};
   assign                          lsu_axi_rdata = '0;
   assign                          lsu_axi_rresp = '0;
   assign                          lsu_axi_rlast = '0;
   //-------------------------- IFU AXI signals--------------------------
   // AXI Write Channels
   wire                            ifu_axi_awvalid;
   wire                            ifu_axi_awready;
   wire [pt.IFU_BUS_TAG-1:0]       ifu_axi_awid;
   wire [31:0]                     ifu_axi_awaddr;
   wire [3:0]                      ifu_axi_awregion;
   wire [7:0]                      ifu_axi_awlen;
   wire [2:0]                      ifu_axi_awsize;
   wire [1:0]                      ifu_axi_awburst;
   wire                            ifu_axi_awlock;
   wire [3:0]                      ifu_axi_awcache;
   wire [2:0]                      ifu_axi_awprot;
   wire [3:0]                      ifu_axi_awqos;

   wire                            ifu_axi_wvalid;
   wire                            ifu_axi_wready;
   wire [63:0]                     ifu_axi_wdata;
   wire [7:0]                      ifu_axi_wstrb;
   wire                            ifu_axi_wlast;

   wire                            ifu_axi_bvalid;
   wire                            ifu_axi_bready;
   wire [1:0]                      ifu_axi_bresp;
   wire [pt.IFU_BUS_TAG-1:0]      ifu_axi_bid;

   // AXI Read Channels
   wire                            ifu_axi_arvalid;
   wire                            ifu_axi_arready;
   wire [pt.IFU_BUS_TAG-1:0]       ifu_axi_arid;
   wire [31:0]                     ifu_axi_araddr;
   wire [3:0]                      ifu_axi_arregion;
   wire [7:0]                      ifu_axi_arlen;
   wire [2:0]                      ifu_axi_arsize;
   wire [1:0]                      ifu_axi_arburst;
   wire                            ifu_axi_arlock;
   wire [3:0]                      ifu_axi_arcache;
   wire [2:0]                      ifu_axi_arprot;
   wire [3:0]                      ifu_axi_arqos;

   wire                            ifu_axi_rvalid;
   wire                            ifu_axi_rready;
   wire [pt.IFU_BUS_TAG-1:0]       ifu_axi_rid;
   wire [63:0]                     ifu_axi_rdata;
   wire [1:0]                      ifu_axi_rresp;
   wire                            ifu_axi_rlast;

   assign                          ifu_axi_bvalid = '0;
   assign                          ifu_axi_bresp = '0;
   assign                          ifu_axi_bid = {pt.IFU_BUS_TAG{1'b0}};
   assign                          ifu_axi_arready = '0;
   assign                          ifu_axi_rvalid = '0;
   assign                          ifu_axi_rid = {pt.IFU_BUS_TAG{1'b0}};
   assign                          ifu_axi_rdata = 0;
   assign                          ifu_axi_rresp = '0;
   assign                          ifu_axi_rlast = '0;
   //-------------------------- SB AXI signals--------------------------
   // AXI Write Channels
   wire                            sb_axi_awvalid;
   wire                            sb_axi_awready;
   wire [pt.SB_BUS_TAG-1:0]        sb_axi_awid;
   wire [31:0]                     sb_axi_awaddr;
   wire [3:0]                      sb_axi_awregion;
   wire [7:0]                      sb_axi_awlen;
   wire [2:0]                      sb_axi_awsize;
   wire [1:0]                      sb_axi_awburst;
   wire                            sb_axi_awlock;
   wire [3:0]                      sb_axi_awcache;
   wire [2:0]                      sb_axi_awprot;
   wire [3:0]                      sb_axi_awqos;

   wire                            sb_axi_wvalid;
   wire                            sb_axi_wready;
   wire [63:0]                     sb_axi_wdata;
   wire [7:0]                      sb_axi_wstrb;
   wire                            sb_axi_wlast;

   wire                            sb_axi_bvalid;
   wire                            sb_axi_bready;
   wire [1:0]                      sb_axi_bresp;
   wire [pt.SB_BUS_TAG-1:0]        sb_axi_bid;

   // AXI Read Channels
   wire                            sb_axi_arvalid;
   wire                            sb_axi_arready;
   wire [pt.SB_BUS_TAG-1:0]        sb_axi_arid;
   wire [31:0]                     sb_axi_araddr;
   wire [3:0]                      sb_axi_arregion;
   wire [7:0]                      sb_axi_arlen;
   wire [2:0]                      sb_axi_arsize;
   wire [1:0]                      sb_axi_arburst;
   wire                            sb_axi_arlock;
   wire [3:0]                      sb_axi_arcache;
   wire [2:0]                      sb_axi_arprot;
   wire [3:0]                      sb_axi_arqos;

   wire                            sb_axi_rvalid;
   wire                            sb_axi_rready;
   wire [pt.SB_BUS_TAG-1:0]        sb_axi_rid;
   wire [63:0]                     sb_axi_rdata;
   wire [1:0]                      sb_axi_rresp;
   wire                            sb_axi_rlast;

   assign                          sb_axi_awready = '0;
   assign                          sb_axi_wready = '0;
   assign                          sb_axi_bvalid = '0;
   assign                          sb_axi_bresp = '0;
   assign                          sb_axi_bid = {pt.SB_BUS_TAG{1'b0}};
   assign                          sb_axi_arready = '0;
   assign                          sb_axi_rvalid = '0;
   assign                          sb_axi_rid = {pt.SB_BUS_TAG{1'b0}};
   assign                          sb_axi_rdata = '0;
   assign                          sb_axi_rresp = '0;
   assign                          sb_axi_rlast = '0;
   //-------------------------- DMA AXI signals--------------------------
   // AXI Write Channels
   wire                         dma_axi_awvalid;
   wire                         dma_axi_awready;
   wire [pt.DMA_BUS_TAG-1:0]    dma_axi_awid;
   wire [31:0]                  dma_axi_awaddr;
   wire [2:0]                   dma_axi_awsize;
   wire [2:0]                   dma_axi_awprot;
   wire [7:0]                   dma_axi_awlen;
   wire [1:0]                   dma_axi_awburst;


   wire                         dma_axi_wvalid;
   wire                         dma_axi_wready;
   wire [63:0]                  dma_axi_wdata;
   wire [7:0]                   dma_axi_wstrb;
   wire                         dma_axi_wlast;

   assign                       dma_axi_awvalid = 1'b0;
   assign                       dma_axi_awid = {pt.DMA_BUS_TAG{1'b0}};
   assign                       dma_axi_awaddr = 32'd0;
   assign                       dma_axi_awsize = 3'd0;
   assign                       dma_axi_awprot = 3'd0;
   assign                       dma_axi_awlen = 8'd0;
   assign                       dma_axi_awburst = 2'd0;


   assign                       dma_axi_wvalid = 1'b0;
   assign                       dma_axi_wdata = 64'd0;
   assign                       dma_axi_wstrb = 8'd0;
   assign                       dma_axi_wlast = 1'b0;


   wire                         dma_axi_bvalid;
   wire                         dma_axi_bready;
   wire [1:0]                   dma_axi_bresp;
   wire [pt.DMA_BUS_TAG-1:0]    dma_axi_bid;

   assign                       dma_axi_bready = 1'b0;
   // AXI Read Channels
   wire                         dma_axi_arvalid;
   wire                         dma_axi_arready;
   wire [pt.DMA_BUS_TAG-1:0]    dma_axi_arid;
   wire [31:0]                  dma_axi_araddr;
   wire [2:0]                   dma_axi_arsize;
   wire [2:0]                   dma_axi_arprot;
   wire [7:0]                   dma_axi_arlen;
   wire [1:0]                   dma_axi_arburst;

   assign                       dma_axi_arvalid = 1'b0;
   assign                       dma_axi_arid = {pt.DMA_BUS_TAG{1'b0}};
   assign                       dma_axi_araddr = 32'd0;
   assign                       dma_axi_arsize = 3'd0;
   assign                       dma_axi_arprot = 3'd0;
   assign                       dma_axi_arlen = 8'd0;
   assign                       dma_axi_arburst = 2'd0;



   wire                         dma_axi_rvalid;
   wire                         dma_axi_rready;
   wire [pt.DMA_BUS_TAG-1:0]    dma_axi_rid;
   wire [63:0]                  dma_axi_rdata;
   wire [1:0]                   dma_axi_rresp;
   wire                         dma_axi_rlast;

   assign                       dma_axi_rready = 1'b0;
   // AXI
   assign ifu_axi_awready = 1'b1;
   assign ifu_axi_wready = 1'b1;
   assign ifu_axi_bvalid = '0;
   assign ifu_axi_bresp[1:0] = '0;
   assign ifu_axi_bid[pt.IFU_BUS_TAG-1:0] = '0;

`endif //  `ifdef RV_BUILD_AHB_LITE

   // DMI (core)
   logic                   dmi_en;
   logic [6:0]             dmi_addr;
   logic                   dmi_wr_en;
   logic [31:0]            dmi_wdata;
   logic [31:0]            dmi_rdata;

   // DMI (core)
   logic                   dmi_reg_en;
   logic [6:0]             dmi_reg_addr;
   logic                   dmi_reg_wr_en;
   logic [31:0]            dmi_reg_wdata;
   logic [31:0]            dmi_reg_rdata;

   // Instantiate the el2_veer core
   el2_veer #(.pt(pt)) veer (
                                .clk(clk),
                                .*
                                );

   // Instantiate the mem
   el2_mem  #(.pt(pt)) mem (
                             .clk(active_l2clk),
                             .rst_l(core_rst_l),
                             .mem_export(el2_mem_export),
                             .*
                             );


   //  JTAG/DMI instance
   dmi_wrapper  dmi_wrapper (
    // JTAG signals
    .trst_n      (jtag_trst_n),     // JTAG reset
    .tck         (jtag_tck),        // JTAG clock
    .tms         (jtag_tms),        // Test mode select
    .tdi         (jtag_tdi),        // Test Data Input
    .tdo         (jtag_tdo),        // Test Data Output
    .tdoEnable   (jtag_tdoEn),      // Test Data Output enable
    // Processor Signals
    .core_rst_n  (dbg_rst_l),       // Debug reset, active low
    .core_clk    (clk),             // Core clock
    .jtag_id     (jtag_id),         // JTAG ID
    .rd_data     (dmi_rdata),       // Read data from  Processor
    .reg_wr_data (dmi_wdata),       // Write data to Processor
    .reg_wr_addr (dmi_addr),        // Write address to Processor
    .reg_en      (dmi_en),          // Write interface bit to Processor
    .reg_wr_en   (dmi_wr_en),       // Write enable to Processor
    .dmi_hard_reset   ()
   );

   // DMI core/uncore mux
   dmi_mux dmi_mux (
    .uncore_enable      (dmi_uncore_enable),

    .dmi_en             (dmi_en),
    .dmi_wr_en          (dmi_wr_en),
    .dmi_addr           (dmi_addr),
    .dmi_wdata          (dmi_wdata),
    .dmi_rdata          (dmi_rdata),

    .dmi_core_en        (dmi_reg_en),
    .dmi_core_wr_en     (dmi_reg_wr_en),
    .dmi_core_addr      (dmi_reg_addr),
    .dmi_core_wdata     (dmi_reg_wdata),
    .dmi_core_rdata     (dmi_reg_rdata),

    .dmi_uncore_en      (dmi_uncore_en),
    .dmi_uncore_wr_en   (dmi_uncore_wr_en),
    .dmi_uncore_addr    (dmi_uncore_addr),
    .dmi_uncore_wdata   (dmi_uncore_wdata),
    .dmi_uncore_rdata   (dmi_uncore_rdata)
   );

`ifdef RV_ASSERT_ON
  // to avoid internal assertions failure at time 0
  initial begin
    $assertoff(0, veer);
    @(negedge clk) $asserton(0, veer);
  end
`endif

endmodule
