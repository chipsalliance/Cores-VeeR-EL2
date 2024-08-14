// SPDX-License-Identifier: Apache-2.0
// Copyright 2019 Western Digital Corporation or its affiliates.
// Copyright (c) 2024 Antmicro <www.antmicro.com>
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
//

`ifndef VERILATOR
module tb_top
    import tb_top_pkg::*;
#(
    `include "el2_param.vh"
);
`else
module tb_top
    import tb_top_pkg::*;
#(
    `include "el2_param.vh"
) (
    input bit                   core_clk,
    input bit [31:0]            mem_signature_begin,
    input bit [31:0]            mem_signature_end,
    input bit [31:0]            mem_mailbox
);
`endif

`ifndef VERILATOR
    bit                         core_clk;
    bit          [31:0]         mem_signature_begin = 32'd0; // TODO:
    bit          [31:0]         mem_signature_end   = 32'd0;
    bit          [31:0]         mem_mailbox         = 32'hD0580000;
`endif
    logic                       rst_l;
    logic                       porst_l;
    logic [pt.PIC_TOTAL_INT:1]  ext_int;
    logic                       nmi_int;
    logic                       timer_int;
    logic                       soft_int;

    logic        [31:0]         reset_vector;
    logic        [31:0]         nmi_vector;
    logic        [31:1]         jtag_id;

    logic        [31:0]         ic_haddr        ;
    logic        [2:0]          ic_hburst       ;
    logic                       ic_hmastlock    ;
    logic        [3:0]          ic_hprot        ;
    logic        [2:0]          ic_hsize        ;
    logic        [1:0]          ic_htrans       ;
    logic                       ic_hwrite       ;
    logic        [63:0]         ic_hrdata       ;
    logic                       ic_hready       ;
    logic                       ic_hresp        ;

    logic        [31:0]         lsu_haddr       ;
    logic        [2:0]          lsu_hburst      ;
    logic                       lsu_hmastlock   ;
    logic        [3:0]          lsu_hprot       ;
    logic        [2:0]          lsu_hsize       ;
    logic        [1:0]          lsu_htrans      ;
    logic                       lsu_hwrite      ;
    logic        [63:0]         lsu_hrdata      ;
    logic        [63:0]         lsu_hwdata      ;
    logic                       lsu_hready      ;
    logic                       lsu_hresp       ;

    logic        [31:0]         mux_haddr       ;
    logic        [2:0]          mux_hburst      ;
    logic                       mux_hmastlock   ;
    logic        [3:0]          mux_hprot       ;
    logic        [2:0]          mux_hsize       ;
    logic        [1:0]          mux_htrans      ;
    logic                       mux_hwrite      ;
    logic                       mux_hsel        ;
    logic        [63:0]         mux_hrdata      ;
    logic        [63:0]         mux_hwdata      ;
    logic                       mux_hready      ;
    logic                       mux_hresp       ;
    logic                        mux_hreadyout  ;

    logic        [31:0]         sb_haddr        ;
    logic        [2:0]          sb_hburst       ;
    logic                       sb_hmastlock    ;
    logic        [3:0]          sb_hprot        ;
    logic        [2:0]          sb_hsize        ;
    logic        [1:0]          sb_htrans       ;
    logic                       sb_hwrite       ;

    logic        [63:0]         sb_hrdata       ;
    logic        [63:0]         sb_hwdata       ;
    logic                       sb_hready       ;
    logic                       sb_hresp        ;

    logic        [31:0]         trace_rv_i_insn_ip;
    logic        [31:0]         trace_rv_i_address_ip;
    logic                       trace_rv_i_valid_ip;
    logic                       trace_rv_i_exception_ip;
    logic        [4:0]          trace_rv_i_ecause_ip;
    logic                       trace_rv_i_interrupt_ip;
    logic        [31:0]         trace_rv_i_tval_ip;

    logic                       o_debug_mode_status;


    logic                       jtag_tdo;
    logic                       jtag_tck;
    logic                       jtag_tms;
    logic                       jtag_tdi;
    logic                       jtag_trst_n;

    logic                       o_cpu_halt_ack;
    logic                       o_cpu_halt_status;
    logic                       o_cpu_run_ack;

    logic                       mailbox_write;
    logic        [63:0]         mailbox_data;

    logic        [63:0]         dma_hrdata       ;
    logic        [63:0]         dma_hwdata       ;
    logic                       dma_hready       ;
    logic                       dma_hresp        ;

    logic                       mpc_debug_halt_req;
    logic                       mpc_debug_run_req;
    logic                       mpc_reset_run_req;
    logic                       mpc_debug_halt_ack;
    logic                       mpc_debug_run_ack;
    logic                       debug_brkpt_status;

    int                         cycleCnt;
    logic                       mailbox_data_val;

    wire                        dma_hready_out;
    int                         commit_count;

    logic                       wb_valid;
    logic [4:0]                 wb_dest;
    logic [31:0]                wb_data;

    logic                       wb_csr_valid;
    logic [11:0]                wb_csr_dest;
    logic [31:0]                wb_csr_data;

   `ifdef RV_OPENOCD_TEST
    // SB and LSU AHB master mux
    ahb_lite_2to1_mux #(
        .AHB_LITE_ADDR_WIDTH (32),
        .AHB_LITE_DATA_WIDTH (64),
        .AHB_NO_OPT(1) //Prevent address and data phase overlap between initiators
    ) u_sb_lsu_ahb_mux (
        .hclk                (core_clk),
        .hreset_n            (rst_l),
        .force_bus_idle      (),
        // Initiator 0
        .hsel_i_0            (1'b1      ),
        .haddr_i_0           (lsu_haddr ),
        .hwdata_i_0          (lsu_hwdata),
        .hwrite_i_0          (lsu_hwrite),
        .htrans_i_0          (lsu_htrans),
        .hsize_i_0           (lsu_hsize ),
        .hready_i_0          (lsu_hready),
        .hresp_o_0           (lsu_hresp ),
        .hready_o_0          (lsu_hready),
        .hrdata_o_0          (lsu_hrdata),

        // Initiator 1
        .hsel_i_1            (1'b1      ),
        .haddr_i_1           (sb_haddr  ),
        .hwdata_i_1          (sb_hwdata ),
        .hwrite_i_1          (sb_hwrite ),
        .htrans_i_1          (sb_htrans ),
        .hsize_i_1           (sb_hsize  ),
        .hready_i_1          (sb_hready ),
        .hresp_o_1           (sb_hresp  ),
        .hready_o_1          (sb_hready ),
        .hrdata_o_1          (sb_hrdata ),

        // Responder
        .hsel_o              (mux_hsel),
        .haddr_o             (mux_haddr ),
        .hwdata_o            (mux_hwdata),
        .hwrite_o            (mux_hwrite),
        .htrans_o            (mux_htrans),
        .hsize_o             (mux_hsize ),
        .hready_o            (mux_hready),
        .hresp_i             (mux_hresp ),
        .hreadyout_i         (mux_hreadyout),
        .hrdata_i            (mux_hrdata)
    );
   `else
   assign mux_hsel = 1'b1;
   assign mux_haddr = lsu_haddr;
   assign mux_hwdata = lsu_hwdata;
   assign mux_hwrite = lsu_hwrite;
   assign mux_htrans = lsu_htrans;
   assign mux_hsize = lsu_hsize;
   assign mux_hready = lsu_hready;

   assign lsu_hresp = mux_hresp;
   assign lsu_hrdata = mux_hrdata;
   assign lsu_hready = mux_hreadyout;
   `endif

`ifdef RV_BUILD_AXI4
   //-------------------------- LSU AXI signals--------------------------
   // AXI Write Channels
   parameter int                RV_MUX_BUS_TAG = (`RV_LSU_BUS_TAG > `RV_SB_BUS_TAG ? `RV_LSU_BUS_TAG : `RV_SB_BUS_TAG) + 1;
    wire                        lsu_axi_awvalid;
    wire                        lsu_axi_awready;
    wire [`RV_LSU_BUS_TAG-1:0]  lsu_axi_awid;
    wire [31:0]                 lsu_axi_awaddr;
    wire [3:0]                  lsu_axi_awregion;
    wire [7:0]                  lsu_axi_awlen;
    wire [2:0]                  lsu_axi_awsize;
    wire [1:0]                  lsu_axi_awburst;
    wire                        lsu_axi_awlock;
    wire [3:0]                  lsu_axi_awcache;
    wire [2:0]                  lsu_axi_awprot;
    wire [3:0]                  lsu_axi_awqos;

    wire                        lsu_axi_wvalid;
    wire                        lsu_axi_wready;
    wire [63:0]                 lsu_axi_wdata;
    wire [7:0]                  lsu_axi_wstrb;
    wire                        lsu_axi_wlast;

    wire                        lsu_axi_bvalid;
    wire                        lsu_axi_bready;
    wire [1:0]                  lsu_axi_bresp;
    wire [`RV_LSU_BUS_TAG-1:0]  lsu_axi_bid;

    // AXI Read Channels
    wire                        lsu_axi_arvalid;
    wire                        lsu_axi_arready;
    wire [`RV_LSU_BUS_TAG-1:0]  lsu_axi_arid;
    wire [31:0]                 lsu_axi_araddr;
    wire [3:0]                  lsu_axi_arregion;
    wire [7:0]                  lsu_axi_arlen;
    wire [2:0]                  lsu_axi_arsize;
    wire [1:0]                  lsu_axi_arburst;
    wire                        lsu_axi_arlock;
    wire [3:0]                  lsu_axi_arcache;
    wire [2:0]                  lsu_axi_arprot;
    wire [3:0]                  lsu_axi_arqos;

    wire                        lsu_axi_rvalid;
    wire                        lsu_axi_rready;
    wire [`RV_LSU_BUS_TAG-1:0]  lsu_axi_rid;
    wire [63:0]                 lsu_axi_rdata;
    wire [1:0]                  lsu_axi_rresp;
    wire                        lsu_axi_rlast;
    wire                        lsu_axi_awuser;
    wire                        lsu_axi_wuser;
    wire                        lsu_axi_buser;
    wire                        lsu_axi_aruser;
    wire                        lsu_axi_ruser;

    //-------------------------- IFU AXI signals--------------------------
    // AXI Write Channels
    wire                        ifu_axi_awvalid;
    wire                        ifu_axi_awready;
    wire [`RV_IFU_BUS_TAG-1:0]  ifu_axi_awid;
    wire [31:0]                 ifu_axi_awaddr;
    wire [3:0]                  ifu_axi_awregion;
    wire [7:0]                  ifu_axi_awlen;
    wire [2:0]                  ifu_axi_awsize;
    wire [1:0]                  ifu_axi_awburst;
    wire                        ifu_axi_awlock;
    wire [3:0]                  ifu_axi_awcache;
    wire [2:0]                  ifu_axi_awprot;
    wire [3:0]                  ifu_axi_awqos;

    wire                        ifu_axi_wvalid;
    wire                        ifu_axi_wready;
    wire [63:0]                 ifu_axi_wdata;
    wire [7:0]                  ifu_axi_wstrb;
    wire                        ifu_axi_wlast;

    wire                        ifu_axi_bvalid;
    wire                        ifu_axi_bready;
    wire [1:0]                  ifu_axi_bresp;
    wire [`RV_IFU_BUS_TAG-1:0]  ifu_axi_bid;

    // AXI Read Channels
    wire                        ifu_axi_arvalid;
    wire                        ifu_axi_arready;
    wire [`RV_IFU_BUS_TAG-1:0]  ifu_axi_arid;
    wire [31:0]                 ifu_axi_araddr;
    wire [3:0]                  ifu_axi_arregion;
    wire [7:0]                  ifu_axi_arlen;
    wire [2:0]                  ifu_axi_arsize;
    wire [1:0]                  ifu_axi_arburst;
    wire                        ifu_axi_arlock;
    wire [3:0]                  ifu_axi_arcache;
    wire [2:0]                  ifu_axi_arprot;
    wire [3:0]                  ifu_axi_arqos;

    wire                        ifu_axi_rvalid;
    wire                        ifu_axi_rready;
    wire [`RV_IFU_BUS_TAG-1:0]  ifu_axi_rid;
    wire [63:0]                 ifu_axi_rdata;
    wire [1:0]                  ifu_axi_rresp;
    wire                        ifu_axi_rlast;

    //-------------------------- SB AXI signals--------------------------
    // AXI Write Channels
    wire                        sb_axi_awvalid;
    wire                        sb_axi_awready;
    wire [`RV_SB_BUS_TAG-1:0]   sb_axi_awid;
    wire [31:0]                 sb_axi_awaddr;
    wire [3:0]                  sb_axi_awregion;
    wire [7:0]                  sb_axi_awlen;
    wire [2:0]                  sb_axi_awsize;
    wire [1:0]                  sb_axi_awburst;
    wire                        sb_axi_awlock;
    wire [3:0]                  sb_axi_awcache;
    wire [2:0]                  sb_axi_awprot;
    wire [3:0]                  sb_axi_awqos;

    wire                        sb_axi_wvalid;
    wire                        sb_axi_wready;
    wire [63:0]                 sb_axi_wdata;
    wire [7:0]                  sb_axi_wstrb;
    wire                        sb_axi_wlast;

    wire                        sb_axi_bvalid;
    wire                        sb_axi_bready;
    wire [1:0]                  sb_axi_bresp;
    wire [`RV_SB_BUS_TAG-1:0]   sb_axi_bid;

    // AXI Read Channels
    wire                        sb_axi_arvalid;
    wire                        sb_axi_arready;
    wire [`RV_SB_BUS_TAG-1:0]   sb_axi_arid;
    wire [31:0]                 sb_axi_araddr;
    wire [3:0]                  sb_axi_arregion;
    wire [7:0]                  sb_axi_arlen;
    wire [2:0]                  sb_axi_arsize;
    wire [1:0]                  sb_axi_arburst;
    wire                        sb_axi_arlock;
    wire [3:0]                  sb_axi_arcache;
    wire [2:0]                  sb_axi_arprot;
    wire [3:0]                  sb_axi_arqos;

    wire                        sb_axi_rvalid;
    wire                        sb_axi_rready;
    wire [`RV_SB_BUS_TAG-1:0]   sb_axi_rid;
    wire [63:0]                 sb_axi_rdata;
    wire [1:0]                  sb_axi_rresp;
    wire                        sb_axi_rlast;
    wire                        sb_axi_awuser;
    wire                        sb_axi_wuser;
    wire                        sb_axi_buser;
    wire                        sb_axi_aruser;
    wire                        sb_axi_ruser;

   //-------------------------- DMA AXI signals--------------------------
   // AXI Write Channels
    wire                        dma_axi_awvalid;
    wire                        dma_axi_awready;
    wire [`RV_DMA_BUS_TAG-1:0]  dma_axi_awid;
    wire [31:0]                 dma_axi_awaddr;
    wire [2:0]                  dma_axi_awsize;
    wire [2:0]                  dma_axi_awprot;
    wire [7:0]                  dma_axi_awlen;
    wire [1:0]                  dma_axi_awburst;


    wire                        dma_axi_wvalid;
    wire                        dma_axi_wready;
    wire [63:0]                 dma_axi_wdata;
    wire [7:0]                  dma_axi_wstrb;
    wire                        dma_axi_wlast;

    wire                        dma_axi_bvalid;
    wire                        dma_axi_bready;
    wire [1:0]                  dma_axi_bresp;
    wire [`RV_DMA_BUS_TAG-1:0]  dma_axi_bid;

    // AXI Read Channels
    wire                        dma_axi_arvalid;
    wire                        dma_axi_arready;
    wire [`RV_DMA_BUS_TAG-1:0]  dma_axi_arid;
    wire [31:0]                 dma_axi_araddr;
    wire [2:0]                  dma_axi_arsize;
    wire [2:0]                  dma_axi_arprot;
    wire [7:0]                  dma_axi_arlen;
    wire [1:0]                  dma_axi_arburst;

    wire                        dma_axi_rvalid;
    wire                        dma_axi_rready;
    wire [`RV_DMA_BUS_TAG-1:0]  dma_axi_rid;
    wire [63:0]                 dma_axi_rdata;
    wire [1:0]                  dma_axi_rresp;
    wire                        dma_axi_rlast;

    wire                        lmem_axi_arvalid;
    wire                        lmem_axi_arready;

    wire                        lmem_axi_rvalid;
    wire [RV_MUX_BUS_TAG-1:0]   lmem_axi_rid;
    wire [1:0]                  lmem_axi_rresp;
    wire [63:0]                 lmem_axi_rdata;
    wire                        lmem_axi_rlast;
    wire                        lmem_axi_rready;

    wire                        lmem_axi_awvalid;
    wire                        lmem_axi_awready;

    wire                        lmem_axi_wvalid;
    wire                        lmem_axi_wready;

    wire [1:0]                  lmem_axi_bresp;
    wire                        lmem_axi_bvalid;
    wire [RV_MUX_BUS_TAG-1:0]   lmem_axi_bid;
    wire                        lmem_axi_bready;

    wire                        mux_axi_awvalid;
    wire                        mux_axi_awready;
    wire [RV_MUX_BUS_TAG-1:0]   mux_axi_awid;
    wire [31:0]                 mux_axi_awaddr;
    wire [3:0]                  mux_axi_awregion;
    wire [7:0]                  mux_axi_awlen;
    wire [2:0]                  mux_axi_awsize;
    wire [1:0]                  mux_axi_awburst;
    wire                        mux_axi_awlock;
    wire [3:0]                  mux_axi_awcache;
    wire [2:0]                  mux_axi_awprot;
    wire [3:0]                  mux_axi_awqos;

    wire                        mux_axi_wvalid;
    wire                        mux_axi_wready;
    wire [63:0]                 mux_axi_wdata;
    wire [7:0]                  mux_axi_wstrb;
    wire                        mux_axi_wlast;

    wire                        mux_axi_bvalid;
    wire                        mux_axi_bready;
    wire [1:0]                  mux_axi_bresp;
    wire [RV_MUX_BUS_TAG-1:0]   mux_axi_bid;

    // AXI Read Channels
    wire                        mux_axi_arvalid;
    wire                        mux_axi_arready;
    wire [RV_MUX_BUS_TAG-1:0]   mux_axi_arid;
    wire [31:0]                 mux_axi_araddr;
    wire [3:0]                  mux_axi_arregion;
    wire [7:0]                  mux_axi_arlen;
    wire [2:0]                  mux_axi_arsize;
    wire [1:0]                  mux_axi_arburst;
    wire                        mux_axi_arlock;
    wire [3:0]                  mux_axi_arcache;
    wire [2:0]                  mux_axi_arprot;
    wire [3:0]                  mux_axi_arqos;

    wire                        mux_axi_rvalid;
    wire                        mux_axi_rready;
    wire [RV_MUX_BUS_TAG-1:0]   mux_axi_rid;
    wire [63:0]                 mux_axi_rdata;
    wire [1:0]                  mux_axi_rresp;
    wire                        mux_axi_rlast;
    wire                        mux_axi_awuser;
    wire                        mux_axi_wuser;
    wire                        mux_axi_buser;
    wire                        mux_axi_aruser;
    wire                        mux_axi_ruser;

`ifdef RV_OPENOCD_TEST
   axi_crossbar_wrap_2x1 #(
        .ADDR_WIDTH (32),
        .DATA_WIDTH (64),
        .S_ID_WIDTH(RV_MUX_BUS_TAG - 1),
        .M00_ADDR_WIDTH(32)
    ) u_axi_crossbar (
                      .clk(core_clk),
                      .rst(!rst_l),

                      // LSU
                      .s00_axi_arvalid(lsu_axi_arvalid),
                      .s00_axi_arready(lsu_axi_arready),
                      .s00_axi_araddr(lsu_axi_araddr),
                      .s00_axi_arid(lsu_axi_arid),
                      .s00_axi_arlen(lsu_axi_arlen),
                      .s00_axi_arburst(lsu_axi_arburst),
                      .s00_axi_arsize(lsu_axi_arsize),

                      .s00_axi_rvalid(lsu_axi_rvalid),
                      .s00_axi_rready(lsu_axi_rready),
                      .s00_axi_rdata(lsu_axi_rdata),
                      .s00_axi_rresp(lsu_axi_rresp),
                      .s00_axi_rid(lsu_axi_rid),
                      .s00_axi_rlast(lsu_axi_rlast),

                      .s00_axi_awvalid(lsu_axi_awvalid),
                      .s00_axi_awready(lsu_axi_awready),
                      .s00_axi_awaddr(lsu_axi_awaddr),
                      .s00_axi_awid(lsu_axi_awid),
                      .s00_axi_awlen(lsu_axi_awlen),
                      .s00_axi_awburst(lsu_axi_awburst),
                      .s00_axi_awlock(lsu_axi_awlock),
                      .s00_axi_awcache(lsu_axi_awcache),
                      .s00_axi_awprot(lsu_axi_awprot),
                      .s00_axi_awqos(lsu_axi_awqos),
                      .s00_axi_awuser(lsu_axi_awuser),
                      .s00_axi_wlast(lsu_axi_wlast),
                      .s00_axi_wuser(lsu_axi_wuser),
                      .s00_axi_buser(lsu_axi_buser),
                      .s00_axi_arlock(lsu_axi_arlock),
                      .s00_axi_arcache(lsu_axi_arcache),
                      .s00_axi_arprot(lsu_axi_arprot),
                      .s00_axi_arqos(lsu_axi_arqos),
                      .s00_axi_aruser(lsu_axi_aruser),
                      .s00_axi_ruser(lsu_axi_ruser),
                      .s00_axi_awsize(lsu_axi_awsize),

                      .s00_axi_wdata(lsu_axi_wdata),
                      .s00_axi_wstrb(lsu_axi_wstrb),
                      .s00_axi_wvalid(lsu_axi_wvalid),
                      .s00_axi_wready(lsu_axi_wready),

                      .s00_axi_bvalid(lsu_axi_bvalid),
                      .s00_axi_bready(lsu_axi_bready),
                      .s00_axi_bresp(lsu_axi_bresp),
                      .s00_axi_bid(lsu_axi_bid),

                      // SB
                      .s01_axi_arvalid(sb_axi_arvalid),
                      .s01_axi_arready(sb_axi_arready),
                      .s01_axi_araddr(sb_axi_araddr),
                      .s01_axi_arid(sb_axi_arid),
                      .s01_axi_arlen(sb_axi_arlen),
                      .s01_axi_arburst(sb_axi_arburst),
                      .s01_axi_arsize(sb_axi_arsize),

                      .s01_axi_rvalid(sb_axi_rvalid),
                      .s01_axi_rready(sb_axi_rready),
                      .s01_axi_rdata(sb_axi_rdata),
                      .s01_axi_rresp(sb_axi_rresp),
                      .s01_axi_rid(sb_axi_rid),
                      .s01_axi_rlast(sb_axi_rlast),

                      .s01_axi_awvalid(sb_axi_awvalid),
                      .s01_axi_awready(sb_axi_awready),
                      .s01_axi_awaddr(sb_axi_awaddr),
                      .s01_axi_awid(sb_axi_awid),
                      .s01_axi_awlen(sb_axi_awlen),
                      .s01_axi_awburst(sb_axi_awburst),
                      .s01_axi_awlock(sb_axi_awlock),
                      .s01_axi_awcache(sb_axi_awcache),
                      .s01_axi_awprot(sb_axi_awprot),
                      .s01_axi_awqos(sb_axi_awqos),
                      .s01_axi_awuser(sb_axi_awuser),
                      .s01_axi_wlast(sb_axi_wlast),
                      .s01_axi_wuser(sb_axi_wuser),
                      .s01_axi_buser(sb_axi_buser),
                      .s01_axi_arlock(sb_axi_arlock),
                      .s01_axi_arcache(sb_axi_arcache),
                      .s01_axi_arprot(sb_axi_arprot),
                      .s01_axi_arqos(sb_axi_arqos),
                      .s01_axi_aruser(sb_axi_aruser),
                      .s01_axi_ruser(sb_axi_ruser),
                      .s01_axi_awsize(sb_axi_awsize),

                      .s01_axi_wdata(sb_axi_wdata),
                      .s01_axi_wstrb(sb_axi_wstrb),
                      .s01_axi_wvalid(sb_axi_wvalid),
                      .s01_axi_wready(sb_axi_wready),

                      .s01_axi_bvalid(sb_axi_bvalid),
                      .s01_axi_bready(sb_axi_bready),
                      .s01_axi_bresp(sb_axi_bresp),
                      .s01_axi_bid(sb_axi_bid),

                      // Output
                      .m00_axi_arvalid(mux_axi_arvalid),
                      .m00_axi_arready(mux_axi_arready),
                      .m00_axi_araddr(mux_axi_araddr),
                      .m00_axi_arid(mux_axi_arid),
                      .m00_axi_arlen(mux_axi_arlen),
                      .m00_axi_arburst(mux_axi_arburst),
                      .m00_axi_arsize(mux_axi_arsize),

                      .m00_axi_rvalid(mux_axi_rvalid),
                      .m00_axi_rready(mux_axi_rready),
                      .m00_axi_rdata(mux_axi_rdata),
                      .m00_axi_rresp(mux_axi_rresp),
                      .m00_axi_rid(mux_axi_rid),
                      .m00_axi_rlast(mux_axi_rlast),

                      .m00_axi_awvalid(mux_axi_awvalid),
                      .m00_axi_awready(mux_axi_awready),
                      .m00_axi_awaddr(mux_axi_awaddr),
                      .m00_axi_awid(mux_axi_awid),
                      .m00_axi_awlen(mux_axi_awlen),
                      .m00_axi_awburst(mux_axi_awburst),
                      .m00_axi_awlock(mux_axi_awlock),
                      .m00_axi_awcache(mux_axi_awcache),
                      .m00_axi_awprot(mux_axi_awprot),
                      .m00_axi_awqos(mux_axi_awqos),
                      .m00_axi_awuser(mux_axi_awuser),
                      .m00_axi_wlast(mux_axi_wlast),
                      .m00_axi_wuser(mux_axi_wuser),
                      .m00_axi_buser(mux_axi_buser),
                      .m00_axi_arlock(mux_axi_arlock),
                      .m00_axi_arcache(mux_axi_arcache),
                      .m00_axi_arprot(mux_axi_arprot),
                      .m00_axi_arqos(mux_axi_arqos),
                      .m00_axi_aruser(mux_axi_aruser),
                      .m00_axi_ruser(mux_axi_ruser),
                      .m00_axi_awsize(mux_axi_awsize),

                      .m00_axi_wdata(mux_axi_wdata),
                      .m00_axi_wstrb(mux_axi_wstrb),
                      .m00_axi_wvalid(mux_axi_wvalid),
                      .m00_axi_wready(mux_axi_wready),

                      .m00_axi_bvalid(mux_axi_bvalid),
                      .m00_axi_bready(mux_axi_bready),
                      .m00_axi_bresp(mux_axi_bresp),
                      .m00_axi_bid(mux_axi_bid),
                      .m00_axi_awregion(mux_axi_awregion),
                      .m00_axi_arregion(mux_axi_arregion)
    );
`else
   assign mux_axi_arvalid = lsu_axi_arvalid;
   assign lsu_axi_arready = mux_axi_arready;
   assign mux_axi_araddr = lsu_axi_araddr;
   assign mux_axi_arid = lsu_axi_arid;
   assign mux_axi_arlen = lsu_axi_arlen;
   assign mux_axi_arburst = lsu_axi_arburst;
   assign mux_axi_arsize = lsu_axi_arsize;
   assign lsu_axi_rvalid = mux_axi_rvalid;
   assign mux_axi_rready = lsu_axi_rready;
   assign lsu_axi_rdata = mux_axi_rdata;
   assign lsu_axi_rresp = mux_axi_rresp;
   assign lsu_axi_rid = mux_axi_rid;
   assign lsu_axi_rlast = mux_axi_rlast;
   assign mux_axi_awvalid = lsu_axi_awvalid;
   assign lsu_axi_awready = mux_axi_awready;
   assign mux_axi_awaddr = lsu_axi_awaddr;
   assign mux_axi_awid = lsu_axi_awid;
   assign mux_axi_awlen = lsu_axi_awlen;
   assign mux_axi_awburst = lsu_axi_awburst;
   assign mux_axi_awlock = lsu_axi_awlock;
   assign mux_axi_awcache = lsu_axi_awcache;
   assign mux_axi_awprot = lsu_axi_awprot;
   assign mux_axi_awqos = lsu_axi_awqos;
   assign mux_axi_awuser = lsu_axi_awuser;
   assign mux_axi_wlast = lsu_axi_wlast;
   assign mux_axi_wuser = lsu_axi_wuser;
   assign lsu_axi_buser = mux_axi_buser;
   assign mux_axi_arlock = lsu_axi_arlock;
   assign mux_axi_arcache = lsu_axi_arcache;
   assign mux_axi_arprot = lsu_axi_arprot;
   assign mux_axi_arqos = lsu_axi_arqos;
   assign mux_axi_aruser = lsu_axi_aruser;
   assign lsu_axi_ruser = mux_axi_ruser;
   assign mux_axi_awsize = lsu_axi_awsize;
   assign mux_axi_wdata = lsu_axi_wdata;
   assign mux_axi_wstrb = lsu_axi_wstrb;
   assign mux_axi_wvalid = lsu_axi_wvalid;
   assign lsu_axi_wready = mux_axi_wready;
   assign lsu_axi_bvalid = mux_axi_bvalid;
   assign mux_axi_bready = lsu_axi_bready;
   assign lsu_axi_bresp = mux_axi_bresp;
   assign lsu_axi_bid = mux_axi_bid;
   assign mux_axi_awregion = lsu_axi_awregion;
   assign mux_axi_arregion = lsu_axi_arregion;
`endif

`endif
    string                      abi_reg[32]; // ABI register names
    el2_mem_if el2_mem_export ();

    logic [pt.ICCM_NUM_BANKS-1:0][                   38:0] iccm_bank_wr_fdata;
    logic [pt.ICCM_NUM_BANKS-1:0][                   38:0] iccm_bank_fdout;
    logic [pt.DCCM_NUM_BANKS-1:0][pt.DCCM_FDATA_WIDTH-1:0] dccm_wr_fdata_bank;
    logic [pt.DCCM_NUM_BANKS-1:0][pt.DCCM_FDATA_WIDTH-1:0] dccm_bank_fdout;

    tb_top_pkg::veer_sram_error_injection_mode_t error_injection_mode;

`define DEC rvtop_wrapper.rvtop.veer.dec

`ifdef RV_BUILD_AXI4
    assign mailbox_write    = lmem.awvalid && lmem.awaddr == mem_mailbox && rst_l;
    assign mailbox_data     = lmem.wdata;
`endif
`ifdef RV_BUILD_AHB_LITE
    assign mailbox_write    = lmem.write   && lmem.laddr  == mem_mailbox && rst_l;
    assign mailbox_data     = lmem.HWDATA;
`endif

    assign mailbox_data_val = mailbox_data[7:0] > 8'h5 && mailbox_data[7:0] < 8'h7f;

    parameter MAX_CYCLES = 2_000_000;

    integer fd, tp, el;

    always @(negedge core_clk) begin
        cycleCnt <= cycleCnt+1;
        // Test timeout monitor
        if(cycleCnt == MAX_CYCLES) begin
            $display ("Hit max cycle count (%0d) .. stopping",cycleCnt);
            $finish;
        end
        // console Monitor
        if( mailbox_data_val & mailbox_write) begin
            $fwrite(fd,"%c", mailbox_data[7:0]);
            $write("%c", mailbox_data[7:0]);
        end
        // Interrupt signals control
        // data[7:0] == 0x80 - clear ext irq line index given by data[15:8]
        // data[7:0] == 0x81 - set ext irq line index given by data[15:8]
        // data[7:0] == 0x82 - clean NMI, timer and soft irq lines to bits data[8:10]
        // data[7:0] == 0x83 - set NMI, timer and soft irq lines to bits data[8:10]
        // data[7:0] == 0x90 - clear all interrupt request signals
        if(mailbox_write && (mailbox_data[7:0] >= 8'h80 && mailbox_data[7:0] < 8'h84)) begin
            if (mailbox_data[7:0] == 8'h80) begin
                if (mailbox_data[15:8] > 0 && mailbox_data[15:8] < pt.PIC_TOTAL_INT)
                    ext_int[mailbox_data[15:8]] <= 1'b0;
            end
            if (mailbox_data[7:0] == 8'h81) begin
                if (mailbox_data[15:8] > 0 && mailbox_data[15:8] < pt.PIC_TOTAL_INT)
                    ext_int[mailbox_data[15:8]] <= 1'b1;
            end
            if (mailbox_data[7:0] == 8'h82) begin
                nmi_int   <= nmi_int   & ~mailbox_data[8];
                timer_int <= timer_int & ~mailbox_data[9];
                soft_int  <= soft_int  & ~mailbox_data[10];
            end
            if (mailbox_data[7:0] == 8'h83) begin
                nmi_int   <= nmi_int   |  mailbox_data[8];
                timer_int <= timer_int |  mailbox_data[9];
                soft_int  <= soft_int  |  mailbox_data[10];
            end
        end
        if(mailbox_write && (mailbox_data[7:0] == 8'h90)) begin
            ext_int   <= {pt.PIC_TOTAL_INT-1{1'b0}};
            nmi_int   <= 1'b0;
            timer_int <= 1'b0;
            soft_int  <= 1'b0;
        end
        // ECC error injection
        if(mailbox_write && (mailbox_data[7:0] == 8'he0)) begin
            $display("Injecting single bit ICCM error");
            error_injection_mode.iccm_single_bit_error <= 1'b1;
        end
        else if(mailbox_write && (mailbox_data[7:0] == 8'he1)) begin
            $display("Injecting double bit ICCM error");
            error_injection_mode.iccm_double_bit_error <= 1'b1;
        end
        else if(mailbox_write && (mailbox_data[7:0] == 8'he2)) begin
            $display("Injecting single bit DCCM error");
            error_injection_mode.dccm_single_bit_error <= 1'b1;
        end
        else if(mailbox_write && (mailbox_data[7:0] == 8'he3)) begin
            $display("Injecting double bit DCCM error");
            error_injection_mode.dccm_double_bit_error <= 1'b1;
        end
        else if(mailbox_write && (mailbox_data[7:0] == 8'he4)) begin
            $display("Disable ECC error injection");
            error_injection_mode <= '0;
        end
        // Memory signature dump
        if(mailbox_write && (mailbox_data[7:0] == 8'hFF || mailbox_data[7:0] == 8'h01)) begin
            if (mem_signature_begin < mem_signature_end) begin
                dump_signature();
            end
        end
        // End Of test monitor
        if(mailbox_write && mailbox_data[7:0] == 8'hff) begin
            $display("TEST_PASSED");
            $display("\nFinished : minstret = %0d, mcycle = %0d", `DEC.tlu.minstretl[31:0],`DEC.tlu.mcyclel[31:0]);
            $display("See \"exec.log\" for execution trace with register updates..\n");
            // OpenOCD test breaks if simulation closes the TCP connection first.
            // This delay allows OpenOCD to close the connection before the #finish.
            #15000;
            $finish;
        end
        else if(mailbox_write && mailbox_data[7:0] == 8'h1) begin
            $display("TEST_FAILED");
            $finish;
        end
    end

    // trace monitor
    always @(posedge core_clk) begin
        wb_valid      <= `DEC.dec_i0_wen_r;
        wb_dest       <= `DEC.dec_i0_waddr_r;
        wb_data       <= `DEC.dec_i0_wdata_r;
        wb_csr_valid  <= `DEC.dec_csr_wen_r;
        wb_csr_dest   <= `DEC.dec_csr_wraddr_r;
        wb_csr_data   <= `DEC.dec_csr_wrdata_r;
        if (trace_rv_i_valid_ip) begin
           $fwrite(tp,"%b,%h,%h,%0h,%0h,3,%b,%h,%h,%b\n", trace_rv_i_valid_ip, 0, trace_rv_i_address_ip,
                  0, trace_rv_i_insn_ip,trace_rv_i_exception_ip,trace_rv_i_ecause_ip,
                  trace_rv_i_tval_ip,trace_rv_i_interrupt_ip);
           // Basic trace - no exception register updates
           // #1 0 ee000000 b0201073 c 0b02       00000000
           commit_count++;
           $fwrite (el, "%10d : %8s 0 %h %h%13s %14s ; %s\n", cycleCnt, $sformatf("#%0d",commit_count),
                        trace_rv_i_address_ip, trace_rv_i_insn_ip,
                        (wb_dest !=0 && wb_valid)?  $sformatf("%s=%h", abi_reg[wb_dest], wb_data) : "            ",
                        (wb_csr_valid)? $sformatf("c%h=%h", wb_csr_dest, wb_csr_data) : "             ",
                        dasm(trace_rv_i_insn_ip, trace_rv_i_address_ip, wb_dest & {5{wb_valid}}, wb_data)
                   );
        end
        if(`DEC.dec_nonblock_load_wen) begin
            $fwrite (el, "%10d : %32s=%h                ; nbL\n", cycleCnt, abi_reg[`DEC.dec_nonblock_load_waddr], `DEC.lsu_nonblock_load_data);
            tb_top.gpr[0][`DEC.dec_nonblock_load_waddr] = `DEC.lsu_nonblock_load_data;
        end
        if(`DEC.exu_div_wren) begin
            $fwrite (el, "%10d : %32s=%h                ; nbD\n", cycleCnt, abi_reg[`DEC.div_waddr_wb], `DEC.exu_div_result);
            tb_top.gpr[0][`DEC.div_waddr_wb] = `DEC.exu_div_result;
        end
    end


    initial begin
        abi_reg[0] = "zero";
        abi_reg[1] = "ra";
        abi_reg[2] = "sp";
        abi_reg[3] = "gp";
        abi_reg[4] = "tp";
        abi_reg[5] = "t0";
        abi_reg[6] = "t1";
        abi_reg[7] = "t2";
        abi_reg[8] = "s0";
        abi_reg[9] = "s1";
        abi_reg[10] = "a0";
        abi_reg[11] = "a1";
        abi_reg[12] = "a2";
        abi_reg[13] = "a3";
        abi_reg[14] = "a4";
        abi_reg[15] = "a5";
        abi_reg[16] = "a6";
        abi_reg[17] = "a7";
        abi_reg[18] = "s2";
        abi_reg[19] = "s3";
        abi_reg[20] = "s4";
        abi_reg[21] = "s5";
        abi_reg[22] = "s6";
        abi_reg[23] = "s7";
        abi_reg[24] = "s8";
        abi_reg[25] = "s9";
        abi_reg[26] = "s10";
        abi_reg[27] = "s11";
        abi_reg[28] = "t3";
        abi_reg[29] = "t4";
        abi_reg[30] = "t5";
        abi_reg[31] = "t6";

        ext_int     = {pt.PIC_TOTAL_INT-1{1'b0}};
        nmi_int     = 0;
        timer_int   = 0;
        soft_int    = 0;

    // tie offs
        jtag_id[31:28] = 4'b1;
        jtag_id[27:12] = '0;
        jtag_id[11:1]  = 11'h45;
        reset_vector = `RV_RESET_VEC;
        nmi_vector   = 32'hee000000;

        $readmemh("program.hex",  lmem.mem);
        $readmemh("program.hex",  imem.mem);
        tp = $fopen("trace_port.csv","w");
        el = $fopen("exec.log","w");
        $fwrite (el, "//   Cycle : #inst    0    pc    opcode    reg=value    csr=value     ; mnemonic\n");
        fd = $fopen("console.log","w");
        commit_count = 0;
        preload_dccm();
        preload_iccm();

`ifndef VERILATOR
        if($test$plusargs("dumpon")) $dumpvars;
        forever  core_clk = #5 ~core_clk;
`endif
    end


    assign rst_l = cycleCnt > 5;
    assign porst_l = cycleCnt > 2;

   //=========================================================================-
   // RTL instance
   //=========================================================================-
veer_wrapper rvtop_wrapper (
    .rst_l                  ( rst_l         ),
    .dbg_rst_l              ( porst_l       ),
    .clk                    ( core_clk      ),
    .rst_vec                ( reset_vector[31:1]),
    .nmi_int                ( nmi_int       ),
    .nmi_vec                ( nmi_vector[31:1]),
    .jtag_id                ( jtag_id[31:1]),

`ifdef RV_BUILD_AHB_LITE
    .haddr                  ( ic_haddr      ),
    .hburst                 ( ic_hburst     ),
    .hmastlock              ( ic_hmastlock  ),
    .hprot                  ( ic_hprot      ),
    .hsize                  ( ic_hsize      ),
    .htrans                 ( ic_htrans     ),
    .hwrite                 ( ic_hwrite     ),

    .hrdata                 ( ic_hrdata[63:0]),
    .hready                 ( ic_hready     ),
    .hresp                  ( ic_hresp      ),

    //---------------------------------------------------------------
    // Debug AHB Master
    //---------------------------------------------------------------
    .sb_haddr               ( sb_haddr      ),
    .sb_hburst              ( sb_hburst     ),
    .sb_hmastlock           ( sb_hmastlock  ),
    .sb_hprot               ( sb_hprot      ),
    .sb_hsize               ( sb_hsize      ),
    .sb_htrans              ( sb_htrans     ),
    .sb_hwrite              ( sb_hwrite     ),
    .sb_hwdata              ( sb_hwdata     ),

    .sb_hrdata              ( sb_hrdata     ),
    .sb_hready              ( sb_hready     ),
    .sb_hresp               ( sb_hresp      ),

    //---------------------------------------------------------------
    // LSU AHB Master
    //---------------------------------------------------------------
    .lsu_haddr              ( lsu_haddr       ),
    .lsu_hburst             ( lsu_hburst      ),
    .lsu_hmastlock          ( lsu_hmastlock   ),
    .lsu_hprot              ( lsu_hprot       ),
    .lsu_hsize              ( lsu_hsize       ),
    .lsu_htrans             ( lsu_htrans      ),
    .lsu_hwrite             ( lsu_hwrite      ),
    .lsu_hwdata             ( lsu_hwdata      ),

    .lsu_hrdata             ( lsu_hrdata[63:0]),
    .lsu_hready             ( lsu_hready      ),
    .lsu_hresp              ( lsu_hresp       ),

    //---------------------------------------------------------------
    // DMA Slave
    //---------------------------------------------------------------
    .dma_haddr              ( '0 ),
    .dma_hburst             ( '0 ),
    .dma_hmastlock          ( '0 ),
    .dma_hprot              ( '0 ),
    .dma_hsize              ( '0 ),
    .dma_htrans             ( '0 ),
    .dma_hwrite             ( '0 ),
    .dma_hwdata             ( '0 ),

    .dma_hrdata             ( dma_hrdata    ),
    .dma_hresp              ( dma_hresp     ),
    .dma_hsel               ( 1'b1            ),
    .dma_hreadyin           ( dma_hready_out  ),
    .dma_hreadyout          ( dma_hready_out  ),
`endif
`ifdef RV_BUILD_AXI4
    //-------------------------- LSU AXI signals--------------------------
    // AXI Write Channels
    .lsu_axi_awvalid        (lsu_axi_awvalid),
    .lsu_axi_awready        (lsu_axi_awready),
    .lsu_axi_awid           (lsu_axi_awid),
    .lsu_axi_awaddr         (lsu_axi_awaddr),
    .lsu_axi_awregion       (lsu_axi_awregion),
    .lsu_axi_awlen          (lsu_axi_awlen),
    .lsu_axi_awsize         (lsu_axi_awsize),
    .lsu_axi_awburst        (lsu_axi_awburst),
    .lsu_axi_awlock         (lsu_axi_awlock),
    .lsu_axi_awcache        (lsu_axi_awcache),
    .lsu_axi_awprot         (lsu_axi_awprot),
    .lsu_axi_awqos          (lsu_axi_awqos),

    .lsu_axi_wvalid         (lsu_axi_wvalid),
    .lsu_axi_wready         (lsu_axi_wready),
    .lsu_axi_wdata          (lsu_axi_wdata),
    .lsu_axi_wstrb          (lsu_axi_wstrb),
    .lsu_axi_wlast          (lsu_axi_wlast),

    .lsu_axi_bvalid         (lsu_axi_bvalid),
    .lsu_axi_bready         (lsu_axi_bready),
    .lsu_axi_bresp          (lsu_axi_bresp),
    .lsu_axi_bid            (lsu_axi_bid),


    .lsu_axi_arvalid        (lsu_axi_arvalid),
    .lsu_axi_arready        (lsu_axi_arready),
    .lsu_axi_arid           (lsu_axi_arid),
    .lsu_axi_araddr         (lsu_axi_araddr),
    .lsu_axi_arregion       (lsu_axi_arregion),
    .lsu_axi_arlen          (lsu_axi_arlen),
    .lsu_axi_arsize         (lsu_axi_arsize),
    .lsu_axi_arburst        (lsu_axi_arburst),
    .lsu_axi_arlock         (lsu_axi_arlock),
    .lsu_axi_arcache        (lsu_axi_arcache),
    .lsu_axi_arprot         (lsu_axi_arprot),
    .lsu_axi_arqos          (lsu_axi_arqos),

    .lsu_axi_rvalid         (lsu_axi_rvalid),
    .lsu_axi_rready         (lsu_axi_rready),
    .lsu_axi_rid            (lsu_axi_rid),
    .lsu_axi_rdata          (lsu_axi_rdata),
    .lsu_axi_rresp          (lsu_axi_rresp),
    .lsu_axi_rlast          (lsu_axi_rlast),

    //-------------------------- IFU AXI signals--------------------------
    // AXI Write Channels
    .ifu_axi_awvalid        (ifu_axi_awvalid),
    .ifu_axi_awready        (ifu_axi_awready),
    .ifu_axi_awid           (ifu_axi_awid),
    .ifu_axi_awaddr         (ifu_axi_awaddr),
    .ifu_axi_awregion       (ifu_axi_awregion),
    .ifu_axi_awlen          (ifu_axi_awlen),
    .ifu_axi_awsize         (ifu_axi_awsize),
    .ifu_axi_awburst        (ifu_axi_awburst),
    .ifu_axi_awlock         (ifu_axi_awlock),
    .ifu_axi_awcache        (ifu_axi_awcache),
    .ifu_axi_awprot         (ifu_axi_awprot),
    .ifu_axi_awqos          (ifu_axi_awqos),

    .ifu_axi_wvalid         (ifu_axi_wvalid),
    .ifu_axi_wready         (ifu_axi_wready),
    .ifu_axi_wdata          (ifu_axi_wdata),
    .ifu_axi_wstrb          (ifu_axi_wstrb),
    .ifu_axi_wlast          (ifu_axi_wlast),

    .ifu_axi_bvalid         (ifu_axi_bvalid),
    .ifu_axi_bready         (ifu_axi_bready),
    .ifu_axi_bresp          (ifu_axi_bresp),
    .ifu_axi_bid            (ifu_axi_bid),

    .ifu_axi_arvalid        (ifu_axi_arvalid),
    .ifu_axi_arready        (ifu_axi_arready),
    .ifu_axi_arid           (ifu_axi_arid),
    .ifu_axi_araddr         (ifu_axi_araddr),
    .ifu_axi_arregion       (ifu_axi_arregion),
    .ifu_axi_arlen          (ifu_axi_arlen),
    .ifu_axi_arsize         (ifu_axi_arsize),
    .ifu_axi_arburst        (ifu_axi_arburst),
    .ifu_axi_arlock         (ifu_axi_arlock),
    .ifu_axi_arcache        (ifu_axi_arcache),
    .ifu_axi_arprot         (ifu_axi_arprot),
    .ifu_axi_arqos          (ifu_axi_arqos),

    .ifu_axi_rvalid         (ifu_axi_rvalid),
    .ifu_axi_rready         (ifu_axi_rready),
    .ifu_axi_rid            (ifu_axi_rid),
    .ifu_axi_rdata          (ifu_axi_rdata),
    .ifu_axi_rresp          (ifu_axi_rresp),
    .ifu_axi_rlast          (ifu_axi_rlast),

    //-------------------------- SB AXI signals--------------------------
    // AXI Write Channels
    .sb_axi_awvalid         (sb_axi_awvalid),
    .sb_axi_awready         (sb_axi_awready),
    .sb_axi_awid            (sb_axi_awid),
    .sb_axi_awaddr          (sb_axi_awaddr),
    .sb_axi_awregion        (sb_axi_awregion),
    .sb_axi_awlen           (sb_axi_awlen),
    .sb_axi_awsize          (sb_axi_awsize),
    .sb_axi_awburst         (sb_axi_awburst),
    .sb_axi_awlock          (sb_axi_awlock),
    .sb_axi_awcache         (sb_axi_awcache),
    .sb_axi_awprot          (sb_axi_awprot),
    .sb_axi_awqos           (sb_axi_awqos),

    .sb_axi_wvalid          (sb_axi_wvalid),
    .sb_axi_wready          (sb_axi_wready),
    .sb_axi_wdata           (sb_axi_wdata),
    .sb_axi_wstrb           (sb_axi_wstrb),
    .sb_axi_wlast           (sb_axi_wlast),

    .sb_axi_bvalid          (sb_axi_bvalid),
    .sb_axi_bready          (sb_axi_bready),
    .sb_axi_bresp           (sb_axi_bresp),
    .sb_axi_bid             (sb_axi_bid),


    .sb_axi_arvalid         (sb_axi_arvalid),
    .sb_axi_arready         (sb_axi_arready),
    .sb_axi_arid            (sb_axi_arid),
    .sb_axi_araddr          (sb_axi_araddr),
    .sb_axi_arregion        (sb_axi_arregion),
    .sb_axi_arlen           (sb_axi_arlen),
    .sb_axi_arsize          (sb_axi_arsize),
    .sb_axi_arburst         (sb_axi_arburst),
    .sb_axi_arlock          (sb_axi_arlock),
    .sb_axi_arcache         (sb_axi_arcache),
    .sb_axi_arprot          (sb_axi_arprot),
    .sb_axi_arqos           (sb_axi_arqos),

    .sb_axi_rvalid          (sb_axi_rvalid),
    .sb_axi_rready          (sb_axi_rready),
    .sb_axi_rid             (sb_axi_rid),
    .sb_axi_rdata           (sb_axi_rdata),
    .sb_axi_rresp           (sb_axi_rresp),
    .sb_axi_rlast           (sb_axi_rlast),

    //-------------------------- DMA AXI signals--------------------------
    // AXI Write Channels
    .dma_axi_awvalid        (dma_axi_awvalid),
    .dma_axi_awready        (dma_axi_awready),
    .dma_axi_awid           ('0),
    .dma_axi_awaddr         (lsu_axi_awaddr),
    .dma_axi_awsize         (lsu_axi_awsize),
    .dma_axi_awprot         (lsu_axi_awprot),
    .dma_axi_awlen          (lsu_axi_awlen),
    .dma_axi_awburst        (lsu_axi_awburst),


    .dma_axi_wvalid         (dma_axi_wvalid),
    .dma_axi_wready         (dma_axi_wready),
    .dma_axi_wdata          (lsu_axi_wdata),
    .dma_axi_wstrb          (lsu_axi_wstrb),
    .dma_axi_wlast          (lsu_axi_wlast),

    .dma_axi_bvalid         (dma_axi_bvalid),
    .dma_axi_bready         (dma_axi_bready),
    .dma_axi_bresp          (dma_axi_bresp),
    .dma_axi_bid            (),


    .dma_axi_arvalid        (dma_axi_arvalid),
    .dma_axi_arready        (dma_axi_arready),
    .dma_axi_arid           ('0),
    .dma_axi_araddr         (lsu_axi_araddr),
    .dma_axi_arsize         (lsu_axi_arsize),
    .dma_axi_arprot         (lsu_axi_arprot),
    .dma_axi_arlen          (lsu_axi_arlen),
    .dma_axi_arburst        (lsu_axi_arburst),

    .dma_axi_rvalid         (dma_axi_rvalid),
    .dma_axi_rready         (dma_axi_rready),
    .dma_axi_rid            (),
    .dma_axi_rdata          (dma_axi_rdata),
    .dma_axi_rresp          (dma_axi_rresp),
    .dma_axi_rlast          (dma_axi_rlast),
`endif
    .timer_int              ( timer_int ),
    .soft_int               ( soft_int ),
    .extintsrc_req          ( ext_int ),

    .lsu_bus_clk_en         ( 1'b1  ),// Clock ratio b/w cpu core clk & AHB master interface
    .ifu_bus_clk_en         ( 1'b1  ),// Clock ratio b/w cpu core clk & AHB master interface
    .dbg_bus_clk_en         ( 1'b1  ),// Clock ratio b/w cpu core clk & AHB Debug master interface
    .dma_bus_clk_en         ( 1'b1  ),// Clock ratio b/w cpu core clk & AHB slave interface

    .trace_rv_i_insn_ip     (trace_rv_i_insn_ip),
    .trace_rv_i_address_ip  (trace_rv_i_address_ip),
    .trace_rv_i_valid_ip    (trace_rv_i_valid_ip),
    .trace_rv_i_exception_ip(trace_rv_i_exception_ip),
    .trace_rv_i_ecause_ip   (trace_rv_i_ecause_ip),
    .trace_rv_i_interrupt_ip(trace_rv_i_interrupt_ip),
    .trace_rv_i_tval_ip     (trace_rv_i_tval_ip),

    .jtag_tck               (jtag_tck),
    .jtag_tms               (jtag_tms),
    .jtag_tdi               (jtag_tdi),
    .jtag_trst_n            (jtag_trst_n),
    .jtag_tdo               (jtag_tdo),
    .jtag_tdoEn             (),

    .mpc_debug_halt_ack     ( mpc_debug_halt_ack),
    .mpc_debug_halt_req     ( 1'b0),
    .mpc_debug_run_ack      ( mpc_debug_run_ack),
    .mpc_debug_run_req      ( 1'b1),
    .mpc_reset_run_req      ( 1'b1),             // Start running after reset
     .debug_brkpt_status    (debug_brkpt_status),

    .i_cpu_halt_req         ( 1'b0  ),    // Async halt req to CPU
    .o_cpu_halt_ack         ( o_cpu_halt_ack ),    // core response to halt
    .o_cpu_halt_status      ( o_cpu_halt_status ), // 1'b1 indicates core is halted
    .i_cpu_run_req          ( 1'b0  ),     // Async restart req to CPU
    .o_debug_mode_status    (o_debug_mode_status),
    .o_cpu_run_ack          ( o_cpu_run_ack ),     // Core response to run req

    .dec_tlu_perfcnt0       (),
    .dec_tlu_perfcnt1       (),
    .dec_tlu_perfcnt2       (),
    .dec_tlu_perfcnt3       (),

    .mem_clk                (el2_mem_export.clk),

    .iccm_clken             (el2_mem_export.iccm_clken),
    .iccm_wren_bank         (el2_mem_export.iccm_wren_bank),
    .iccm_addr_bank         (el2_mem_export.iccm_addr_bank),
    .iccm_bank_wr_data      (el2_mem_export.iccm_bank_wr_data),
    .iccm_bank_wr_ecc       (el2_mem_export.iccm_bank_wr_ecc),
    .iccm_bank_dout         (el2_mem_export.iccm_bank_dout),
    .iccm_bank_ecc          (el2_mem_export.iccm_bank_ecc),

    .dccm_clken             (el2_mem_export.dccm_clken),
    .dccm_wren_bank         (el2_mem_export.dccm_wren_bank),
    .dccm_addr_bank         (el2_mem_export.dccm_addr_bank),
    .dccm_wr_data_bank      (el2_mem_export.dccm_wr_data_bank),
    .dccm_wr_ecc_bank       (el2_mem_export.dccm_wr_ecc_bank),
    .dccm_bank_dout         (el2_mem_export.dccm_bank_dout),
    .dccm_bank_ecc          (el2_mem_export.dccm_bank_ecc),

    .iccm_ecc_single_error  (),
    .iccm_ecc_double_error  (),
    .dccm_ecc_single_error  (),
    .dccm_ecc_double_error  (),

// remove mems DFT pins for opensource
    .ic_data_ext_in_pkt     ('0),
    .ic_tag_ext_in_pkt      ('0),

    .core_id                ('0),
    .scan_mode              ( 1'b0 ),         // To enable scan mode
    .mbist_mode             ( 1'b0 ),        // to enable mbist

    .dmi_uncore_enable      (),
    .dmi_uncore_en          (),
    .dmi_uncore_wr_en       (),
    .dmi_uncore_addr        (),
    .dmi_uncore_wdata       (),
    .dmi_uncore_rdata       ()

);


   //=========================================================================-
   // AHB I$ instance
   //=========================================================================-
`ifdef RV_BUILD_AHB_LITE

ahb_sif imem (
     // Inputs
     .HWDATA(64'h0),
     .HCLK(core_clk),
     .HSEL(1'b1),
     .HPROT(ic_hprot),
     .HWRITE(ic_hwrite),
     .HTRANS(ic_htrans),
     .HSIZE(ic_hsize),
     .HREADY(ic_hready),
     .HRESETn(rst_l),
     .HADDR(ic_haddr),
     .HBURST(ic_hburst),

     // Outputs
     .HREADYOUT(ic_hready),
     .HRESP(ic_hresp),
     .HRDATA(ic_hrdata[63:0])
);


ahb_sif lmem (
     // Inputs
     .HWDATA(mux_hwdata),
     .HCLK(core_clk),
     .HSEL(mux_hsel),
     .HPROT(mux_hprot),
     .HWRITE(mux_hwrite),
     .HTRANS(mux_htrans),
     .HSIZE(mux_hsize),
     .HREADY(mux_hready),
     .HRESETn(rst_l),
     .HADDR(mux_haddr),
     .HBURST(mux_hburst),

     // Outputs
     .HREADYOUT(mux_hreadyout),
     .HRESP(mux_hresp),
     .HRDATA(mux_hrdata[63:0])
);

`endif
`ifdef RV_BUILD_AXI4
axi_slv #(.TAGW(`RV_IFU_BUS_TAG)) imem(
    .aclk(core_clk),
    .rst_l(rst_l),
    .arvalid(ifu_axi_arvalid),
    .arready(ifu_axi_arready),
    .araddr(ifu_axi_araddr),
    .arid(ifu_axi_arid),
    .arlen(ifu_axi_arlen),
    .arburst(ifu_axi_arburst),
    .arsize(ifu_axi_arsize),

    .rvalid(ifu_axi_rvalid),
    .rready(ifu_axi_rready),
    .rdata(ifu_axi_rdata),
    .rresp(ifu_axi_rresp),
    .rid(ifu_axi_rid),
    .rlast(ifu_axi_rlast),

    .awvalid(1'b0),
    .awready(),
    .awaddr('0),
    .awid('0),
    .awlen('0),
    .awburst('0),
    .awsize('0),

    .wdata('0),
    .wstrb('0),
    .wvalid(1'b0),
    .wready(),

    .bvalid(),
    .bready(1'b0),
    .bresp(),
    .bid()
);

defparam lmem.TAGW = RV_MUX_BUS_TAG;

//axi_slv #(.TAGW(`RV_LSU_BUS_TAG)) lmem(
axi_slv  lmem(
    .aclk(core_clk),
    .rst_l(rst_l),
    .arvalid(lmem_axi_arvalid),
    .arready(lmem_axi_arready),
    .araddr(mux_axi_araddr),
    .arid(mux_axi_arid),
    .arlen(mux_axi_arlen),
    .arburst(mux_axi_arburst),
    .arsize(mux_axi_arsize),

    .rvalid(lmem_axi_rvalid),
    .rready(lmem_axi_rready),
    .rdata(lmem_axi_rdata),
    .rresp(lmem_axi_rresp),
    .rid(lmem_axi_rid),
    .rlast(lmem_axi_rlast),

    .awvalid(lmem_axi_awvalid),
    .awready(lmem_axi_awready),
    .awaddr(mux_axi_awaddr),
    .awid(mux_axi_awid),
    .awlen(mux_axi_awlen),
    .awburst(mux_axi_awburst),
    .awsize(mux_axi_awsize),

    .wdata(mux_axi_wdata),
    .wstrb(mux_axi_wstrb),
    .wvalid(lmem_axi_wvalid),
    .wready(lmem_axi_wready),

    .bvalid(lmem_axi_bvalid),
    .bready(lmem_axi_bready),
    .bresp(lmem_axi_bresp),
    .bid(lmem_axi_bid)
);

axi_lsu_dma_bridge # (RV_MUX_BUS_TAG, RV_MUX_BUS_TAG) bridge(
    .clk(core_clk),
    .reset_l(rst_l),

    .m_arvalid(mux_axi_arvalid),
    .m_arid(mux_axi_arid),
    .m_araddr(mux_axi_araddr),
    .m_arready(mux_axi_arready),

    .m_rvalid(mux_axi_rvalid),
    .m_rready(mux_axi_rready),
    .m_rdata(mux_axi_rdata),
    .m_rid(mux_axi_rid),
    .m_rresp(mux_axi_rresp),
    .m_rlast(mux_axi_rlast),

    .m_awvalid(mux_axi_awvalid),
    .m_awid(mux_axi_awid),
    .m_awaddr(mux_axi_awaddr),
    .m_awready(mux_axi_awready),

    .m_wvalid(mux_axi_wvalid),
    .m_wready(mux_axi_wready),

    .m_bresp(mux_axi_bresp),
    .m_bvalid(mux_axi_bvalid),
    .m_bid(mux_axi_bid),
    .m_bready(mux_axi_bready),

    .s0_arvalid(lmem_axi_arvalid),
    .s0_arready(lmem_axi_arready),

    .s0_rvalid(lmem_axi_rvalid),
    .s0_rid(lmem_axi_rid),
    .s0_rresp(lmem_axi_rresp),
    .s0_rdata(lmem_axi_rdata),
    .s0_rlast(lmem_axi_rlast),
    .s0_rready(lmem_axi_rready),

    .s0_awvalid(lmem_axi_awvalid),
    .s0_awready(lmem_axi_awready),

    .s0_wvalid(lmem_axi_wvalid),
    .s0_wready(lmem_axi_wready),

    .s0_bresp(lmem_axi_bresp),
    .s0_bvalid(lmem_axi_bvalid),
    .s0_bid(lmem_axi_bid),
    .s0_bready(lmem_axi_bready),


    .s1_arvalid(dma_axi_arvalid),
    .s1_arready(dma_axi_arready),

    .s1_rvalid(dma_axi_rvalid),
    .s1_rresp(dma_axi_rresp),
    .s1_rdata(dma_axi_rdata),
    .s1_rlast(dma_axi_rlast),
    .s1_rready(dma_axi_rready),

    .s1_awvalid(dma_axi_awvalid),
    .s1_awready(dma_axi_awready),

    .s1_wvalid(dma_axi_wvalid),
    .s1_wready(dma_axi_wready),

    .s1_bresp(dma_axi_bresp),
    .s1_bvalid(dma_axi_bvalid),
    .s1_bready(dma_axi_bready)
);


`endif

task preload_iccm;
bit[31:0] data;
bit[31:0] addr, eaddr, saddr;

/*
addresses:
 0xfffffff0 - ICCM start address to load
 0xfffffff4 - ICCM end address to load
*/
`ifndef VERILATOR
init_iccm();
`endif
addr = 'hffff_fff0;
saddr = {lmem.mem[addr+3],lmem.mem[addr+2],lmem.mem[addr+1],lmem.mem[addr]};
if ( (saddr < `RV_ICCM_SADR) || (saddr > `RV_ICCM_EADR)) return;
`ifndef RV_ICCM_ENABLE
    $display("********************************************************");
    $display("ICCM preload: there is no ICCM in VeeR, terminating !!!");
    $display("********************************************************");
    $finish;
`endif
addr += 4;
eaddr = {lmem.mem[addr+3],lmem.mem[addr+2],lmem.mem[addr+1],lmem.mem[addr]};
$display("ICCM pre-load from %h to %h", saddr, eaddr);

for(addr= saddr; addr <= eaddr; addr+=4) begin
    data = {imem.mem[addr+3],imem.mem[addr+2],imem.mem[addr+1],imem.mem[addr]};
    slam_iccm_ram(addr, data == 0 ? 0 : {riscv_ecc32(data),data});
end

endtask


task preload_dccm;
bit[31:0] data;
bit[31:0] addr, saddr, eaddr;

/*
addresses:
 0xffff_fff8 - DCCM start address to load
 0xffff_fffc - DCCM end address to load
*/

addr = 'hffff_fff8;
saddr = {lmem.mem[addr+3],lmem.mem[addr+2],lmem.mem[addr+1],lmem.mem[addr]};
if (saddr < `RV_DCCM_SADR || saddr > `RV_DCCM_EADR) return;
`ifndef RV_DCCM_ENABLE
    $display("********************************************************");
    $display("DCCM preload: there is no DCCM in VeeR, terminating !!!");
    $display("********************************************************");
    $finish;
`endif
addr += 4;
eaddr = {lmem.mem[addr+3],lmem.mem[addr+2],lmem.mem[addr+1],lmem.mem[addr]};
$display("DCCM pre-load from %h to %h", saddr, eaddr);

for(addr=saddr; addr <= eaddr; addr+=4) begin
    data = {lmem.mem[addr+3],lmem.mem[addr+2],lmem.mem[addr+1],lmem.mem[addr]};
    slam_dccm_ram(addr, data == 0 ? 0 : {riscv_ecc32(data),data});
end

endtask



`define DRAM(bk) Gen_dccm_enable.dccm_loop[bk].dccm.dccm_bank.ram_core
`define IRAM(bk) Gen_iccm_enable.iccm_loop[bk].iccm.iccm_bank.ram_core


task slam_dccm_ram(input [31:0] addr, input[38:0] data);
int bank, indx;
bank = get_dccm_bank(addr, indx);
`ifdef RV_DCCM_ENABLE
case(bank)
0: `DRAM(0)[indx] = data;
1: `DRAM(1)[indx] = data;
`ifdef RV_DCCM_NUM_BANKS_4
2: `DRAM(2)[indx] = data;
3: `DRAM(3)[indx] = data;
`endif
`ifdef RV_DCCM_NUM_BANKS_8
2: `DRAM(2)[indx] = data;
3: `DRAM(3)[indx] = data;
4: `DRAM(4)[indx] = data;
5: `DRAM(5)[indx] = data;
6: `DRAM(6)[indx] = data;
7: `DRAM(7)[indx] = data;
`endif
endcase
`endif
//$display("Writing bank %0d indx=%0d A=%h, D=%h",bank, indx, addr, data);
endtask


task slam_iccm_ram( input[31:0] addr, input[38:0] data);
int bank, idx;

bank = get_iccm_bank(addr, idx);
`ifdef RV_ICCM_ENABLE
case(bank) // {
  0: `IRAM(0)[idx] = data;
  1: `IRAM(1)[idx] = data;
 `ifdef RV_ICCM_NUM_BANKS_4
  2: `IRAM(2)[idx] = data;
  3: `IRAM(3)[idx] = data;
 `endif
 `ifdef RV_ICCM_NUM_BANKS_8
  2: `IRAM(2)[idx] = data;
  3: `IRAM(3)[idx] = data;
  4: `IRAM(4)[idx] = data;
  5: `IRAM(5)[idx] = data;
  6: `IRAM(6)[idx] = data;
  7: `IRAM(7)[idx] = data;
 `endif

 `ifdef RV_ICCM_NUM_BANKS_16
  2: `IRAM(2)[idx] = data;
  3: `IRAM(3)[idx] = data;
  4: `IRAM(4)[idx] = data;
  5: `IRAM(5)[idx] = data;
  6: `IRAM(6)[idx] = data;
  7: `IRAM(7)[idx] = data;
  8: `IRAM(8)[idx] = data;
  9: `IRAM(9)[idx] = data;
  10: `IRAM(10)[idx] = data;
  11: `IRAM(11)[idx] = data;
  12: `IRAM(12)[idx] = data;
  13: `IRAM(13)[idx] = data;
  14: `IRAM(14)[idx] = data;
  15: `IRAM(15)[idx] = data;
 `endif
endcase // }
`endif
endtask

task init_iccm;
`ifdef RV_ICCM_ENABLE
    `IRAM(0) = '{default:39'h0};
    `IRAM(1) = '{default:39'h0};
`ifdef RV_ICCM_NUM_BANKS_4
    `IRAM(2) = '{default:39'h0};
    `IRAM(3) = '{default:39'h0};
`endif
`ifdef RV_ICCM_NUM_BANKS_8
    `IRAM(4) = '{default:39'h0};
    `IRAM(5) = '{default:39'h0};
    `IRAM(6) = '{default:39'h0};
    `IRAM(7) = '{default:39'h0};
`endif

`ifdef RV_ICCM_NUM_BANKS_16
    `IRAM(4) = '{default:39'h0};
    `IRAM(5) = '{default:39'h0};
    `IRAM(6) = '{default:39'h0};
    `IRAM(7) = '{default:39'h0};
    `IRAM(8) = '{default:39'h0};
    `IRAM(9) = '{default:39'h0};
    `IRAM(10) = '{default:39'h0};
    `IRAM(11) = '{default:39'h0};
    `IRAM(12) = '{default:39'h0};
    `IRAM(13) = '{default:39'h0};
    `IRAM(14) = '{default:39'h0};
    `IRAM(15) = '{default:39'h0};
 `endif
`endif
endtask


function[6:0] riscv_ecc32(input[31:0] data);
reg[6:0] synd;
synd[0] = ^(data & 32'h56aa_ad5b);
synd[1] = ^(data & 32'h9b33_366d);
synd[2] = ^(data & 32'he3c3_c78e);
synd[3] = ^(data & 32'h03fc_07f0);
synd[4] = ^(data & 32'h03ff_f800);
synd[5] = ^(data & 32'hfc00_0000);
synd[6] = ^{data, synd[5:0]};
return synd;
endfunction

function int get_dccm_bank(input[31:0] addr,  output int bank_idx);
`ifdef RV_DCCM_NUM_BANKS_2
    bank_idx = int'(addr[`RV_DCCM_BITS-1:3]);
    return int'( addr[2]);
`elsif RV_DCCM_NUM_BANKS_4
    bank_idx = int'(addr[`RV_DCCM_BITS-1:4]);
    return int'(addr[3:2]);
`elsif RV_DCCM_NUM_BANKS_8
    bank_idx = int'(addr[`RV_DCCM_BITS-1:5]);
    return int'( addr[4:2]);
`endif
endfunction

function int get_iccm_bank(input[31:0] addr,  output int bank_idx);
`ifdef RV_DCCM_NUM_BANKS_2
    bank_idx = int'(addr[`RV_DCCM_BITS-1:3]);
    return int'( addr[2]);
`elsif RV_ICCM_NUM_BANKS_4
    bank_idx = int'(addr[`RV_ICCM_BITS-1:4]);
    return int'(addr[3:2]);
`elsif RV_ICCM_NUM_BANKS_8
    bank_idx = int'(addr[`RV_ICCM_BITS-1:5]);
    return int'( addr[4:2]);
`elsif RV_ICCM_NUM_BANKS_16
    bank_idx = int'(addr[`RV_ICCM_BITS-1:6]);
    return int'( addr[5:2]);
`endif
endfunction

task dump_signature ();
    integer fp, i;

    $display("Dumping memory signature (0x%08X - 0x%08X)...",
        mem_signature_begin,
        mem_signature_end
    );

    fp = $fopen("veer.signature", "w");
    for (i=mem_signature_begin; i<mem_signature_end; i=i+4) begin

        // From DCCM
`ifdef RV_DCCM_ENABLE
        if (i >= `RV_DCCM_SADR && i < `RV_DCCM_EADR) begin
            bit[38:0] data;
            int bank, indx;
            bank = get_dccm_bank(i, indx);

            case (bank)
            0: data = `DRAM(0)[indx];
            1: data = `DRAM(1)[indx];
            `ifdef RV_DCCM_NUM_BANKS_4
            2: data = `DRAM(2)[indx];
            3: data = `DRAM(3)[indx];
            `endif
            `ifdef RV_DCCM_NUM_BANKS_8
            2: data = `DRAM(2)[indx];
            3: data = `DRAM(3)[indx];
            4: data = `DRAM(4)[indx];
            5: data = `DRAM(5)[indx];
            6: data = `DRAM(6)[indx];
            7: data = `DRAM(7)[indx];
            `endif
            endcase

            $fwrite(fp, "%08X\n", data[31:0]);
        end else
`endif
        // From RAM
        begin
            $fwrite(fp, "%02X%02X%02X%02X\n",
                lmem.mem[i+3],
                lmem.mem[i+2],
                lmem.mem[i+1],
                lmem.mem[i+0]
            );
        end
    end

    $fclose(fp);
endtask

//////////////////////////////////////////////////////
// DCCM
//
if (pt.DCCM_ENABLE == 1) begin: Gen_dccm_enable
    `define EL2_LOCAL_DCCM_RAM_TEST_PORTS   .TEST1   (1'b0   ), \
                                            .RME     (1'b0   ), \
                                            .RM      (4'b0000), \
                                            .LS      (1'b0   ), \
                                            .DS      (1'b0   ), \
                                            .SD      (1'b0   ), \
                                            .TEST_RNM(1'b0   ), \
                                            .BC1     (1'b0   ), \
                                            .BC2     (1'b0   ), \

    logic [pt.DCCM_NUM_BANKS-1:0] [pt.DCCM_FDATA_WIDTH-1:0] dccm_wdata_bitflip;
    int ii;
    localparam DCCM_INDEX_DEPTH = ((pt.DCCM_SIZE)*1024)/((pt.DCCM_BYTE_WIDTH)*(pt.DCCM_NUM_BANKS));  // Depth of memory bank
    // 8 Banks, 16KB each (2048 x 72)
    always_ff @(el2_mem_export.clk) begin : inject_dccm_ecc_error
        if (~error_injection_mode.dccm_single_bit_error && ~error_injection_mode.dccm_double_bit_error) begin
            dccm_wdata_bitflip <= '{default:0};
        end else if (el2_mem_export.dccm_clken & el2_mem_export.dccm_wren_bank) begin
            for (ii=0; ii<pt.DCCM_NUM_BANKS; ii++) begin: dccm_bitflip_injection_loop
                dccm_wdata_bitflip[ii] <= get_bitflip_mask(error_injection_mode.dccm_double_bit_error);
            end
        end
    end
    for (genvar i=0; i<pt.DCCM_NUM_BANKS; i++) begin: dccm_loop
        assign dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0] = {el2_mem_export.dccm_wr_ecc_bank[i], el2_mem_export.dccm_wr_data_bank[i]} ^ dccm_wdata_bitflip[i];
        assign el2_mem_export.dccm_bank_dout[i] = dccm_bank_fdout[i][31:0];
        assign el2_mem_export.dccm_bank_ecc[i] = dccm_bank_fdout[i][38:32];

        if (DCCM_INDEX_DEPTH == 32768) begin : dccm
            ram_32768x39  dccm_bank (
                                    // Primary ports
                                    .ME(el2_mem_export.dccm_clken[i]),
                                    .CLK(el2_mem_export.clk),
                                    .WE(el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 16384) begin : dccm
            ram_16384x39  dccm_bank (
                                    // Primary ports
                                    .ME(el2_mem_export.dccm_clken[i]),
                                    .CLK(el2_mem_export.clk),
                                    .WE(el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 8192) begin : dccm
            ram_8192x39  dccm_bank (
                                    // Primary ports
                                    .ME(el2_mem_export.dccm_clken[i]),
                                    .CLK(el2_mem_export.clk),
                                    .WE(el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 4096) begin : dccm
            ram_4096x39  dccm_bank (
                                    // Primary ports
                                    .ME(el2_mem_export.dccm_clken[i]),
                                    .CLK(el2_mem_export.clk),
                                    .WE(el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 3072) begin : dccm
            ram_3072x39  dccm_bank (
                                    // Primary ports
                                    .ME(el2_mem_export.dccm_clken[i]),
                                    .CLK(el2_mem_export.clk),
                                    .WE(el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 2048) begin : dccm
            ram_2048x39  dccm_bank (
                                    // Primary ports
                                    .ME(el2_mem_export.dccm_clken[i]),
                                    .CLK(el2_mem_export.clk),
                                    .WE(el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 1024) begin : dccm
            ram_1024x39  dccm_bank (
                                    // Primary ports
                                    .ME(el2_mem_export.dccm_clken[i]),
                                    .CLK(el2_mem_export.clk),
                                    .WE(el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 512) begin : dccm
            ram_512x39  dccm_bank (
                                    // Primary ports
                                    .ME(el2_mem_export.dccm_clken[i]),
                                    .CLK(el2_mem_export.clk),
                                    .WE(el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 256) begin : dccm
            ram_256x39  dccm_bank (
                                    // Primary ports
                                    .ME(el2_mem_export.dccm_clken[i]),
                                    .CLK(el2_mem_export.clk),
                                    .WE(el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 128) begin : dccm
            ram_128x39  dccm_bank (
                                    // Primary ports
                                    .ME(el2_mem_export.dccm_clken[i]),
                                    .CLK(el2_mem_export.clk),
                                    .WE(el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
    end : dccm_loop
end :Gen_dccm_enable

//////////////////////////////////////////////////////
// ICCM
//
if (pt.ICCM_ENABLE) begin : Gen_iccm_enable

logic [pt.ICCM_NUM_BANKS-1:0] [38:0] iccm_wdata_bitflip;
int jj;
always_ff @(el2_mem_export.clk) begin : inject_iccm_ecc_error
    if (~error_injection_mode.iccm_single_bit_error && ~error_injection_mode.iccm_double_bit_error) begin
        iccm_wdata_bitflip <= '{default:0};
    end else if (el2_mem_export.iccm_clken & el2_mem_export.iccm_wren_bank) begin
        for (jj=0; jj<pt.ICCM_NUM_BANKS; jj++) begin: iccm_bitflip_injection_loop
            iccm_wdata_bitflip[jj] <= get_bitflip_mask(error_injection_mode.iccm_double_bit_error);
        end
    end
end
for (genvar i=0; i<pt.ICCM_NUM_BANKS; i++) begin: iccm_loop
    assign iccm_bank_wr_fdata[i][32+pt.ICCM_ECC_WIDTH-1:0] = {el2_mem_export.iccm_bank_wr_ecc[i], el2_mem_export.iccm_bank_wr_data[i]} ^ iccm_wdata_bitflip[i];
    assign el2_mem_export.iccm_bank_dout[i] = iccm_bank_fdout[i][31:0];
    assign el2_mem_export.iccm_bank_ecc[i] = iccm_bank_fdout[i][32+pt.ICCM_ECC_WIDTH-1:32];

     if (pt.ICCM_INDEX_BITS == 6 ) begin : iccm
               ram_64x39 iccm_bank (
                                     // Primary ports
                                     .CLK(el2_mem_export.clk),
                                     .ME(el2_mem_export.iccm_clken[i]),
                                     .WE(el2_mem_export.iccm_wren_bank[i]),
                                     .ADR(el2_mem_export.iccm_addr_bank[i]),
                                     .D(iccm_bank_wr_fdata[i][38:0]),
                                     .Q(iccm_bank_fdout[i][38:0]),
                                     .ROP ( ),
                                     // These are used by SoC
                                     .TEST1    (1'b0   ),
                                     .RME      (1'b0   ),
                                     .RM       (4'b0000),
                                     .LS       (1'b0   ),
                                     .DS       (1'b0   ),
                                     .SD       (1'b0   ) ,
                                     .TEST_RNM (1'b0   ),
                                     .BC1      (1'b0   ),
                                     .BC2      (1'b0   )

                                      );
     end // block: iccm

   else if (pt.ICCM_INDEX_BITS == 7 ) begin : iccm
               ram_128x39 iccm_bank (
                                     // Primary ports
                                     .CLK(el2_mem_export.clk),
                                     .ME(el2_mem_export.iccm_clken[i]),
                                     .WE(el2_mem_export.iccm_wren_bank[i]),
                                     .ADR(el2_mem_export.iccm_addr_bank[i]),
                                     .D(iccm_bank_wr_fdata[i][38:0]),
                                     .Q(iccm_bank_fdout[i][38:0]),
                                     .ROP ( ),
                                     // These are used by SoC
                                     .TEST1    (1'b0   ),
                                     .RME      (1'b0   ),
                                     .RM       (4'b0000),
                                     .LS       (1'b0   ),
                                     .DS       (1'b0   ),
                                     .SD       (1'b0   ) ,
                                     .TEST_RNM (1'b0   ),
                                     .BC1      (1'b0   ),
                                     .BC2      (1'b0   )

                                      );
     end // block: iccm

     else if (pt.ICCM_INDEX_BITS == 8 ) begin : iccm
               ram_256x39 iccm_bank (
                                     // Primary ports
                                     .CLK(el2_mem_export.clk),
                                     .ME(el2_mem_export.iccm_clken[i]),
                                     .WE(el2_mem_export.iccm_wren_bank[i]),
                                     .ADR(el2_mem_export.iccm_addr_bank[i]),
                                     .D(iccm_bank_wr_fdata[i][38:0]),
                                     .Q(iccm_bank_fdout[i][38:0]),
                                     .ROP ( ),
                                     // These are used by SoC
                                     .TEST1    (1'b0   ),
                                     .RME      (1'b0   ),
                                     .RM       (4'b0000),
                                     .LS       (1'b0   ),
                                     .DS       (1'b0   ),
                                     .SD       (1'b0   ) ,
                                     .TEST_RNM (1'b0   ),
                                     .BC1      (1'b0   ),
                                     .BC2      (1'b0   )

                                      );
     end // block: iccm
     else if (pt.ICCM_INDEX_BITS == 9 ) begin : iccm
               ram_512x39 iccm_bank (
                                     // Primary ports
                                     .CLK(el2_mem_export.clk),
                                     .ME(el2_mem_export.iccm_clken[i]),
                                     .WE(el2_mem_export.iccm_wren_bank[i]),
                                     .ADR(el2_mem_export.iccm_addr_bank[i]),
                                     .D(iccm_bank_wr_fdata[i][38:0]),
                                     .Q(iccm_bank_fdout[i][38:0]),
                                     .ROP ( ),
                                     // These are used by SoC
                                     .TEST1    (1'b0   ),
                                     .RME      (1'b0   ),
                                     .RM       (4'b0000),
                                     .LS       (1'b0   ),
                                     .DS       (1'b0   ),
                                     .SD       (1'b0   ) ,
                                     .TEST_RNM (1'b0   ),
                                     .BC1      (1'b0   ),
                                     .BC2      (1'b0   )

                                      );
     end // block: iccm
     else if (pt.ICCM_INDEX_BITS == 10 ) begin : iccm
               ram_1024x39 iccm_bank (
                                     // Primary ports
                                     .CLK(el2_mem_export.clk),
                                     .ME(el2_mem_export.iccm_clken[i]),
                                     .WE(el2_mem_export.iccm_wren_bank[i]),
                                     .ADR(el2_mem_export.iccm_addr_bank[i]),
                                     .D(iccm_bank_wr_fdata[i][38:0]),
                                     .Q(iccm_bank_fdout[i][38:0]),
                                     .ROP ( ),
                                     // These are used by SoC
                                     .TEST1    (1'b0   ),
                                     .RME      (1'b0   ),
                                     .RM       (4'b0000),
                                     .LS       (1'b0   ),
                                     .DS       (1'b0   ),
                                     .SD       (1'b0   ) ,
                                     .TEST_RNM (1'b0   ),
                                     .BC1      (1'b0   ),
                                     .BC2      (1'b0   )

                                      );
     end // block: iccm
     else if (pt.ICCM_INDEX_BITS == 11 ) begin : iccm
               ram_2048x39 iccm_bank (
                                     // Primary ports
                                     .CLK(el2_mem_export.clk),
                                     .ME(el2_mem_export.iccm_clken[i]),
                                     .WE(el2_mem_export.iccm_wren_bank[i]),
                                     .ADR(el2_mem_export.iccm_addr_bank[i]),
                                     .D(iccm_bank_wr_fdata[i][38:0]),
                                     .Q(iccm_bank_fdout[i][38:0]),
                                     .ROP ( ),
                                     // These are used by SoC
                                     .TEST1    (1'b0   ),
                                     .RME      (1'b0   ),
                                     .RM       (4'b0000),
                                     .LS       (1'b0   ),
                                     .DS       (1'b0   ),
                                     .SD       (1'b0   ) ,
                                     .TEST_RNM (1'b0   ),
                                     .BC1      (1'b0   ),
                                     .BC2      (1'b0   )

                                      );
     end // block: iccm
     else if (pt.ICCM_INDEX_BITS == 12 ) begin : iccm
               ram_4096x39 iccm_bank (
                                     // Primary ports
                                     .CLK(el2_mem_export.clk),
                                     .ME(el2_mem_export.iccm_clken[i]),
                                     .WE(el2_mem_export.iccm_wren_bank[i]),
                                     .ADR(el2_mem_export.iccm_addr_bank[i]),
                                     .D(iccm_bank_wr_fdata[i][38:0]),
                                     .Q(iccm_bank_fdout[i][38:0]),
                                     .ROP ( ),
                                     // These are used by SoC
                                     .TEST1    (1'b0   ),
                                     .RME      (1'b0   ),
                                     .RM       (4'b0000),
                                     .LS       (1'b0   ),
                                     .DS       (1'b0   ),
                                     .SD       (1'b0   ) ,
                                     .TEST_RNM (1'b0   ),
                                     .BC1      (1'b0   ),
                                     .BC2      (1'b0   )

                                      );
     end // block: iccm
     else if (pt.ICCM_INDEX_BITS == 13 ) begin : iccm
               ram_8192x39 iccm_bank (
                                     // Primary ports
                                     .CLK(el2_mem_export.clk),
                                     .ME(el2_mem_export.iccm_clken[i]),
                                     .WE(el2_mem_export.iccm_wren_bank[i]),
                                     .ADR(el2_mem_export.iccm_addr_bank[i]),
                                     .D(iccm_bank_wr_fdata[i][38:0]),
                                     .Q(iccm_bank_fdout[i][38:0]),
                                     .ROP ( ),
                                     // These are used by SoC
                                     .TEST1    (1'b0   ),
                                     .RME      (1'b0   ),
                                     .RM       (4'b0000),
                                     .LS       (1'b0   ),
                                     .DS       (1'b0   ),
                                     .SD       (1'b0   ) ,
                                     .TEST_RNM (1'b0   ),
                                     .BC1      (1'b0   ),
                                     .BC2      (1'b0   )

                                      );
     end // block: iccm
     else if (pt.ICCM_INDEX_BITS == 14 ) begin : iccm
               ram_16384x39 iccm_bank (
                                     // Primary ports
                                     .CLK(el2_mem_export.clk),
                                     .ME(el2_mem_export.iccm_clken[i]),
                                     .WE(el2_mem_export.iccm_wren_bank[i]),
                                     .ADR(el2_mem_export.iccm_addr_bank[i]),
                                     .D(iccm_bank_wr_fdata[i][38:0]),
                                     .Q(iccm_bank_fdout[i][38:0]),
                                     .ROP ( ),
                                     // These are used by SoC
                                     .TEST1    (1'b0   ),
                                     .RME      (1'b0   ),
                                     .RM       (4'b0000),
                                     .LS       (1'b0   ),
                                     .DS       (1'b0   ),
                                     .SD       (1'b0   ) ,
                                     .TEST_RNM (1'b0   ),
                                     .BC1      (1'b0   ),
                                     .BC2      (1'b0   )

                                      );
     end // block: iccm
     else begin : iccm
               ram_32768x39 iccm_bank (
                                     // Primary ports
                                     .CLK(el2_mem_export.clk),
                                     .ME(el2_mem_export.iccm_clken[i]),
                                     .WE(el2_mem_export.iccm_wren_bank[i]),
                                     .ADR(el2_mem_export.iccm_addr_bank[i]),
                                     .D(iccm_bank_wr_fdata[i][38:0]),
                                     .Q(iccm_bank_fdout[i][38:0]),
                                     .ROP ( ),
                                     // These are used by SoC
                                     .TEST1    (1'b0   ),
                                     .RME      (1'b0   ),
                                     .RM       (4'b0000),
                                     .LS       (1'b0   ),
                                     .DS       (1'b0   ),
                                     .SD       (1'b0   ) ,
                                     .TEST_RNM (1'b0   ),
                                     .BC1      (1'b0   ),
                                     .BC2      (1'b0   )

                                      );
     end // block: iccm
end : iccm_loop
end : Gen_iccm_enable

`ifdef RV_OPENOCD_TEST
jtagdpi #(
    .Name           ("jtag0"),
    .ListenPort     (5000)
) jtagdpi (
    .clk_i          (core_clk),
    .rst_ni         (rst_l),
    .jtag_tck       (jtag_tck),
    .jtag_tms       (jtag_tms),
    .jtag_tdi       (jtag_tdi),
    .jtag_tdo       (jtag_tdo),
    .jtag_trst_n    (jtag_trst_n),
    .jtag_srst_n    ()
);
`endif

/* verilator lint_off CASEINCOMPLETE */
`include "dasm.svi"
/* verilator lint_on CASEINCOMPLETE */

endmodule
