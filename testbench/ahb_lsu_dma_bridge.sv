// SPDX-License-Identifier: Apache-2.0
// Copyright 2024 Antmicro <www.antmicro.com>
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

// connects LSU master (AHB) to external AXI slave and DMA slave (AHB)
module ahb_lsu_dma_bridge
#(
  TAG = 1,
  `include "el2_param.vh"
)
(
    input                   clk,
    input                   reset_l,

    // AHB master interface (LSU)
    input logic [2:0]       m_ahb_hburst,    // tied to 0
    input logic             m_ahb_hmastlock, // tied to 0
    input logic [3:0]       m_ahb_hprot,     // tied to 4'b0011
    input logic [31:0]      m_ahb_haddr,     // ahb bus address
    input logic [2:0]       m_ahb_hsize,     // size of bus transaction (possible values 0,1,2,3)
    input logic [1:0]       m_ahb_htrans,    // Transaction type (possible values 0,2 only right now)
    input logic             m_ahb_hwrite,    // ahb bus write
    input logic [63:0]      m_ahb_hwdata,    // ahb bus write data
    input logic             m_ahb_hsel,      // this slave was selected
    input logic             m_ahb_hreadyin,  // previous hready was accepted or not
    output logic [63:0]     m_ahb_hrdata,    // ahb bus read data
    output logic            m_ahb_hreadyout, // slave ready to accept transaction
    output logic            m_ahb_hresp,     // slave response (high indicates erro)

    // AXI slave interface (lmem)
    // AXI Write Channels
    output logic            s0_axi_awvalid,
    input  logic            s0_axi_awready,
    output logic [TAG-1:0]  s0_axi_awid,
    output logic [31:0]     s0_axi_awaddr,
    output logic [2:0]      s0_axi_awsize,

    output logic            s0_axi_wvalid,
    input  logic            s0_axi_wready,
    output logic [63:0]     s0_axi_wdata,
    output logic [7:0]      s0_axi_wstrb,

    input  logic            s0_axi_bvalid,
    output logic            s0_axi_bready,
    input  logic [1:0]      s0_axi_bresp,
    input  logic [TAG-1:0]  s0_axi_bid,
    // AXI Read Channels
    output logic            s0_axi_arvalid,
    input  logic            s0_axi_arready,
    output logic [TAG-1:0]  s0_axi_arid,
    output logic [31:0]     s0_axi_araddr,
    output logic [2:0]      s0_axi_arsize,

    input  logic            s0_axi_rvalid,
    output logic            s0_axi_rready,
    input  logic [TAG-1:0]  s0_axi_rid,
    input  logic [63:0]     s0_axi_rdata,
    input  logic [1:0]      s0_axi_rresp,
    input  logic            s0_axi_rlast,

    // AHB slave interface (dma)
    output logic [31:0]     s1_ahb_haddr,       // ahb bus address
    output logic [2:0]      s1_ahb_hburst,      // tied to 0
    output logic            s1_ahb_hmastlock,   // tied to 0
    output logic [3:0]      s1_ahb_hprot,       // [3:1] are tied to 3'b001
    output logic [2:0]      s1_ahb_hsize,       // size of bus transaction (possible values 0,1,2,3)
    output logic [1:0]      s1_ahb_htrans,      // Transaction type (possible values 0,2 only right now)
    output logic            s1_ahb_hwrite,      // ahb bus write
    output logic [63:0]     s1_ahb_hwdata,      // ahb bus write data
    input logic  [63:0]     s1_ahb_hrdata,      // ahb bus read data
    input logic             s1_ahb_hready,      // connect to veer's dma_hreadyout
    input logic             s1_ahb_hresp        // slave response (high indicates erro)
);

    // AXI signals for the M interface converted from AHB to AXI
    logic            m_axi_awvalid;
    logic            m_axi_awready;
    logic [TAG-1:0]  m_axi_awid;
    logic [31:0]     m_axi_awaddr;
    logic [2:0]      m_axi_awsize;
    logic [2:0]      m_axi_awprot;
    logic [7:0]      m_axi_awlen;
    logic [1:0]      m_axi_awburst;

    logic            m_axi_wvalid;
    logic            m_axi_wready;
    logic [63:0]     m_axi_wdata;
    logic [7:0]      m_axi_wstrb;
    logic            m_axi_wlast;

    logic            m_axi_bvalid;
    logic            m_axi_bready;
    logic [1:0]      m_axi_bresp;
    logic [TAG-1:0]  m_axi_bid;

    // AXI Read Channels
    logic            m_axi_arvalid;
    logic            m_axi_arready;
    logic [TAG-1:0]  m_axi_arid;
    logic [31:0]     m_axi_araddr;
    logic [2:0]      m_axi_arsize;
    logic [2:0]      m_axi_arprot;
    logic [7:0]      m_axi_arlen;
    logic [1:0]      m_axi_arburst;

    logic            m_axi_rvalid;
    logic            m_axi_rready;
    logic [TAG-1:0]  m_axi_rid;
    logic [63:0]     m_axi_rdata;
    logic [1:0]      m_axi_rresp;
    logic            m_axi_rlast;

    // AXI signals for the S1 interface converted from AXI to AHB
    logic            s1_axi_awvalid;
    logic            s1_axi_awready;
    logic            s1_axi_wvalid;
    logic            s1_axi_wready;
    logic            s1_axi_bvalid;
    logic            s1_axi_bready;
    logic [1:0]      s1_axi_bresp;
    logic            s1_axi_arvalid;
    logic            s1_axi_arready;
    logic            s1_axi_rvalid;
    logic            s1_axi_rready;
    logic [63:0]     s1_axi_rdata;
    logic [1:0]      s1_axi_rresp;
    logic            s1_axi_rlast;

    // These signals are not contolled by the bridge, assign them here.
    assign s0_axi_awid = m_axi_awid;
    assign s0_axi_awaddr = m_axi_awaddr;
    assign s0_axi_awsize = m_axi_awsize;
    assign s0_axi_wdata = m_axi_wdata;
    assign s0_axi_wstrb = m_axi_wstrb;
    assign s0_axi_arid = m_axi_arid;
    assign s0_axi_araddr = m_axi_araddr;
    assign s0_axi_arsize = m_axi_arsize;

    ahb_to_axi4 #(.pt(pt), .CHECK_RANGES(0)) m_ahb_to_axi (
        .clk(clk),
        .rst_l(reset_l),
        .scan_mode('0),
        .bus_clk_en(1'b1),
        .clk_override('0),

        // AXI Write Channels
        .axi_awvalid(m_axi_awvalid),
        .axi_awready(m_axi_awready),
        .axi_awid(m_axi_awid[TAG-1:0]),
        .axi_awaddr(m_axi_awaddr[31:0]),
        .axi_awsize(m_axi_awsize[2:0]),
        .axi_awprot(m_axi_awprot[2:0]),
        .axi_awlen(m_axi_awlen),
        .axi_awburst(m_axi_awburst),

        .axi_wvalid(m_axi_wvalid),
        .axi_wready(m_axi_wready),
        .axi_wdata(m_axi_wdata[63:0]),
        .axi_wstrb(m_axi_wstrb[7:0]),
        .axi_wlast(m_axi_wlast),

        .axi_bvalid(m_axi_bvalid),
        .axi_bready(m_axi_bready),
        .axi_bresp(m_axi_bresp[1:0]),
        .axi_bid(m_axi_bid[TAG-1:0]),

        // AXI Read Channels
        .axi_arvalid(m_axi_arvalid),
        .axi_arready(m_axi_arready),
        .axi_arid(m_axi_arid[TAG-1:0]),
        .axi_araddr(m_axi_araddr[31:0]),
        .axi_arsize(m_axi_arsize[2:0]),
        .axi_arprot(m_axi_arprot[2:0]),
        .axi_arlen(m_axi_arlen),
        .axi_arburst(m_axi_arburst),

        .axi_rvalid(m_axi_rvalid),
        .axi_rready(m_axi_rready),
        .axi_rid(m_axi_rid[TAG-1:0]),
        .axi_rdata(m_axi_rdata[63:0]),
        .axi_rresp(m_axi_rresp[1:0]),

        // AHB-LITE signals
        // connect lsu master here
        .ahb_haddr(m_ahb_haddr[31:0]),
        .ahb_hburst(m_ahb_hburst),
        .ahb_hmastlock(m_ahb_hmastlock),
        .ahb_hprot(m_ahb_hprot[3:0]),
        .ahb_hsize(m_ahb_hsize[2:0]),
        .ahb_htrans(m_ahb_htrans[1:0]),
        .ahb_hwrite(m_ahb_hwrite),
        .ahb_hwdata(m_ahb_hwdata[63:0]),
        .ahb_hsel('1),
        .ahb_hreadyin('1),
        .ahb_hrdata(m_ahb_hrdata[63:0]),
        .ahb_hreadyout(m_ahb_hreadyout), // TODO
        .ahb_hresp(m_ahb_hresp)
    );

    axi4_to_ahb #(.pt(pt)) s1_axi4_to_ahb (
        .clk(clk),
        .free_clk(clk),
        .rst_l(reset_l),
        .scan_mode('0),
        .bus_clk_en('1),
        .clk_override('0),
        .dec_tlu_force_halt('0),

        // AXI Write Channels
        .axi_awvalid(s1_axi_awvalid),
        .axi_awready(s1_axi_awready),
        .axi_awid(m_axi_awid),
        .axi_awaddr(m_axi_awaddr[31:0]),
        .axi_awsize(m_axi_awsize[2:0]),
        .axi_awprot(m_axi_awprot[2:0]),
        .axi_wvalid(s1_axi_wvalid),
        .axi_wready(s1_axi_wready),
        .axi_wdata(m_axi_wdata[63:0]),
        .axi_wstrb(m_axi_wstrb[7:0]),
        .axi_wlast(m_axi_wlast),
        .axi_bvalid(s1_axi_bvalid),
        .axi_bready(s1_axi_bready),
        .axi_bresp(s1_axi_bresp[1:0]),
        .axi_bid(), // axi_lsu_dma_bridge doesn't have such port

        // AXI Read Channels
        .axi_arvalid(s1_axi_arvalid),
        .axi_arready(s1_axi_arready),
        .axi_arid(), // axi_lsu_dma_bridge doesn't use such port
        .axi_araddr(m_axi_araddr[31:0]),
        .axi_arsize(m_axi_arsize[2:0]),
        .axi_arprot(m_axi_arprot[2:0]),
        .axi_rvalid(s1_axi_rvalid),
        .axi_rready(s1_axi_rready),
        .axi_rid(), // axi_lsu_dma_bridge doesn't have such port
        .axi_rdata(s1_axi_rdata[63:0]),
        .axi_rresp(s1_axi_rresp[1:0]),
        .axi_rlast(s1_axi_rlast),

        // AHB signals
        // connect s1 here
        .ahb_haddr(s1_ahb_haddr),
        .ahb_hburst(s1_ahb_hburst),
        .ahb_hmastlock(s1_ahb_hmastlock),
        .ahb_hprot(s1_ahb_hprot),
        .ahb_hsize(s1_ahb_hsize),
        .ahb_htrans(s1_ahb_htrans),
        .ahb_hwrite(s1_ahb_hwrite),
        .ahb_hwdata(s1_ahb_hwdata),
        .ahb_hrdata(s1_ahb_hrdata),
        .ahb_hready(s1_ahb_hready),
        .ahb_hresp(s1_ahb_hresp)
    );

    // This is the actual bridge, implemented for AXI only.
    axi_lsu_dma_bridge # (TAG, TAG) bridge(
        .clk(clk),
        .reset_l(reset_l),

        // master read bus
        .m_arvalid(m_axi_arvalid),
        .m_arid(m_axi_arid),
        .m_araddr(m_axi_araddr),
        .m_arready(m_axi_arready),

        .m_rvalid(m_axi_rvalid),
        .m_rready(m_axi_rready),
        .m_rdata(m_axi_rdata),
        .m_rid(m_axi_rid),
        .m_rresp(m_axi_rresp),
        .m_rlast(m_axi_rlast),

        // master write bus
        .m_awvalid(m_axi_awvalid),
        .m_awid(m_axi_awid),
        .m_awaddr(m_axi_awaddr),
        .m_awready(m_axi_awready),

        .m_wvalid(m_axi_wvalid),
        .m_wready(m_axi_wready),

        .m_bresp(m_axi_bresp),
        .m_bvalid(m_axi_bvalid),
        .m_bid(m_axi_bid),
        .m_bready(m_axi_bready),

        // lmem
        .s0_arvalid(s0_axi_arvalid),
        .s0_arready(s0_axi_arready),

        .s0_rvalid(s0_axi_rvalid),
        .s0_rid(s0_axi_rid),
        .s0_rresp(s0_axi_rresp),
        .s0_rdata(s0_axi_rdata),
        .s0_rlast(s0_axi_rlast),
        .s0_rready(s0_axi_rready),

        .s0_awvalid(s0_axi_awvalid),
        .s0_awready(s0_axi_awready),

        .s0_wvalid(s0_axi_wvalid),
        .s0_wready(s0_axi_wready),

        .s0_bresp(s0_axi_bresp),
        .s0_bvalid(s0_axi_bvalid),
        .s0_bid(s0_axi_bid),
        .s0_bready(s0_axi_bready),

        // dma
        .s1_arvalid(s1_axi_arvalid),
        .s1_arready(s1_axi_arready),

        .s1_rvalid(s1_axi_rvalid),
        .s1_rresp(s1_axi_rresp),
        .s1_rdata(s1_axi_rdata),
        .s1_rlast(s1_axi_rlast),
        .s1_rready(s1_axi_rready),

        .s1_awvalid(s1_axi_awvalid),
        .s1_awready(s1_axi_awready),

        .s1_wvalid(s1_axi_wvalid),
        .s1_wready(s1_axi_wready),

        .s1_bresp(s1_axi_bresp),
        .s1_bvalid(s1_axi_bvalid),
        .s1_bready(s1_axi_bready)
    );

endmodule
