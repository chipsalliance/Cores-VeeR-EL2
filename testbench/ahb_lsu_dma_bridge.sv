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
    input logic [31:0]      m_ahb_haddr,     // ahb bus address
    input logic [2:0]       m_ahb_hburst,    // tied to 0
    input logic             m_ahb_hmastlock, // tied to 0
    input logic [3:0]       m_ahb_hprot,     // tied to 4'b0011
    input logic [2:0]       m_ahb_hsize,     // size of bus transaction (possible values 0,1,2,3)
    input logic [1:0]       m_ahb_htrans,    // Transaction type (possible values 0,2 only right now)
    input logic             m_ahb_hwrite,    // ahb bus write
    input logic [63:0]      m_ahb_hwdata,    // ahb bus write data
    input logic             m_ahb_hsel,      // this slave was selected
    input logic             m_ahb_hreadyin,  // previous hready was accepted or not
    output logic [63:0]     m_ahb_hrdata,    // ahb bus read data
    output logic            m_ahb_hreadyout, // slave ready to accept transaction
    output logic            m_ahb_hresp,     // slave response (high indicates erro)

    // AHB slave interface (lmem)
    output logic            s0_ahb_hsel,        // ahb bus slave select
    output logic [31:0]     s0_ahb_haddr,       // ahb bus address
    output logic [2:0]      s0_ahb_hburst,      // tied to 0
    output logic            s0_ahb_hmastlock,   // tied to 0
    output logic [3:0]      s0_ahb_hprot,       // [3:1] are tied to 3'b001
    output logic [2:0]      s0_ahb_hsize,       // size of bus transaction (possible values 0,1,2,3)
    output logic [1:0]      s0_ahb_htrans,      // Transaction type (possible values 0,2 only right now)
    output logic            s0_ahb_hwrite,      // ahb bus write
    output logic [63:0]     s0_ahb_hwdata,      // ahb bus write data
    input logic  [63:0]     s0_ahb_hrdata,      // ahb bus read data
    input logic             s0_ahb_hready,      // connect to veer's dma_hreadyout
    input logic             s0_ahb_hresp,       // slave response (high indicates erro)

    // AHB slave interface (dma)
    output logic            s1_ahb_hsel,        // ahb bus slave select
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

parameter ICCM_BASE = `RV_ICCM_BITS; // in LSBs
bit[31:0] iccm_real_base_addr = `RV_ICCM_SADR ;

wire bus_active;
wire slave_select;

reg slave_select_dly;

assign bus_active = m_ahb_htrans inside {2'b10, 2'b11};
assign slave_select = m_ahb_haddr[31:ICCM_BASE] == iccm_real_base_addr[31:ICCM_BASE];

assign s0_ahb_hsel = bus_active & ~slave_select;
assign s0_ahb_haddr = m_ahb_haddr;
assign s0_ahb_hburst = m_ahb_hburst;
assign s0_ahb_hmastlock = m_ahb_hmastlock;
assign s0_ahb_hprot  = m_ahb_hprot;
assign s0_ahb_hsize  = m_ahb_hsize;
assign s0_ahb_htrans = m_ahb_htrans;
assign s0_ahb_hwrite = m_ahb_hwrite;
assign s0_ahb_hwdata = m_ahb_hwdata;

assign s1_ahb_hsel = bus_active & slave_select;
assign s1_ahb_haddr = m_ahb_haddr;
assign s1_ahb_hburst = m_ahb_hburst;
assign s1_ahb_hmastlock = m_ahb_hmastlock;
assign s1_ahb_hprot  = m_ahb_hprot;
assign s1_ahb_hsize  = m_ahb_hsize;
assign s1_ahb_htrans = m_ahb_htrans;
assign s1_ahb_hwrite = m_ahb_hwrite;
assign s1_ahb_hwdata = m_ahb_hwdata;

assign m_ahb_hreadyout = &{s0_ahb_hready, s1_ahb_hready};
assign m_ahb_hrdata = slave_select_dly ? s1_ahb_hrdata : s0_ahb_hrdata;
assign m_ahb_hresp  = slave_select_dly ? s1_ahb_hresp : s0_ahb_hresp;

always_ff @(posedge clk or negedge reset_l) begin
  if(~reset_l) slave_select_dly <= 1'b0;
  else slave_select_dly <= slave_select;
end

endmodule
