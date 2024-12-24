// SPDX-License-Identifier: Apache-2.0
// Copyright 2020 Western Digital Corporation or its affiliates.
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
// Owner:
// Function: AHB to AXI4 Bridge
// Comments:
//
//********************************************************************************
module ahb_to_axi4
import el2_pkg::*;
#(
   TAG = 1,
   CHECK_RANGES = 1,
   `include "el2_param.vh"
)
(
   input                   clk,
   input                   rst_l,
   /* pragma coverage off */
   input                   scan_mode,
   /* pragma coverage on */
   input                   bus_clk_en,
   input                   clk_override,

   // AXI signals
   // AXI Write Channels
   output logic            axi_awvalid,
   input  logic            axi_awready,
   /* exclude signals that are tied to constant value in this file */
   /*pragma coverage off*/
   output logic [TAG-1:0]  axi_awid,
   /*pragma coverage on*/
   output logic [31:0]     axi_awaddr,
   output logic [2:0]      axi_awsize,
   /* exclude signals that are tied to constant value in this file */
   /*pragma coverage off*/
   output logic [2:0]      axi_awprot,
   output logic [7:0]      axi_awlen,
   output logic [1:0]      axi_awburst,
   /*pragma coverage on*/

   output logic            axi_wvalid,
   input  logic            axi_wready,
   output logic [63:0]     axi_wdata,
   output logic [7:0]      axi_wstrb,
   /* exclude signals that are tied to constant value in this file */
   /*pragma coverage off*/
   output logic            axi_wlast,
   /*pragma coverage on*/

   input  logic            axi_bvalid,
   /* exclude signals that are tied to constant value in this file */
   /*pragma coverage off*/
   output logic            axi_bready,
   /*pragma coverage on*/
   input  logic [1:0]      axi_bresp,
   /* Exclude unused AXI rid since it has no equivalent in AHB */
   /*pragma coverage off*/
   input  logic [TAG-1:0]  axi_bid,
   /*pragma coverage on*/

   // AXI Read Channels
   output logic            axi_arvalid,
   input  logic            axi_arready,
   /* exclude signals that are tied to constant value in this file */
   /*pragma coverage off*/
   output logic [TAG-1:0]  axi_arid,
   /*pragma coverage on*/
   output logic [31:0]     axi_araddr,
   output logic [2:0]      axi_arsize,
   /* exclude signals that are tied to constant value in this file */
   /*pragma coverage off*/
   output logic [2:0]      axi_arprot,
   output logic [7:0]      axi_arlen,
   output logic [1:0]      axi_arburst,
   /*pragma coverage on*/

   input  logic            axi_rvalid,
   /* exclude signals that are tied to constant value in this file */
   /*pragma coverage off*/
   output logic            axi_rready,
   /*pragma coverage on*/
   /* Exclude unused AXI rid since it has no equivalent in AHB */
   /*pragma coverage off*/
   input  logic [TAG-1:0]  axi_rid,
   /*pragma coverage on*/
   input  logic [63:0]     axi_rdata,
   input  logic [1:0]      axi_rresp,

   // AHB-Lite signals
   input logic [31:0]      ahb_haddr,     // ahb bus address
   // Exclude input signals that are unused in this file (their AXI equivalents
   // are tied to constants)
   /*pragma coverage off*/
   input logic [2:0]       ahb_hburst,    // tied to 0
   input logic             ahb_hmastlock, // tied to 0
   input logic [3:0]       ahb_hprot,     // tied to 4'b0011
   /*pragma coverage on*/
   input logic [2:0]       ahb_hsize,     // size of bus transaction (possible values 0,1,2,3)
   input logic [1:0]       ahb_htrans,    // Transaction type (possible values 0,2 only right now)
   input logic             ahb_hwrite,    // ahb bus write
   input logic [63:0]      ahb_hwdata,    // ahb bus write data
   input logic             ahb_hsel,      // this slave was selected
   input logic             ahb_hreadyin,  // previous hready was accepted or not

   output logic [63:0]      ahb_hrdata,      // ahb bus read data
   output logic             ahb_hreadyout,   // slave ready to accept transaction
   output logic             ahb_hresp        // slave response (high indicates erro)

);

   logic [7:0]       master_wstrb;

 typedef enum logic [1:0] {   IDLE   = 2'b00,    // Nothing in the buffer. No commands yet recieved
                              WR     = 2'b01,    // Write Command recieved
                              RD     = 2'b10,    // Read Command recieved
                              PEND   = 2'b11     // Waiting on Read Data from core
                            } state_t;
   state_t      buf_state, buf_nxtstate;
   logic        buf_state_en;

   // Buffer signals (one entry buffer)
   logic                    buf_read_error_in, buf_read_error;
   logic [63:0]             buf_rdata;

   logic                    ahb_hready;
   logic                    ahb_hready_q;
   logic [1:0]              ahb_htrans_in, ahb_htrans_q;
   logic [2:0]              ahb_hsize_q;
   logic                    ahb_hwrite_q;
   logic [31:0]             ahb_haddr_q;
   logic                    ahb_hresp_q;

   // signals needed for the read data coming back from the core and to block any further commands as AHB is a blocking bus
   logic                    buf_rdata_en;

   logic                    ahb_addr_clk_en, buf_rdata_clk_en;
   logic                    bus_clk, ahb_addr_clk, buf_rdata_clk;
   // Command buffer is the holding station where we convert to AXI and send to core
   logic                    cmdbuf_wr_en, cmdbuf_rst;
   logic                    cmdbuf_full;
   logic                    cmdbuf_vld, cmdbuf_write;
   logic [1:0]              cmdbuf_size;
   logic [7:0]              cmdbuf_wstrb;
   logic [31:0]             cmdbuf_addr;
   logic [63:0]             cmdbuf_wdata;

// FSM to control the bus states and when to block the hready and load the command buffer
   always_comb begin
      buf_nxtstate      = IDLE;
      buf_state_en      = 1'b0;
      buf_rdata_en      = 1'b0;              // signal to load the buffer when the core sends read data back
      buf_read_error_in = 1'b0;              // signal indicating that an error came back with the read from the core
      cmdbuf_wr_en      = 1'b0;              // all clear from the gasket to load the buffer with the command for reads, command/dat for writes
      case (buf_state)
         IDLE: begin  // No commands recieved
                  buf_nxtstate      = ahb_hwrite ? WR : RD;
                  buf_state_en      = ahb_hready & ahb_htrans[1] & ahb_hsel;                 // only transition on a valid hrtans
          end
         WR: begin // Write command recieved last cycle
                  buf_nxtstate      = (ahb_hresp | (ahb_htrans[1:0] == 2'b0) | ~ahb_hsel) ? IDLE : ahb_hwrite  ? WR : RD;
                  buf_state_en      = (~cmdbuf_full | ahb_hresp) ;
                  cmdbuf_wr_en      = ~cmdbuf_full & ~(ahb_hresp | ((ahb_htrans[1:0] == 2'b01) & ahb_hsel));   // Dont send command to the buffer in case of an error or when the master is not ready with the data now.
         end
         RD: begin // Read command recieved last cycle.
                 buf_nxtstate      = ahb_hresp ? IDLE :PEND;                                       // If error go to idle, else wait for read data
                 buf_state_en      = (~cmdbuf_full | ahb_hresp);                                   // only when command can go, or if its an error
                 cmdbuf_wr_en      = ~ahb_hresp & ~cmdbuf_full;                                    // send command only when no error
         end
         PEND: begin // Read Command has been sent. Waiting on Data.
                 buf_nxtstate      = IDLE;                                                          // go back for next command and present data next cycle
                 buf_state_en      = axi_rvalid & ~cmdbuf_write;                                    // read data is back
                 buf_rdata_en      = buf_state_en;                                                  // buffer the read data coming back from core
                 buf_read_error_in = buf_state_en & |axi_rresp[1:0];                                // buffer error flag if return has Error ( ECC )
         end
     endcase
   end // always_comb begin

    rvdffs_fpga #($bits(state_t)) state_reg (.*, .din(buf_nxtstate), .dout({buf_state}), .en(buf_state_en), .clk(bus_clk), .clken(bus_clk_en), .rawclk(clk));

   assign master_wstrb[7:0]   = ({8{ahb_hsize_q[2:0] == 3'b0}}  & (8'b1    << ahb_haddr_q[2:0])) |
                                ({8{ahb_hsize_q[2:0] == 3'b1}}  & (8'b11   << ahb_haddr_q[2:0])) |
                                ({8{ahb_hsize_q[2:0] == 3'b10}} & (8'b1111 << ahb_haddr_q[2:0])) |
                                ({8{ahb_hsize_q[2:0] == 3'b11}} & 8'b1111_1111);

   // AHB signals
   assign ahb_hreadyout       = ahb_hresp ? (ahb_hresp_q & ~ahb_hready_q) :
                                         ((~cmdbuf_full | (buf_state == IDLE)) & ~(buf_state == RD | buf_state == PEND)  & ~buf_read_error);

   assign ahb_hready          = ahb_hreadyout & ahb_hreadyin;
   assign ahb_htrans_in[1:0]  = {2{ahb_hsel}} & ahb_htrans[1:0];
   assign ahb_hrdata[63:0]    = buf_rdata[63:0];

   if (CHECK_RANGES) begin
       // Miscellaneous signals
       logic                    ahb_addr_in_dccm, ahb_addr_in_iccm, ahb_addr_in_pic;
       logic                    ahb_addr_in_dccm_region_nc, ahb_addr_in_iccm_region_nc, ahb_addr_in_pic_region_nc;

       assign ahb_hresp    = ((ahb_htrans_q[1:0] != 2'b0) & (buf_state != IDLE)  &
                             ((~(ahb_addr_in_dccm | ahb_addr_in_iccm)) |                                                                                   // request not for ICCM or DCCM
                             ((ahb_addr_in_iccm | (ahb_addr_in_dccm &  ahb_hwrite_q)) & ~((ahb_hsize_q[1:0] == 2'b10) | (ahb_hsize_q[1:0] == 2'b11))) |    // ICCM Rd/Wr OR DCCM Wr not the right size
                             ((ahb_hsize_q[2:0] == 3'h1) & ahb_haddr_q[0])   |                                                                             // HW size but unaligned
                             ((ahb_hsize_q[2:0] == 3'h2) & (|ahb_haddr_q[1:0])) |                                                                          // W size but unaligned
                             ((ahb_hsize_q[2:0] == 3'h3) & (|ahb_haddr_q[2:0])))) |                                                                        // DW size but unaligned
                             buf_read_error |                                                                                                              // Read ECC error
                             (ahb_hresp_q & ~ahb_hready_q);

       // Address check  dccm
       rvrangecheck #(.CCM_SADR(pt.DCCM_SADR),
                      .CCM_SIZE(pt.DCCM_SIZE)) addr_dccm_rangecheck (
          .addr(ahb_haddr_q[31:0]),
          .in_range(ahb_addr_in_dccm),
          .in_region(ahb_addr_in_dccm_region_nc)
       );

      // Address check  iccm
      if (pt.ICCM_ENABLE == 1) begin: GenICCM
         rvrangecheck #(.CCM_SADR(pt.ICCM_SADR),
                        .CCM_SIZE(pt.ICCM_SIZE)) addr_iccm_rangecheck (
            .addr(ahb_haddr_q[31:0]),
            .in_range(ahb_addr_in_iccm),
            .in_region(ahb_addr_in_iccm_region_nc)
         );
      end else begin: GenNoICCM
         assign ahb_addr_in_iccm = '0;
         assign ahb_addr_in_iccm_region_nc = '0;
      end

      // PIC memory address check
      rvrangecheck #(.CCM_SADR(pt.PIC_BASE_ADDR),
                     .CCM_SIZE(pt.PIC_SIZE)) addr_pic_rangecheck (
         .addr(ahb_haddr_q[31:0]),
         .in_range(ahb_addr_in_pic),
         .in_region(ahb_addr_in_pic_region_nc)
      );
   end else begin // !CHECK_RANGES
       assign ahb_hresp    = ((ahb_htrans_q[1:0] != 2'b0) & (buf_state != IDLE)  &
                             (((ahb_hsize_q[2:0] == 3'h1) & ahb_haddr_q[0]) |       // HW size but unaligned
                             ((ahb_hsize_q[2:0] == 3'h2) & (|ahb_haddr_q[1:0])) |   // W size but unaligned
                             ((ahb_hsize_q[2:0] == 3'h3) & (|ahb_haddr_q[2:0])))) | // DW size but unaligned
                             buf_read_error |                                       // Read ECC error
                             (ahb_hresp_q & ~ahb_hready_q);
   end // CHECK_RANGES

   // Buffer signals - needed for the read data and ECC error response
   rvdff_fpga  #(.WIDTH(64)) buf_rdata_ff     (.din(axi_rdata[63:0]),   .dout(buf_rdata[63:0]), .clk(buf_rdata_clk), .clken(buf_rdata_clk_en), .rawclk(clk), .*);
   rvdff_fpga  #(.WIDTH(1))  buf_read_error_ff(.din(buf_read_error_in), .dout(buf_read_error),  .clk(bus_clk),       .clken(bus_clk_en),       .rawclk(clk), .*);          // buf_read_error will be high only one cycle

   // All the Master signals are captured before presenting it to the command buffer. We check for Hresp before sending it to the cmd buffer.
   rvdff_fpga #(.WIDTH(1))  hresp_ff  (.din(ahb_hresp),          .dout(ahb_hresp_q),       .clk(bus_clk),      .clken(bus_clk_en),      .rawclk(clk), .*);
   rvdff_fpga #(.WIDTH(1))  hready_ff (.din(ahb_hready),         .dout(ahb_hready_q),      .clk(bus_clk),      .clken(bus_clk_en),      .rawclk(clk), .*);
   rvdff_fpga #(.WIDTH(2))  htrans_ff (.din(ahb_htrans_in[1:0]), .dout(ahb_htrans_q[1:0]), .clk(bus_clk),      .clken(bus_clk_en),      .rawclk(clk), .*);
   rvdff_fpga #(.WIDTH(3))  hsize_ff  (.din(ahb_hsize[2:0]),     .dout(ahb_hsize_q[2:0]),  .clk(ahb_addr_clk), .clken(ahb_addr_clk_en), .rawclk(clk), .*);
   rvdff_fpga #(.WIDTH(1))  hwrite_ff (.din(ahb_hwrite),         .dout(ahb_hwrite_q),      .clk(ahb_addr_clk), .clken(ahb_addr_clk_en), .rawclk(clk), .*);
   rvdff_fpga #(.WIDTH(32)) haddr_ff  (.din(ahb_haddr[31:0]),    .dout(ahb_haddr_q[31:0]), .clk(ahb_addr_clk), .clken(ahb_addr_clk_en), .rawclk(clk), .*);

   // Command Buffer - Holding for the commands to be sent for the AXI. It will be converted to the AXI signals.
   assign cmdbuf_rst         = (((axi_awvalid & axi_awready) | (axi_arvalid & axi_arready)) & ~cmdbuf_wr_en) | (ahb_hresp & ~cmdbuf_write);
   assign cmdbuf_full        = (cmdbuf_vld & ~((axi_awvalid & axi_awready) | (axi_arvalid & axi_arready)));

   rvdffsc_fpga #(.WIDTH(1))  cmdbuf_vldff      (.din(1'b1),              .dout(cmdbuf_vld),         .en(cmdbuf_wr_en), .clear(cmdbuf_rst), .clk(bus_clk), .clken(bus_clk_en), .rawclk(clk), .*);
   rvdffs_fpga  #(.WIDTH(1))  cmdbuf_writeff    (.din(ahb_hwrite_q),      .dout(cmdbuf_write),       .en(cmdbuf_wr_en),                     .clk(bus_clk), .clken(bus_clk_en), .rawclk(clk), .*);
   rvdffs_fpga  #(.WIDTH(2))  cmdbuf_sizeff     (.din(ahb_hsize_q[1:0]),  .dout(cmdbuf_size[1:0]),   .en(cmdbuf_wr_en),                     .clk(bus_clk), .clken(bus_clk_en), .rawclk(clk), .*);
   rvdffs_fpga  #(.WIDTH(8))  cmdbuf_wstrbff    (.din(master_wstrb[7:0]), .dout(cmdbuf_wstrb[7:0]),  .en(cmdbuf_wr_en),                     .clk(bus_clk), .clken(bus_clk_en), .rawclk(clk), .*);
   rvdffe       #(.WIDTH(32)) cmdbuf_addrff     (.din(ahb_haddr_q[31:0]), .dout(cmdbuf_addr[31:0]),  .en(cmdbuf_wr_en & bus_clk_en),        .clk(clk), .*);
   rvdffe       #(.WIDTH(64)) cmdbuf_wdataff    (.din(ahb_hwdata[63:0]),  .dout(cmdbuf_wdata[63:0]), .en(cmdbuf_wr_en & bus_clk_en),        .clk(clk), .*);

   // AXI Write Command Channel
   assign axi_awvalid           = cmdbuf_vld & cmdbuf_write;
   assign axi_awid[TAG-1:0]     = '0;
   assign axi_awaddr[31:0]      = cmdbuf_addr[31:0];
   assign axi_awsize[2:0]       = {1'b0, cmdbuf_size[1:0]};
   assign axi_awprot[2:0]       = 3'b0;
   assign axi_awlen[7:0]        = '0;
   assign axi_awburst[1:0]      = 2'b01;
   // AXI Write Data Channel - This is tied to the command channel as we only write the command buffer once we have the data.
   assign axi_wvalid            = cmdbuf_vld & cmdbuf_write;
   assign axi_wdata[63:0]       = cmdbuf_wdata[63:0];
   assign axi_wstrb[7:0]        = cmdbuf_wstrb[7:0];
   assign axi_wlast             = 1'b1;
  // AXI Write Response - Always ready. AHB does not require a write response.
   assign axi_bready            = 1'b1;
   // AXI Read Channels
   assign axi_arvalid           = cmdbuf_vld & ~cmdbuf_write;
   assign axi_arid[TAG-1:0]     = '0;
   assign axi_araddr[31:0]      = cmdbuf_addr[31:0];
   assign axi_arsize[2:0]       = {1'b0, cmdbuf_size[1:0]};
   assign axi_arprot            = 3'b0;
   assign axi_arlen[7:0]        = '0;
   assign axi_arburst[1:0]      = 2'b01;
   // AXI Read Response Channel - Always ready as AHB reads are blocking and the the buffer is available for the read coming back always.
   assign axi_rready            = 1'b1;

   // Clock header logic
   assign ahb_addr_clk_en = bus_clk_en & (ahb_hready & ahb_htrans[1]);
   assign buf_rdata_clk_en    = bus_clk_en & buf_rdata_en;

`ifdef RV_FPGA_OPTIMIZE
   assign bus_clk = 1'b0;
   assign ahb_addr_clk = 1'b0;
   assign buf_rdata_clk = 1'b0;
`else
   rvclkhdr bus_cgc       (.en(bus_clk_en),       .l1clk(bus_clk),       .*);
   rvclkhdr ahb_addr_cgc  (.en(ahb_addr_clk_en),  .l1clk(ahb_addr_clk),  .*);
   rvclkhdr buf_rdata_cgc (.en(buf_rdata_clk_en), .l1clk(buf_rdata_clk), .*);
`endif

`ifdef RV_ASSERT_ON
   property ahb_error_protocol;
      @(posedge bus_clk) (ahb_hready & ahb_hresp) |-> (~$past(ahb_hready) & $past(ahb_hresp));
   endproperty
   assert_ahb_error_protocol: assert property (ahb_error_protocol) else
      $display("Bus Error with hReady isn't preceded with Bus Error without hready");

`endif

endmodule // ahb_to_axi4
