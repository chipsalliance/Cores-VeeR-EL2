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
//
// Owner:
// Function: DCCM for LSU pipe
// Comments: Single ported memory
//
//
// DC1 -> DC2 -> DC3 -> DC4 (Commit)
//
// //********************************************************************************

module el2_lsu_dccm_mem
  import el2_pkg::*;
#(
`include "el2_param.vh"
 )(
   input logic         clk,                                             // Clock only while core active.  Through one clock header.  For flops with    second clock header built in.  Connected to ACTIVE_L2CLK.
   input logic         active_clk,                                      // Clock only while core active.  Through two clock headers. For flops without second clock header built in.
   input logic         rst_l,                                           // reset, active low
   input logic         clk_override,                                    // Override non-functional clock gating

   input logic         dccm_wren,                                       // write enable
   input logic         dccm_rden,                                       // read enable
   input logic [pt.DCCM_BITS-1:0]  dccm_wr_addr_lo,                     // write address
   input logic [pt.DCCM_BITS-1:0]  dccm_wr_addr_hi,                     // write address
   input logic [pt.DCCM_BITS-1:0]  dccm_rd_addr_lo,                     // read address
   input logic [pt.DCCM_BITS-1:0]  dccm_rd_addr_hi,                     // read address for the upper bank in case of a misaligned access
   input logic [pt.DCCM_FDATA_WIDTH-1:0]  dccm_wr_data_lo,              // write data
   input logic [pt.DCCM_FDATA_WIDTH-1:0]  dccm_wr_data_hi,              // write data
   el2_mem_if.veer_dccm                   dccm_mem_export,              // RAM repositioned in testbench and connected by this interface

   output logic [pt.DCCM_FDATA_WIDTH-1:0] dccm_rd_data_lo,              // read data from the lo bank
   output logic [pt.DCCM_FDATA_WIDTH-1:0] dccm_rd_data_hi,              // read data from the hi bank

   input  logic         scan_mode
);


   localparam DCCM_WIDTH_BITS = $clog2(pt.DCCM_BYTE_WIDTH);
   localparam DCCM_INDEX_BITS = (pt.DCCM_BITS - pt.DCCM_BANK_BITS - pt.DCCM_WIDTH_BITS);
   localparam DCCM_INDEX_DEPTH = ((pt.DCCM_SIZE)*1024)/((pt.DCCM_BYTE_WIDTH)*(pt.DCCM_NUM_BANKS));  // Depth of memory bank

   logic [pt.DCCM_NUM_BANKS-1:0]                                        wren_bank;
   logic [pt.DCCM_NUM_BANKS-1:0]                                        rden_bank;
   logic [pt.DCCM_NUM_BANKS-1:0] [pt.DCCM_BITS-1:(pt.DCCM_BANK_BITS+2)] addr_bank;
   logic [pt.DCCM_BITS-1:(pt.DCCM_BANK_BITS+DCCM_WIDTH_BITS)]           rd_addr_even, rd_addr_odd;
   logic                                                                rd_unaligned, wr_unaligned;
   logic [pt.DCCM_NUM_BANKS-1:0] [pt.DCCM_FDATA_WIDTH-1:0]              dccm_bank_dout;
   logic [pt.DCCM_FDATA_WIDTH-1:0]                                      wrdata;

   logic [pt.DCCM_NUM_BANKS-1:0][pt.DCCM_FDATA_WIDTH-1:0]               wr_data_bank;

   logic [(DCCM_WIDTH_BITS+pt.DCCM_BANK_BITS-1):DCCM_WIDTH_BITS]        dccm_rd_addr_lo_q;
   logic [(DCCM_WIDTH_BITS+pt.DCCM_BANK_BITS-1):DCCM_WIDTH_BITS]        dccm_rd_addr_hi_q;

   logic [pt.DCCM_NUM_BANKS-1:0]            dccm_clken;

   assign rd_unaligned = (dccm_rd_addr_lo[DCCM_WIDTH_BITS+:pt.DCCM_BANK_BITS] != dccm_rd_addr_hi[DCCM_WIDTH_BITS+:pt.DCCM_BANK_BITS]);
   assign wr_unaligned = (dccm_wr_addr_lo[DCCM_WIDTH_BITS+:pt.DCCM_BANK_BITS] != dccm_wr_addr_hi[DCCM_WIDTH_BITS+:pt.DCCM_BANK_BITS]);

   // Align the read data
   assign dccm_rd_data_lo[pt.DCCM_FDATA_WIDTH-1:0]  = dccm_bank_dout[dccm_rd_addr_lo_q[pt.DCCM_WIDTH_BITS+:pt.DCCM_BANK_BITS]][pt.DCCM_FDATA_WIDTH-1:0];
   assign dccm_rd_data_hi[pt.DCCM_FDATA_WIDTH-1:0]  = dccm_bank_dout[dccm_rd_addr_hi_q[DCCM_WIDTH_BITS+:pt.DCCM_BANK_BITS]][pt.DCCM_FDATA_WIDTH-1:0];


   // 8 Banks, 16KB each (2048 x 72)
   for (genvar i=0; i<pt.DCCM_NUM_BANKS; i++) begin: mem_bank
      assign  wren_bank[i]        = dccm_wren & ((dccm_wr_addr_hi[2+:pt.DCCM_BANK_BITS] == i) | (dccm_wr_addr_lo[2+:pt.DCCM_BANK_BITS] == i));
      assign  rden_bank[i]        = dccm_rden & ((dccm_rd_addr_hi[2+:pt.DCCM_BANK_BITS] == i) | (dccm_rd_addr_lo[2+:pt.DCCM_BANK_BITS] == i));
      assign  addr_bank[i][(pt.DCCM_BANK_BITS+DCCM_WIDTH_BITS)+:DCCM_INDEX_BITS] = wren_bank[i] ? (((dccm_wr_addr_hi[2+:pt.DCCM_BANK_BITS] == i) & wr_unaligned) ?
                                                                                                        dccm_wr_addr_hi[(pt.DCCM_BANK_BITS+DCCM_WIDTH_BITS)+:DCCM_INDEX_BITS] :
                                                                                                        dccm_wr_addr_lo[(pt.DCCM_BANK_BITS+DCCM_WIDTH_BITS)+:DCCM_INDEX_BITS])  :
                                                                                                  (((dccm_rd_addr_hi[2+:pt.DCCM_BANK_BITS] == i) & rd_unaligned) ?
                                                                                                        dccm_rd_addr_hi[(pt.DCCM_BANK_BITS+DCCM_WIDTH_BITS)+:DCCM_INDEX_BITS] :
                                                                                                        dccm_rd_addr_lo[(pt.DCCM_BANK_BITS+DCCM_WIDTH_BITS)+:DCCM_INDEX_BITS]);

      assign wr_data_bank[i]     = ((dccm_wr_addr_hi[2+:pt.DCCM_BANK_BITS] == i) & wr_unaligned) ? dccm_wr_data_hi[pt.DCCM_FDATA_WIDTH-1:0] : dccm_wr_data_lo[pt.DCCM_FDATA_WIDTH-1:0];

      // clock gating section
      assign  dccm_clken[i] = (wren_bank[i] | rden_bank[i] | clk_override) ;
      // end clock gating section

      // Connect to exported RAM Banks
      always_comb begin
         dccm_mem_export.dccm_clken[i]                               = dccm_clken[i];
         dccm_mem_export.dccm_wren_bank[i]                           = wren_bank[i];
         dccm_mem_export.dccm_addr_bank[i]                           = addr_bank[i];
         dccm_mem_export.dccm_wr_data_bank[i]                        = wr_data_bank[i][pt.DCCM_DATA_WIDTH-1:0];
         dccm_mem_export.dccm_wr_ecc_bank[i]                         = wr_data_bank[i][pt.DCCM_FDATA_WIDTH-1:pt.DCCM_DATA_WIDTH];
         dccm_bank_dout[i][pt.DCCM_DATA_WIDTH-1:0]                   = dccm_mem_export.dccm_bank_dout[i];
         dccm_bank_dout[i][pt.DCCM_FDATA_WIDTH-1:pt.DCCM_DATA_WIDTH] = dccm_mem_export.dccm_bank_ecc[i];
      end

   end : mem_bank

   // Flops
   rvdff  #(pt.DCCM_BANK_BITS) rd_addr_lo_ff (.*, .din(dccm_rd_addr_lo[DCCM_WIDTH_BITS+:pt.DCCM_BANK_BITS]), .dout(dccm_rd_addr_lo_q[DCCM_WIDTH_BITS+:pt.DCCM_BANK_BITS]), .clk(active_clk));
   rvdff  #(pt.DCCM_BANK_BITS) rd_addr_hi_ff (.*, .din(dccm_rd_addr_hi[DCCM_WIDTH_BITS+:pt.DCCM_BANK_BITS]), .dout(dccm_rd_addr_hi_q[DCCM_WIDTH_BITS+:pt.DCCM_BANK_BITS]), .clk(active_clk));

endmodule // el2_lsu_dccm_mem


