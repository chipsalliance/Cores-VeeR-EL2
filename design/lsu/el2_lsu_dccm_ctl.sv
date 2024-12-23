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
//
// Owner:
// Function: DCCM for LSU pipe
// Comments: Single ported memory
//
//
// DC1 -> DC2 -> DC3 -> DC4 (Commit)
//
// //********************************************************************************

module el2_lsu_dccm_ctl
import el2_pkg::*;
#(
`include "el2_param.vh"
 )
  (
   input logic                             lsu_c2_m_clk,            // clocks
   input logic                             lsu_c2_r_clk,            // clocks
   input logic                             lsu_c1_r_clk,            // clocks
   input logic                             lsu_store_c1_r_clk,      // clocks
   input logic                             lsu_free_c2_clk,         // clocks
   input logic                             clk_override,            // Override non-functional clock gating
   input logic                             clk,                     // Clock only while core active.  Through one clock header.  For flops with    second clock header built in.  Connected to ACTIVE_L2CLK.

   input logic                             rst_l,                   // reset, active low

   input                                   el2_lsu_pkt_t lsu_pkt_r,// lsu packets
   input                                   el2_lsu_pkt_t lsu_pkt_m,// lsu packets
   input                                   el2_lsu_pkt_t lsu_pkt_d,// lsu packets
   input logic                             addr_in_dccm_d,          // address maps to dccm
   input logic                             addr_in_pic_d,           // address maps to pic
   input logic                             addr_in_pic_m,           // address maps to pic
   input logic                             addr_in_dccm_m, addr_in_dccm_r,   // address in dccm per pipe stage
   input logic                             addr_in_pic_r,                    // address in pic  per pipe stage
   input logic                             lsu_raw_fwd_lo_r, lsu_raw_fwd_hi_r,
   input logic                             lsu_commit_r,            // lsu instruction in r commits
   input logic                             ldst_dual_m, ldst_dual_r,// load/store is unaligned at 32 bit boundary per pipe stage

   // lsu address down the pipe
   input logic [31:0]                      lsu_addr_d,
   input logic [pt.DCCM_BITS-1:0]          lsu_addr_m,
   input logic [31:0]                      lsu_addr_r,

   // lsu address down the pipe - needed to check unaligned
   input logic [pt.DCCM_BITS-1:0]          end_addr_d,
   input logic [pt.DCCM_BITS-1:0]          end_addr_m,
   input logic [pt.DCCM_BITS-1:0]          end_addr_r,


   input logic                             stbuf_reqvld_any,        // write enable
   input logic [pt.LSU_SB_BITS-1:0]        stbuf_addr_any,          // stbuf address (aligned)

   input logic [pt.DCCM_DATA_WIDTH-1:0]    stbuf_data_any,          // the read out from stbuf
   input logic [pt.DCCM_ECC_WIDTH-1:0]     stbuf_ecc_any,           // the encoded data with ECC bits
   input logic [pt.DCCM_DATA_WIDTH-1:0]    stbuf_fwddata_hi_m,      // stbuf fowarding to load
   input logic [pt.DCCM_DATA_WIDTH-1:0]    stbuf_fwddata_lo_m,      // stbuf fowarding to load
   input logic [pt.DCCM_BYTE_WIDTH-1:0]    stbuf_fwdbyteen_hi_m,    // stbuf fowarding to load
   input logic [pt.DCCM_BYTE_WIDTH-1:0]    stbuf_fwdbyteen_lo_m,    // stbuf fowarding to load

   output logic [pt.DCCM_DATA_WIDTH-1:0]   dccm_rdata_hi_r,         // data from the dccm
   output logic [pt.DCCM_DATA_WIDTH-1:0]   dccm_rdata_lo_r,         // data from the dccm
   output logic [pt.DCCM_ECC_WIDTH-1:0]    dccm_data_ecc_hi_r,      // data from the dccm + ecc
   output logic [pt.DCCM_ECC_WIDTH-1:0]    dccm_data_ecc_lo_r,
   output logic [pt.DCCM_DATA_WIDTH-1:0]   lsu_ld_data_r,           // right justified, ie load byte will have data at 7:0
   output logic [pt.DCCM_DATA_WIDTH-1:0]   lsu_ld_data_corr_r,      // right justified & ECC corrected, ie load byte will have data at 7:0

   input logic                             lsu_double_ecc_error_r,  // lsu has a DED
   input logic                             single_ecc_error_hi_r,   // sec detected on hi dccm bank
   input logic                             single_ecc_error_lo_r,   // sec detected on lower dccm bank
   input logic [pt.DCCM_DATA_WIDTH-1:0]    sec_data_hi_r,           // corrected dccm data
   input logic [pt.DCCM_DATA_WIDTH-1:0]    sec_data_lo_r,           // corrected dccm data
   input logic [pt.DCCM_DATA_WIDTH-1:0]    sec_data_hi_r_ff,        // corrected dccm data
   input logic [pt.DCCM_DATA_WIDTH-1:0]    sec_data_lo_r_ff,        // corrected dccm data
   input logic [pt.DCCM_ECC_WIDTH-1:0]     sec_data_ecc_hi_r_ff,    // the encoded data with ECC bits
   input logic [pt.DCCM_ECC_WIDTH-1:0]     sec_data_ecc_lo_r_ff,    // the encoded data with ECC bits

   output logic [pt.DCCM_DATA_WIDTH-1:0]   dccm_rdata_hi_m,         // data from the dccm
   output logic [pt.DCCM_DATA_WIDTH-1:0]   dccm_rdata_lo_m,         // data from the dccm
   output logic [pt.DCCM_ECC_WIDTH-1:0]    dccm_data_ecc_hi_m,      // data from the dccm + ecc
   output logic [pt.DCCM_ECC_WIDTH-1:0]    dccm_data_ecc_lo_m,
   output logic [pt.DCCM_DATA_WIDTH-1:0]   lsu_ld_data_m,           // right justified, ie load byte will have data at 7:0

   input logic                             lsu_double_ecc_error_m,  // lsu has a DED
   input logic [pt.DCCM_DATA_WIDTH-1:0]    sec_data_hi_m,           // corrected dccm data
   input logic [pt.DCCM_DATA_WIDTH-1:0]    sec_data_lo_m,           // corrected dccm data

   input logic [31:0]                      store_data_m,            // Store data M-stage
   input logic                             dma_dccm_wen,            // Perform DMA writes only for word/dword
   input logic                             dma_pic_wen,             // Perform PIC writes
   input logic [2:0]                       dma_mem_tag_m,           // DMA Buffer entry number M-stage
   input logic [31:0]                      dma_mem_addr,            // DMA request address
   input logic [63:0]                      dma_mem_wdata,           // DMA write data
   input logic [31:0]                      dma_dccm_wdata_lo,       // Shift the dma data to lower bits to make it consistent to lsu stores
   input logic [31:0]                      dma_dccm_wdata_hi,       // Shift the dma data to lower bits to make it consistent to lsu stores
   input logic [pt.DCCM_ECC_WIDTH-1:0]     dma_dccm_wdata_ecc_hi,   // ECC bits for the DMA wdata
   input logic [pt.DCCM_ECC_WIDTH-1:0]     dma_dccm_wdata_ecc_lo,   // ECC bits for the DMA wdata

   output logic [pt.DCCM_DATA_WIDTH-1:0]   store_data_hi_r,
   output logic [pt.DCCM_DATA_WIDTH-1:0]   store_data_lo_r,
   output logic [pt.DCCM_DATA_WIDTH-1:0]   store_datafn_hi_r,       // data from the dccm
   output logic [pt.DCCM_DATA_WIDTH-1:0]   store_datafn_lo_r,       // data from the dccm
   output logic [31:0]                     store_data_r,            // raw store data to be sent to bus
   output logic                            ld_single_ecc_error_r,
   output logic                            ld_single_ecc_error_r_ff,

   output logic [31:0]                     picm_mask_data_m,        // pic data to stbuf
   output logic                            lsu_stbuf_commit_any,    // stbuf wins the dccm port or is to pic
   output logic                            lsu_dccm_rden_m,         // dccm read
   output logic                            lsu_dccm_rden_r,         // dccm read

   output logic                            dccm_dma_rvalid,         // dccm serviving the dma load
   output logic                            dccm_dma_ecc_error,      // DMA load had ecc error
   output logic [2:0]                      dccm_dma_rtag,           // DMA return tag
   output logic [63:0]                     dccm_dma_rdata,          // dccm data to dma request

   // DCCM ports
   output logic                            dccm_wren,               // dccm interface -- write
   output logic                            dccm_rden,               // dccm interface -- write
   output logic [pt.DCCM_BITS-1:0]         dccm_wr_addr_lo,         // dccm interface -- wr addr for lo bank
   output logic [pt.DCCM_BITS-1:0]         dccm_wr_addr_hi,         // dccm interface -- wr addr for hi bank
   output logic [pt.DCCM_BITS-1:0]         dccm_rd_addr_lo,         // dccm interface -- read address for lo bank
   output logic [pt.DCCM_BITS-1:0]         dccm_rd_addr_hi,         // dccm interface -- read address for hi bank
   output logic [pt.DCCM_FDATA_WIDTH-1:0]  dccm_wr_data_lo,         // dccm write data for lo bank
   output logic [pt.DCCM_FDATA_WIDTH-1:0]  dccm_wr_data_hi,         // dccm write data for hi bank

   input logic [pt.DCCM_FDATA_WIDTH-1:0]   dccm_rd_data_lo,         // dccm read data back from the dccm
   input logic [pt.DCCM_FDATA_WIDTH-1:0]   dccm_rd_data_hi,         // dccm read data back from the dccm

   // PIC ports
   output logic                            picm_wren,               // write to pic
   output logic                            picm_rden,               // read to pick
   output logic                            picm_mken,               // write to pic need a mask
   output logic [31:0]                     picm_rdaddr,             // address for pic read access
   output logic [31:0]                     picm_wraddr,             // address for pic write access
   output logic [31:0]                     picm_wr_data,            // write data
   input logic [31:0]                      picm_rd_data,            // read data

   // Excluding scan_mode from coverage as its usage is determined by the integrator of the VeeR core.
   /*pragma coverage off*/
   input logic                             scan_mode                // scan mode
   /*pragma coverage on*/
);


   localparam DCCM_WIDTH_BITS = $clog2(pt.DCCM_BYTE_WIDTH);

   logic                           lsu_dccm_rden_d, lsu_dccm_wren_d;
   logic                           ld_single_ecc_error_lo_r, ld_single_ecc_error_hi_r;
   logic                           ld_single_ecc_error_lo_r_ns, ld_single_ecc_error_hi_r_ns;
   logic                           ld_single_ecc_error_lo_r_ff, ld_single_ecc_error_hi_r_ff;
   logic                           lsu_double_ecc_error_r_ff;
   logic [pt.DCCM_BITS-1:0]        ld_sec_addr_lo_r_ff, ld_sec_addr_hi_r_ff;
   logic [pt.DCCM_DATA_WIDTH-1:0]  store_data_lo_r_in, store_data_hi_r_in ;
   logic [63:0]                    picm_rd_data_m;

   logic                           dccm_wr_bypass_d_m_hi, dccm_wr_bypass_d_r_hi;
   logic                           dccm_wr_bypass_d_m_lo, dccm_wr_bypass_d_r_lo;
   logic                           kill_ecc_corr_lo_r, kill_ecc_corr_hi_r;

    // byte_en flowing down
   logic [3:0]                     store_byteen_m ,store_byteen_r;
   logic [7:0]                     store_byteen_ext_m, store_byteen_ext_r;

   if (pt.LOAD_TO_USE_PLUS1 == 1) begin: L2U_Plus1_1
      logic [63:0]  lsu_rdata_r, lsu_rdata_corr_r;
      logic [63:0]  dccm_rdata_r, dccm_rdata_corr_r;
      logic [63:0]  stbuf_fwddata_r;
      logic [7:0]   stbuf_fwdbyteen_r;
      logic [31:0]  stbuf_fwddata_lo_r, stbuf_fwddata_hi_r;
      logic [3:0]   stbuf_fwdbyteen_lo_r, stbuf_fwdbyteen_hi_r;
      logic [31:0]  lsu_rdata_lo_r, lsu_rdata_hi_r;
      logic [63:0]  picm_rd_data_r;
      logic [63:32] lsu_ld_data_r_nc, lsu_ld_data_corr_r_nc;
      logic [2:0]   dma_mem_tag_r;
      logic         stbuf_fwddata_en;

      assign dccm_dma_rvalid      = lsu_pkt_r.valid & lsu_pkt_r.load & lsu_pkt_r.dma;
      assign dccm_dma_ecc_error   = lsu_double_ecc_error_r;
      assign dccm_dma_rtag[2:0]   = dma_mem_tag_r[2:0];
      assign dccm_dma_rdata[63:0] = ldst_dual_r ? lsu_rdata_corr_r[63:0] : {2{lsu_rdata_corr_r[31:0]}};
      assign {lsu_ld_data_r_nc[63:32], lsu_ld_data_r[31:0]}           = lsu_rdata_r[63:0] >> 8*lsu_addr_r[1:0];
      assign {lsu_ld_data_corr_r_nc[63:32], lsu_ld_data_corr_r[31:0]} = lsu_rdata_corr_r[63:0] >> 8*lsu_addr_r[1:0];

      assign picm_rd_data_r[63:32]   = picm_rd_data_r[31:0];
      assign dccm_rdata_r[63:0]      = {dccm_rdata_hi_r[31:0],dccm_rdata_lo_r[31:0]};
      assign dccm_rdata_corr_r[63:0] = {sec_data_hi_r[31:0],sec_data_lo_r[31:0]};
      assign stbuf_fwddata_r[63:0]   = {stbuf_fwddata_hi_r[31:0], stbuf_fwddata_lo_r[31:0]};
      assign stbuf_fwdbyteen_r[7:0]  = {stbuf_fwdbyteen_hi_r[3:0], stbuf_fwdbyteen_lo_r[3:0]};
      assign stbuf_fwddata_en        = (|stbuf_fwdbyteen_hi_m[3:0]) | (|stbuf_fwdbyteen_lo_m[3:0]) | clk_override;

      for (genvar i=0; i<8; i++) begin: GenDMAData
         assign lsu_rdata_corr_r[(8*i)+7:8*i]  = stbuf_fwdbyteen_r[i] ? stbuf_fwddata_r[(8*i)+7:8*i] :
                                                                        (addr_in_pic_r ? picm_rd_data_r[(8*i)+7:8*i] :  ({8{addr_in_dccm_r}} & dccm_rdata_corr_r[(8*i)+7:8*i]));

         assign lsu_rdata_r[(8*i)+7:8*i]       = stbuf_fwdbyteen_r[i] ? stbuf_fwddata_r[(8*i)+7:8*i] :
                                                                        (addr_in_pic_r ? picm_rd_data_r[(8*i)+7:8*i] :  ({8{addr_in_dccm_r}} & dccm_rdata_r[(8*i)+7:8*i]));
      end
      rvdffe #(pt.DCCM_DATA_WIDTH) dccm_rdata_hi_r_ff    (.*, .din(dccm_rdata_hi_m[pt.DCCM_DATA_WIDTH-1:0]), .dout(dccm_rdata_hi_r[pt.DCCM_DATA_WIDTH-1:0]), .en((lsu_dccm_rden_m & ldst_dual_m) | clk_override));
      rvdffe #(pt.DCCM_DATA_WIDTH) dccm_rdata_lo_r_ff    (.*, .din(dccm_rdata_lo_m[pt.DCCM_DATA_WIDTH-1:0]), .dout(dccm_rdata_lo_r[pt.DCCM_DATA_WIDTH-1:0]), .en(lsu_dccm_rden_m | clk_override));
      rvdffe #(2*pt.DCCM_ECC_WIDTH)  dccm_data_ecc_r_ff  (.*, .din({dccm_data_ecc_hi_m[pt.DCCM_ECC_WIDTH-1:0], dccm_data_ecc_lo_m[pt.DCCM_ECC_WIDTH-1:0]}),
                                                              .dout({dccm_data_ecc_hi_r[pt.DCCM_ECC_WIDTH-1:0], dccm_data_ecc_lo_r[pt.DCCM_ECC_WIDTH-1:0]}),                                  .en(lsu_dccm_rden_m | clk_override));
      rvdff #(8)                   stbuf_fwdbyteen_ff    (.*, .din({stbuf_fwdbyteen_hi_m[3:0], stbuf_fwdbyteen_lo_m[3:0]}), .dout({stbuf_fwdbyteen_hi_r[3:0], stbuf_fwdbyteen_lo_r[3:0]}), .clk(lsu_c2_r_clk));
      rvdffe #(64)                 stbuf_fwddata_ff      (.*, .din({stbuf_fwddata_hi_m[31:0], stbuf_fwddata_lo_m[31:0]}),   .dout({stbuf_fwddata_hi_r[31:0], stbuf_fwddata_lo_r[31:0]}),   .en(stbuf_fwddata_en));
      rvdffe #(32)                 picm_rddata_rff       (.*, .din(picm_rd_data_m[31:0]),                                   .dout(picm_rd_data_r[31:0]),                                   .en(addr_in_pic_m | clk_override));
      rvdff #(3)                   dma_mem_tag_rff       (.*, .din(dma_mem_tag_m[2:0]),                                     .dout(dma_mem_tag_r[2:0]),                                     .clk(lsu_c1_r_clk));

   end else begin: L2U_Plus1_0

      logic [63:0]  lsu_rdata_m, lsu_rdata_corr_m;
      logic [63:0]  dccm_rdata_m, dccm_rdata_corr_m;
      logic [63:0]  stbuf_fwddata_m;
      logic [7:0]   stbuf_fwdbyteen_m;
      logic [63:32] lsu_ld_data_m_nc, lsu_ld_data_corr_m_nc;
      logic [31:0]  lsu_ld_data_corr_m;

      assign dccm_dma_rvalid      = lsu_pkt_m.valid & lsu_pkt_m.load & lsu_pkt_m.dma;
      assign dccm_dma_ecc_error   = lsu_double_ecc_error_m;
      assign dccm_dma_rtag[2:0]   = dma_mem_tag_m[2:0];
      assign dccm_dma_rdata[63:0] = ldst_dual_m ? lsu_rdata_corr_m[63:0] : {2{lsu_rdata_corr_m[31:0]}};
      assign {lsu_ld_data_m_nc[63:32], lsu_ld_data_m[31:0]} = 64'(lsu_rdata_m[63:0] >> 8*lsu_addr_m[1:0]);
      assign {lsu_ld_data_corr_m_nc[63:32], lsu_ld_data_corr_m[31:0]} = 64'(lsu_rdata_corr_m[63:0] >> 8*lsu_addr_m[1:0]);

      assign dccm_rdata_m[63:0]      = {dccm_rdata_hi_m[31:0],dccm_rdata_lo_m[31:0]};
      assign dccm_rdata_corr_m[63:0] = {sec_data_hi_m[31:0],sec_data_lo_m[31:0]};
      assign stbuf_fwddata_m[63:0]   = {stbuf_fwddata_hi_m[31:0], stbuf_fwddata_lo_m[31:0]};
      assign stbuf_fwdbyteen_m[7:0]  = {stbuf_fwdbyteen_hi_m[3:0], stbuf_fwdbyteen_lo_m[3:0]};

      for (genvar i=0; i<8; i++) begin: GenLoop
         assign lsu_rdata_corr_m[(8*i)+7:8*i] = stbuf_fwdbyteen_m[i] ? stbuf_fwddata_m[(8*i)+7:8*i] :
                                                                       (addr_in_pic_m ? picm_rd_data_m[(8*i)+7:8*i] : ({8{addr_in_dccm_m}} & dccm_rdata_corr_m[(8*i)+7:8*i]));

         assign lsu_rdata_m[(8*i)+7:8*i]      = stbuf_fwdbyteen_m[i] ? stbuf_fwddata_m[(8*i)+7:8*i] :
                                                                       (addr_in_pic_m ? picm_rd_data_m[(8*i)+7:8*i] : ({8{addr_in_dccm_m}} & dccm_rdata_m[(8*i)+7:8*i]));
      end

      rvdffe #(32) lsu_ld_data_corr_rff(.*, .din(lsu_ld_data_corr_m[31:0]), .dout(lsu_ld_data_corr_r[31:0]), .en((lsu_pkt_m.valid & lsu_pkt_m.load & (addr_in_pic_m | addr_in_dccm_m)) | clk_override));
   end

   assign kill_ecc_corr_lo_r = (((lsu_addr_d[pt.DCCM_BITS-1:2] == lsu_addr_r[pt.DCCM_BITS-1:2]) | (end_addr_d[pt.DCCM_BITS-1:2] == lsu_addr_r[pt.DCCM_BITS-1:2])) & lsu_pkt_d.valid & lsu_pkt_d.store & lsu_pkt_d.dma & addr_in_dccm_d) |
                               (((lsu_addr_m[pt.DCCM_BITS-1:2] == lsu_addr_r[pt.DCCM_BITS-1:2]) | (end_addr_m[pt.DCCM_BITS-1:2] == lsu_addr_r[pt.DCCM_BITS-1:2])) & lsu_pkt_m.valid & lsu_pkt_m.store & lsu_pkt_m.dma & addr_in_dccm_m);

   assign kill_ecc_corr_hi_r = (((lsu_addr_d[pt.DCCM_BITS-1:2] == end_addr_r[pt.DCCM_BITS-1:2]) | (end_addr_d[pt.DCCM_BITS-1:2] == end_addr_r[pt.DCCM_BITS-1:2])) & lsu_pkt_d.valid & lsu_pkt_d.store & lsu_pkt_d.dma & addr_in_dccm_d) |
                               (((lsu_addr_m[pt.DCCM_BITS-1:2] == end_addr_r[pt.DCCM_BITS-1:2]) | (end_addr_m[pt.DCCM_BITS-1:2] == end_addr_r[pt.DCCM_BITS-1:2])) & lsu_pkt_m.valid & lsu_pkt_m.store & lsu_pkt_m.dma & addr_in_dccm_m);

   assign ld_single_ecc_error_lo_r = lsu_pkt_r.load & single_ecc_error_lo_r & ~lsu_raw_fwd_lo_r;
   assign ld_single_ecc_error_hi_r = lsu_pkt_r.load & single_ecc_error_hi_r & ~lsu_raw_fwd_hi_r;
   assign ld_single_ecc_error_r    = (ld_single_ecc_error_lo_r | ld_single_ecc_error_hi_r) & ~lsu_double_ecc_error_r;

   assign ld_single_ecc_error_lo_r_ns = ld_single_ecc_error_lo_r & (lsu_commit_r | lsu_pkt_r.dma) & ~kill_ecc_corr_lo_r;
   assign ld_single_ecc_error_hi_r_ns = ld_single_ecc_error_hi_r & (lsu_commit_r | lsu_pkt_r.dma) & ~kill_ecc_corr_hi_r;
   assign ld_single_ecc_error_r_ff = (ld_single_ecc_error_lo_r_ff | ld_single_ecc_error_hi_r_ff) & ~lsu_double_ecc_error_r_ff;

   assign lsu_stbuf_commit_any = stbuf_reqvld_any &
                                 (~(lsu_dccm_rden_d | lsu_dccm_wren_d | ld_single_ecc_error_r_ff) |
                                  (lsu_dccm_rden_d & ~((stbuf_addr_any[pt.DCCM_WIDTH_BITS+:pt.DCCM_BANK_BITS] == lsu_addr_d[pt.DCCM_WIDTH_BITS+:pt.DCCM_BANK_BITS]) |
                                                       (stbuf_addr_any[pt.DCCM_WIDTH_BITS+:pt.DCCM_BANK_BITS] == end_addr_d[pt.DCCM_WIDTH_BITS+:pt.DCCM_BANK_BITS]))));

   // No need to read for aligned word/dword stores since ECC will come by new data completely
   assign lsu_dccm_rden_d = lsu_pkt_d.valid & (lsu_pkt_d.load | (lsu_pkt_d.store & (~(lsu_pkt_d.word | lsu_pkt_d.dword) | (lsu_addr_d[1:0] != 2'b0)))) & addr_in_dccm_d;

   // DMA will read/write in decode stage
   assign lsu_dccm_wren_d = dma_dccm_wen;

   // DCCM inputs
   assign dccm_wren                             = lsu_dccm_wren_d | lsu_stbuf_commit_any | ld_single_ecc_error_r_ff;
   assign dccm_rden                             = lsu_dccm_rden_d & addr_in_dccm_d;
   assign dccm_wr_addr_lo[pt.DCCM_BITS-1:0]     = ld_single_ecc_error_r_ff ? (ld_single_ecc_error_lo_r_ff ? ld_sec_addr_lo_r_ff[pt.DCCM_BITS-1:0] : ld_sec_addr_hi_r_ff[pt.DCCM_BITS-1:0]) :
                                                                             lsu_dccm_wren_d ? lsu_addr_d[pt.DCCM_BITS-1:0] : stbuf_addr_any[pt.DCCM_BITS-1:0];
   assign dccm_wr_addr_hi[pt.DCCM_BITS-1:0]     = ld_single_ecc_error_r_ff ? (ld_single_ecc_error_hi_r_ff ? ld_sec_addr_hi_r_ff[pt.DCCM_BITS-1:0] : ld_sec_addr_lo_r_ff[pt.DCCM_BITS-1:0]) :
                                                                             lsu_dccm_wren_d ? end_addr_d[pt.DCCM_BITS-1:0] : stbuf_addr_any[pt.DCCM_BITS-1:0];
   assign dccm_rd_addr_lo[pt.DCCM_BITS-1:0]     = lsu_addr_d[pt.DCCM_BITS-1:0];
   assign dccm_rd_addr_hi[pt.DCCM_BITS-1:0]     = end_addr_d[pt.DCCM_BITS-1:0];
   assign dccm_wr_data_lo[pt.DCCM_FDATA_WIDTH-1:0] = ld_single_ecc_error_r_ff ? (ld_single_ecc_error_lo_r_ff ? {sec_data_ecc_lo_r_ff[pt.DCCM_ECC_WIDTH-1:0],sec_data_lo_r_ff[pt.DCCM_DATA_WIDTH-1:0]} :
                                                                                                               {sec_data_ecc_hi_r_ff[pt.DCCM_ECC_WIDTH-1:0],sec_data_hi_r_ff[pt.DCCM_DATA_WIDTH-1:0]}) :
                                                                                (dma_dccm_wen ? {dma_dccm_wdata_ecc_lo[pt.DCCM_ECC_WIDTH-1:0],dma_dccm_wdata_lo[pt.DCCM_DATA_WIDTH-1:0]} :
                                                                                                {stbuf_ecc_any[pt.DCCM_ECC_WIDTH-1:0],stbuf_data_any[pt.DCCM_DATA_WIDTH-1:0]});
   assign dccm_wr_data_hi[pt.DCCM_FDATA_WIDTH-1:0] = ld_single_ecc_error_r_ff ? (ld_single_ecc_error_hi_r_ff ? {sec_data_ecc_hi_r_ff[pt.DCCM_ECC_WIDTH-1:0],sec_data_hi_r_ff[pt.DCCM_DATA_WIDTH-1:0]} :
                                                                                                               {sec_data_ecc_lo_r_ff[pt.DCCM_ECC_WIDTH-1:0],sec_data_lo_r_ff[pt.DCCM_DATA_WIDTH-1:0]}) :
                                                                                (dma_dccm_wen ? {dma_dccm_wdata_ecc_hi[pt.DCCM_ECC_WIDTH-1:0],dma_dccm_wdata_hi[pt.DCCM_DATA_WIDTH-1:0]} :
                                                                                                {stbuf_ecc_any[pt.DCCM_ECC_WIDTH-1:0],stbuf_data_any[pt.DCCM_DATA_WIDTH-1:0]});

   // DCCM outputs
   assign store_byteen_m[3:0] = {4{lsu_pkt_m.store}} &
                                (({4{lsu_pkt_m.by}}    & 4'b0001) |
                                 ({4{lsu_pkt_m.half}}  & 4'b0011) |
                                 ({4{lsu_pkt_m.word}}  & 4'b1111));

   assign store_byteen_r[3:0] =  {4{lsu_pkt_r.store}} &
                                 (({4{lsu_pkt_r.by}}    & 4'b0001) |
                                  ({4{lsu_pkt_r.half}}  & 4'b0011) |
                                  ({4{lsu_pkt_r.word}}  & 4'b1111));

   assign store_byteen_ext_m[7:0] = {4'b0,store_byteen_m[3:0]} << lsu_addr_m[1:0];      // The packet in m
   assign store_byteen_ext_r[7:0] = {4'b0,store_byteen_r[3:0]} << lsu_addr_r[1:0];



   assign dccm_wr_bypass_d_m_lo   = (stbuf_addr_any[pt.DCCM_BITS-1:2] == lsu_addr_m[pt.DCCM_BITS-1:2]) & addr_in_dccm_m;
   assign dccm_wr_bypass_d_m_hi   = (stbuf_addr_any[pt.DCCM_BITS-1:2] == end_addr_m[pt.DCCM_BITS-1:2]) & addr_in_dccm_m;

   assign dccm_wr_bypass_d_r_lo   = (stbuf_addr_any[pt.DCCM_BITS-1:2] == lsu_addr_r[pt.DCCM_BITS-1:2]) & addr_in_dccm_r;
   assign dccm_wr_bypass_d_r_hi   = (stbuf_addr_any[pt.DCCM_BITS-1:2] == end_addr_r[pt.DCCM_BITS-1:2]) & addr_in_dccm_r;


   if (pt.LOAD_TO_USE_PLUS1 == 1) begin: L2U1_Plus1_1
      logic        dccm_wren_Q;
      logic [31:0] dccm_wr_data_Q;
      logic        dccm_wr_bypass_d_m_lo_Q, dccm_wr_bypass_d_m_hi_Q;
      logic [31:0] store_data_pre_hi_r, store_data_pre_lo_r;

      assign {store_data_pre_hi_r[31:0], store_data_pre_lo_r[31:0]} = {32'b0,store_data_r[31:0]} << 8*lsu_addr_r[1:0];

      for (genvar i=0; i<4; i++) begin
          assign store_data_lo_r[(8*i)+7:(8*i)]   = store_byteen_ext_r[i] ? store_data_pre_lo_r[(8*i)+7:(8*i)] : ((dccm_wren_Q & dccm_wr_bypass_d_m_lo_Q) ? dccm_wr_data_Q[(8*i)+7:(8*i)] : sec_data_lo_r[(8*i)+7:(8*i)]);
          assign store_data_hi_r[(8*i)+7:(8*i)]   = store_byteen_ext_r[i+4] ? store_data_pre_hi_r[(8*i)+7:(8*i)] : ((dccm_wren_Q & dccm_wr_bypass_d_m_hi_Q) ? dccm_wr_data_Q[(8*i)+7:(8*i)] : sec_data_hi_r[(8*i)+7:(8*i)]);

          assign store_datafn_lo_r[(8*i)+7:(8*i)] = store_byteen_ext_r[i] ? store_data_pre_lo_r[(8*i)+7:(8*i)] : ((lsu_stbuf_commit_any & dccm_wr_bypass_d_r_lo) ? stbuf_data_any[(8*i)+7:(8*i)] :
                                                                                                                    ((dccm_wren_Q & dccm_wr_bypass_d_m_lo_Q) ? dccm_wr_data_Q[(8*i)+7:(8*i)] : sec_data_lo_r[(8*i)+7:(8*i)]));
          assign store_datafn_hi_r[(8*i)+7:(8*i)] = store_byteen_ext_r[i+4] ? store_data_pre_hi_r[(8*i)+7:(8*i)] : ((lsu_stbuf_commit_any & dccm_wr_bypass_d_r_hi) ? stbuf_data_any[(8*i)+7:(8*i)] :
                                                                                                                    ((dccm_wren_Q & dccm_wr_bypass_d_m_hi_Q) ? dccm_wr_data_Q[(8*i)+7:(8*i)] : sec_data_hi_r[(8*i)+7:(8*i)]));
      end

      rvdff #(1)   dccm_wren_ff       (.*, .din(lsu_stbuf_commit_any),  .dout(dccm_wren_Q),             .clk(lsu_free_c2_clk));   // ECC load errors writing to dccm shouldn't fwd to stores in pipe
      rvdffe #(32) dccm_wrdata_ff     (.*, .din(stbuf_data_any[31:0]),  .dout(dccm_wr_data_Q[31:0]),    .en(lsu_stbuf_commit_any | clk_override), .clk(clk));
      rvdff #(1)   dccm_wrbyp_dm_loff (.*, .din(dccm_wr_bypass_d_m_lo), .dout(dccm_wr_bypass_d_m_lo_Q), .clk(lsu_free_c2_clk));
      rvdff #(1)   dccm_wrbyp_dm_hiff (.*, .din(dccm_wr_bypass_d_m_hi), .dout(dccm_wr_bypass_d_m_hi_Q), .clk(lsu_free_c2_clk));
      rvdff #(32)  store_data_rff     (.*, .din(store_data_m[31:0]),    .dout(store_data_r[31:0]),      .clk(lsu_store_c1_r_clk));

   end else begin: L2U1_Plus1_0

      logic [31:0] store_data_hi_m, store_data_lo_m;
      logic [63:0] store_data_mask;
      assign {store_data_hi_m[31:0] , store_data_lo_m[31:0]} = {32'b0,store_data_m[31:0]} << 8*lsu_addr_m[1:0];

      for (genvar i=0; i<4; i++) begin
         assign store_data_hi_r_in[(8*i)+7:(8*i)]  = store_byteen_ext_m[i+4] ? store_data_hi_m[(8*i)+7:(8*i)] :
                                                                               ((lsu_stbuf_commit_any &  dccm_wr_bypass_d_m_hi)   ? stbuf_data_any[(8*i)+7:(8*i)] : sec_data_hi_m[(8*i)+7:(8*i)]);
         assign store_data_lo_r_in[(8*i)+7:(8*i)]  = store_byteen_ext_m[i]   ? store_data_lo_m[(8*i)+7:(8*i)] :
                                                                               ((lsu_stbuf_commit_any &  dccm_wr_bypass_d_m_lo) ? stbuf_data_any[(8*i)+7:(8*i)] : sec_data_lo_m[(8*i)+7:(8*i)]);

         assign store_datafn_lo_r[(8*i)+7:(8*i)]   = (lsu_stbuf_commit_any & dccm_wr_bypass_d_r_lo & ~store_byteen_ext_r[i])   ? stbuf_data_any[(8*i)+7:(8*i)] : store_data_lo_r[(8*i)+7:(8*i)];
         assign store_datafn_hi_r[(8*i)+7:(8*i)]   = (lsu_stbuf_commit_any & dccm_wr_bypass_d_r_hi & ~store_byteen_ext_r[i+4]) ? stbuf_data_any[(8*i)+7:(8*i)] : store_data_hi_r[(8*i)+7:(8*i)];
      end // for (genvar i=0; i<BYTE_WIDTH; i++)

      for (genvar i=0; i<4; i++) begin
         assign store_data_mask[(8*i)+7:(8*i)] = {8{store_byteen_r[i]}};
      end
      assign store_data_r[31:0]      = 32'({store_data_hi_r[31:0],store_data_lo_r[31:0]} >> 8*lsu_addr_r[1:0]) & store_data_mask[31:0];

      rvdffe #(pt.DCCM_DATA_WIDTH) store_data_hi_rff (.*, .din(store_data_hi_r_in[pt.DCCM_DATA_WIDTH-1:0]), .dout(store_data_hi_r[pt.DCCM_DATA_WIDTH-1:0]), .en((ldst_dual_m & lsu_pkt_m.valid & lsu_pkt_m.store) | clk_override), .clk(clk));
      rvdff  #(pt.DCCM_DATA_WIDTH) store_data_lo_rff (.*, .din(store_data_lo_r_in[pt.DCCM_DATA_WIDTH-1:0]), .dout(store_data_lo_r[pt.DCCM_DATA_WIDTH-1:0]), .clk(lsu_store_c1_r_clk));

   end

   assign dccm_rdata_lo_m[pt.DCCM_DATA_WIDTH-1:0]   = dccm_rd_data_lo[pt.DCCM_DATA_WIDTH-1:0]; // for ld choose dccm_out
   assign dccm_rdata_hi_m[pt.DCCM_DATA_WIDTH-1:0]   = dccm_rd_data_hi[pt.DCCM_DATA_WIDTH-1:0]; // for ld this is used for ecc

   assign dccm_data_ecc_lo_m[pt.DCCM_ECC_WIDTH-1:0] = dccm_rd_data_lo[pt.DCCM_FDATA_WIDTH-1:pt.DCCM_DATA_WIDTH];
   assign dccm_data_ecc_hi_m[pt.DCCM_ECC_WIDTH-1:0] = dccm_rd_data_hi[pt.DCCM_FDATA_WIDTH-1:pt.DCCM_DATA_WIDTH];

   // PIC signals. PIC ignores the lower 2 bits of address since PIC memory registers are 32-bits
   assign picm_wren          = (lsu_pkt_r.valid & lsu_pkt_r.store & addr_in_pic_r & lsu_commit_r) | dma_pic_wen;
   assign picm_rden          = lsu_pkt_d.valid & lsu_pkt_d.load  & addr_in_pic_d;
   assign picm_mken          = lsu_pkt_d.valid & lsu_pkt_d.store & addr_in_pic_d;  // Get the mask for stores
   assign picm_rdaddr[31:0]  = pt.PIC_BASE_ADDR | {{32-pt.PIC_BITS{1'b0}},lsu_addr_d[pt.PIC_BITS-1:0]};

   assign picm_wraddr[31:0]  = pt.PIC_BASE_ADDR | {{32-pt.PIC_BITS{1'b0}},(dma_pic_wen ? dma_mem_addr[pt.PIC_BITS-1:0] : lsu_addr_r[pt.PIC_BITS-1:0])};

   assign picm_wr_data[31:0] = dma_pic_wen ? dma_mem_wdata[31:0] : store_datafn_lo_r[31:0];

   assign picm_mask_data_m[31:0] = picm_rd_data_m[31:0];
   assign picm_rd_data_m[63:0]   = {picm_rd_data[31:0],picm_rd_data[31:0]};

   if (pt.DCCM_ENABLE == 1) begin: Gen_dccm_enable
      rvdff #(1) dccm_rden_mff (.*, .din(lsu_dccm_rden_d), .dout(lsu_dccm_rden_m), .clk(lsu_c2_m_clk));
      rvdff #(1) dccm_rden_rff (.*, .din(lsu_dccm_rden_m), .dout(lsu_dccm_rden_r), .clk(lsu_c2_r_clk));

      // ECC correction flops since dccm write happens next cycle
      // We are writing to dccm in r+1 for ecc correction since fast_int needs to be blocked in decode - 1. We can probably write in r for plus0 configuration since we know ecc error in M.
      // In that case these (_ff) flops are needed only in plus1 configuration
      rvdff #(1) ld_double_ecc_error_rff    (.*, .din(lsu_double_ecc_error_r),   .dout(lsu_double_ecc_error_r_ff),   .clk(lsu_free_c2_clk));
      rvdff #(1) ld_single_ecc_error_hi_rff (.*, .din(ld_single_ecc_error_hi_r_ns), .dout(ld_single_ecc_error_hi_r_ff), .clk(lsu_free_c2_clk));
      rvdff #(1) ld_single_ecc_error_lo_rff (.*, .din(ld_single_ecc_error_lo_r_ns), .dout(ld_single_ecc_error_lo_r_ff), .clk(lsu_free_c2_clk));
      rvdffe #(pt.DCCM_BITS) ld_sec_addr_hi_rff (.*, .din(end_addr_r[pt.DCCM_BITS-1:0]), .dout(ld_sec_addr_hi_r_ff[pt.DCCM_BITS-1:0]), .en(ld_single_ecc_error_r | clk_override), .clk(clk));
      rvdffe #(pt.DCCM_BITS) ld_sec_addr_lo_rff (.*, .din(lsu_addr_r[pt.DCCM_BITS-1:0]), .dout(ld_sec_addr_lo_r_ff[pt.DCCM_BITS-1:0]), .en(ld_single_ecc_error_r | clk_override), .clk(clk));

   end else begin: Gen_dccm_disable
      assign lsu_dccm_rden_m = '0;
      assign lsu_dccm_rden_r = '0;

      assign lsu_double_ecc_error_r_ff = 1'b0;
      assign ld_single_ecc_error_hi_r_ff = 1'b0;
      assign ld_single_ecc_error_lo_r_ff = 1'b0;
      assign ld_sec_addr_hi_r_ff[pt.DCCM_BITS-1:0] = '0;
      assign ld_sec_addr_lo_r_ff[pt.DCCM_BITS-1:0] = '0;
   end

`ifdef RV_ASSERT_ON

   // Load single ECC error correction implies commit/dma
   property ld_single_ecc_error_commit;
      @(posedge clk) disable iff(~rst_l) (ld_single_ecc_error_r_ff & dccm_wren) |-> ($past(lsu_commit_r | lsu_pkt_r.dma));
   endproperty
   assert_ld_single_ecc_error_commit: assert property (ld_single_ecc_error_commit) else
     $display("No commit or DMA but ECC correction happened");


`endif

endmodule
