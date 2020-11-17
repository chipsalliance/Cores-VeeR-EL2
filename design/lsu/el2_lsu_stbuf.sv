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
// Function: Store Buffer
// Comments: Dual writes and single drain
//
//
// DC1 -> DC2 -> DC3 -> DC4 (Commit)
//
// //********************************************************************************


module el2_lsu_stbuf
import el2_pkg::*;
#(
`include "el2_param.vh"
 )
(
   input logic                           clk,                         // core clock
   input logic                           rst_l,                       // reset

   input logic                           lsu_stbuf_c1_clk,            // stbuf clock
   input logic                           lsu_free_c2_clk,             // free clk

   // Store Buffer input
   input logic                           store_stbuf_reqvld_r,        // core instruction goes to stbuf
   input logic                           lsu_commit_r,                // lsu commits
   input logic                           dec_lsu_valid_raw_d,         // Speculative decode valid
   input logic [pt.DCCM_DATA_WIDTH-1:0]  store_data_hi_r,             // merged data from the dccm for stores. This is used for fwding
   input logic [pt.DCCM_DATA_WIDTH-1:0]  store_data_lo_r,             // merged data from the dccm for stores. This is used for fwding
   input logic [pt.DCCM_DATA_WIDTH-1:0]  store_datafn_hi_r,           // merged data from the dccm for stores
   input logic [pt.DCCM_DATA_WIDTH-1:0]  store_datafn_lo_r,           // merged data from the dccm for stores

   // Store Buffer output
   output logic                          stbuf_reqvld_any,            // stbuf is draining
   output logic                          stbuf_reqvld_flushed_any,    // Top entry is flushed
   output logic [pt.LSU_SB_BITS-1:0]     stbuf_addr_any,              // address
   output logic [pt.DCCM_DATA_WIDTH-1:0] stbuf_data_any,              // stbuf data

   input  logic                          lsu_stbuf_commit_any,        // pop the stbuf as it commite
   output logic                          lsu_stbuf_full_any,          // stbuf is full
   output logic                          lsu_stbuf_empty_any,         // stbuf is empty
   output logic                          ldst_stbuf_reqvld_r,         // needed for clocking

   input logic [pt.LSU_SB_BITS-1:0]      lsu_addr_d,                  // lsu address D-stage
   input logic [31:0]                    lsu_addr_m,                  // lsu address M-stage
   input logic [31:0]                    lsu_addr_r,                  // lsu address R-stage

   input logic [pt.LSU_SB_BITS-1:0]      end_addr_d,                  // lsu end address D-stage - needed to check unaligned
   input logic [31:0]                    end_addr_m,                  // lsu end address M-stage - needed to check unaligned
   input logic [31:0]                    end_addr_r,                  // lsu end address R-stage - needed to check unaligned

   input logic                           ldst_dual_d, ldst_dual_m, ldst_dual_r,
   input logic                           addr_in_dccm_m,              // address is in dccm
   input logic                           addr_in_dccm_r,              // address is in dccm

   // Forwarding signals
   input logic                           lsu_cmpen_m,                 // needed for forwarding stbuf - load
   input el2_lsu_pkt_t                  lsu_pkt_m,                   // LSU packet M-stage
   input el2_lsu_pkt_t                  lsu_pkt_r,                   // LSU packet R-stage

   output logic [pt.DCCM_DATA_WIDTH-1:0] stbuf_fwddata_hi_m,          // stbuf data
   output logic [pt.DCCM_DATA_WIDTH-1:0] stbuf_fwddata_lo_m,          // stbuf data
   output logic [pt.DCCM_BYTE_WIDTH-1:0] stbuf_fwdbyteen_hi_m,        // stbuf data
   output logic [pt.DCCM_BYTE_WIDTH-1:0] stbuf_fwdbyteen_lo_m,        // stbuf data

   input  logic       scan_mode                                       // Scan mode

);


   localparam DEPTH      = pt.LSU_STBUF_DEPTH;
   localparam DATA_WIDTH = pt.DCCM_DATA_WIDTH;
   localparam BYTE_WIDTH = pt.DCCM_BYTE_WIDTH;
   localparam DEPTH_LOG2 = $clog2(DEPTH);

   // These are the fields in the store queue
   logic [DEPTH-1:0]                     stbuf_vld;
   logic [DEPTH-1:0]                     stbuf_dma_kill;
   logic [DEPTH-1:0][pt.LSU_SB_BITS-1:0] stbuf_addr;
   logic [DEPTH-1:0][BYTE_WIDTH-1:0]     stbuf_byteen;
   logic [DEPTH-1:0][DATA_WIDTH-1:0]     stbuf_data;

   logic [DEPTH-1:0]                     sel_lo;
   logic [DEPTH-1:0]                     stbuf_wr_en;
   logic [DEPTH-1:0]                     stbuf_dma_kill_en;
   logic [DEPTH-1:0]                     stbuf_reset;
   logic [DEPTH-1:0][pt.LSU_SB_BITS-1:0] stbuf_addrin;
   logic [DEPTH-1:0][DATA_WIDTH-1:0]     stbuf_datain;
   logic [DEPTH-1:0][BYTE_WIDTH-1:0]     stbuf_byteenin;

   logic [7:0]             store_byteen_ext_r;
   logic [BYTE_WIDTH-1:0]  store_byteen_hi_r;
   logic [BYTE_WIDTH-1:0]  store_byteen_lo_r;

   logic                   WrPtrEn, RdPtrEn;
   logic [DEPTH_LOG2-1:0]  WrPtr, RdPtr;
   logic [DEPTH_LOG2-1:0]  NxtWrPtr, NxtRdPtr;
   logic [DEPTH_LOG2-1:0]  WrPtrPlus1, WrPtrPlus2, RdPtrPlus1;

   logic                   dual_stbuf_write_r;

   logic                   isdccmst_m, isdccmst_r;
   logic [3:0]             stbuf_numvld_any, stbuf_specvld_any;
   logic [1:0]             stbuf_specvld_m, stbuf_specvld_r;

   logic [pt.LSU_SB_BITS-1:$clog2(BYTE_WIDTH)] cmpaddr_hi_m, cmpaddr_lo_m;

   // variables to detect matching from the store queue
   logic [DEPTH-1:0]                 stbuf_match_hi, stbuf_match_lo;
   logic [DEPTH-1:0][BYTE_WIDTH-1:0] stbuf_fwdbyteenvec_hi, stbuf_fwdbyteenvec_lo;
   logic [DATA_WIDTH-1:0]            stbuf_fwddata_hi_pre_m, stbuf_fwddata_lo_pre_m;
   logic [BYTE_WIDTH-1:0]            stbuf_fwdbyteen_hi_pre_m, stbuf_fwdbyteen_lo_pre_m;

   // logic to detect matching from the pipe - needed for store - load forwarding
   logic [BYTE_WIDTH-1:0]  ld_byte_rhit_lo_lo, ld_byte_rhit_hi_lo, ld_byte_rhit_lo_hi, ld_byte_rhit_hi_hi;
   logic                   ld_addr_rhit_lo_lo, ld_addr_rhit_hi_lo, ld_addr_rhit_lo_hi, ld_addr_rhit_hi_hi;

   logic [BYTE_WIDTH-1:0]  ld_byte_hit_lo, ld_byte_rhit_lo;
   logic [BYTE_WIDTH-1:0]  ld_byte_hit_hi, ld_byte_rhit_hi;

   logic [BYTE_WIDTH-1:0]  ldst_byteen_hi_r;
   logic [BYTE_WIDTH-1:0]  ldst_byteen_lo_r;
   // byte_en flowing down
   logic [7:0]             ldst_byteen_r;
   logic [7:0]             ldst_byteen_ext_r;
   // fwd data through the pipe
   logic [31:0]       ld_fwddata_rpipe_lo;
   logic [31:0]       ld_fwddata_rpipe_hi;

   // coalescing signals
   logic [DEPTH-1:0]      store_matchvec_lo_r, store_matchvec_hi_r;
   logic                  store_coalesce_lo_r, store_coalesce_hi_r;

   //----------------------------------------
   // Logic starts here
   //----------------------------------------
   // Create high/low byte enables
   assign store_byteen_ext_r[7:0]           = ldst_byteen_r[7:0] << lsu_addr_r[1:0];
   assign store_byteen_hi_r[BYTE_WIDTH-1:0] = store_byteen_ext_r[7:4] & {4{lsu_pkt_r.store}};
   assign store_byteen_lo_r[BYTE_WIDTH-1:0] = store_byteen_ext_r[3:0] & {4{lsu_pkt_r.store}};

   assign RdPtrPlus1[DEPTH_LOG2-1:0]     = RdPtr[DEPTH_LOG2-1:0] + 1'b1;
   assign WrPtrPlus1[DEPTH_LOG2-1:0]     = WrPtr[DEPTH_LOG2-1:0] + 1'b1;
   assign WrPtrPlus2[DEPTH_LOG2-1:0]     = WrPtr[DEPTH_LOG2-1:0] + 2'b10;

   // ecc error on both hi/lo
   assign dual_stbuf_write_r   = ldst_dual_r & store_stbuf_reqvld_r;
   assign ldst_stbuf_reqvld_r  = ((lsu_commit_r | lsu_pkt_r.dma) & store_stbuf_reqvld_r);

  // Store Buffer coalescing
   for (genvar i=0; i<DEPTH; i++) begin: FindMatchEntry
       assign store_matchvec_lo_r[i] = (stbuf_addr[i][pt.LSU_SB_BITS-1:$clog2(BYTE_WIDTH)] == lsu_addr_r[pt.LSU_SB_BITS-1:$clog2(BYTE_WIDTH)]) & stbuf_vld[i] & ~stbuf_dma_kill[i] & ~stbuf_reset[i];
       assign store_matchvec_hi_r[i] = (stbuf_addr[i][pt.LSU_SB_BITS-1:$clog2(BYTE_WIDTH)] == end_addr_r[pt.LSU_SB_BITS-1:$clog2(BYTE_WIDTH)]) & stbuf_vld[i] & ~stbuf_dma_kill[i] & dual_stbuf_write_r & ~stbuf_reset[i];
   end: FindMatchEntry

   assign store_coalesce_lo_r = |store_matchvec_lo_r[DEPTH-1:0];
   assign store_coalesce_hi_r = |store_matchvec_hi_r[DEPTH-1:0];


   if (pt.DCCM_ENABLE == 1) begin: Gen_dccm_enable
      // Allocate new in this entry if :
      // 1. wrptr, single allocate, lo did not coalesce
      // 2. wrptr, double allocate, lo ^ hi coalesced
      // 3. wrptr + 1, double alloacte, niether lo or hi coalesced
      // Also update if there is a hi or a lo coalesce to this entry
      // Store Buffer instantiation
      for (genvar i=0; i<DEPTH; i++) begin: GenStBuf
         assign stbuf_wr_en[i] = ldst_stbuf_reqvld_r & (
                                   ( (i == WrPtr[DEPTH_LOG2-1:0])      &  ~store_coalesce_lo_r)   |                                                    // Allocate : new Lo
                                   ( (i == WrPtr[DEPTH_LOG2-1:0])      &  dual_stbuf_write_r & ~store_coalesce_hi_r) |                               // Allocate : only 1 new Write Either
                                   ( (i == WrPtrPlus1[DEPTH_LOG2-1:0]) &  dual_stbuf_write_r & ~(store_coalesce_lo_r | store_coalesce_hi_r)) |     // Allocate2 : 2 new so Write Hi
                                   store_matchvec_lo_r[i] | store_matchvec_hi_r[i]);                                                                 // Coalesced Write Lo or Hi
         assign stbuf_reset[i] = (lsu_stbuf_commit_any | stbuf_reqvld_flushed_any) & (i == RdPtr[DEPTH_LOG2-1:0]);

         // Mux select for start/end address
         assign sel_lo[i]                         = ((~ldst_dual_r | store_stbuf_reqvld_r) & (i == WrPtr[DEPTH_LOG2-1:0]) & ~store_coalesce_lo_r) |   // lo allocated new entry
                                                    store_matchvec_lo_r[i];                                                                                                           // lo coalesced in to this entry
         assign stbuf_addrin[i][pt.LSU_SB_BITS-1:0]  = sel_lo[i] ? lsu_addr_r[pt.LSU_SB_BITS-1:0]       : end_addr_r[pt.LSU_SB_BITS-1:0];
         assign stbuf_byteenin[i][BYTE_WIDTH-1:0] = sel_lo[i] ? (stbuf_byteen[i][BYTE_WIDTH-1:0] | store_byteen_lo_r[BYTE_WIDTH-1:0])          : (stbuf_byteen[i][BYTE_WIDTH-1:0] | store_byteen_hi_r[BYTE_WIDTH-1:0]);
         assign stbuf_datain[i][7:0]              = sel_lo[i] ? ((~stbuf_byteen[i][0] | store_byteen_lo_r[0]) ? store_datafn_lo_r[7:0]   : stbuf_data[i][7:0])    :
                                                                ((~stbuf_byteen[i][0] | store_byteen_hi_r[0]) ? store_datafn_hi_r[7:0]   : stbuf_data[i][7:0]);
         assign stbuf_datain[i][15:8]             = sel_lo[i] ? ((~stbuf_byteen[i][1] | store_byteen_lo_r[1]) ? store_datafn_lo_r[15:8]  : stbuf_data[i][15:8])    :
                                                                ((~stbuf_byteen[i][1] | store_byteen_hi_r[1]) ? store_datafn_hi_r[15:8]  : stbuf_data[i][15:8]);
         assign stbuf_datain[i][23:16]            = sel_lo[i] ? ((~stbuf_byteen[i][2] | store_byteen_lo_r[2]) ? store_datafn_lo_r[23:16] : stbuf_data[i][23:16])    :
                                                                ((~stbuf_byteen[i][2] | store_byteen_hi_r[2]) ? store_datafn_hi_r[23:16] : stbuf_data[i][23:16]);
         assign stbuf_datain[i][31:24]            = sel_lo[i] ? ((~stbuf_byteen[i][3] | store_byteen_lo_r[3]) ? store_datafn_lo_r[31:24] : stbuf_data[i][31:24])    :
                                                                ((~stbuf_byteen[i][3] | store_byteen_hi_r[3]) ? store_datafn_hi_r[31:24] : stbuf_data[i][31:24]);

         rvdffsc #(.WIDTH(1))              stbuf_vldff         (.din(1'b1),                                .dout(stbuf_vld[i]),                      .en(stbuf_wr_en[i]), .clear(stbuf_reset[i]), .clk(lsu_free_c2_clk), .*);
         rvdffsc #(.WIDTH(1))              stbuf_killff        (.din(1'b1),                                .dout(stbuf_dma_kill[i]),                 .en(stbuf_dma_kill_en[i]), .clear(stbuf_reset[i]), .clk(lsu_free_c2_clk), .*);
         rvdffe  #(.WIDTH(pt.LSU_SB_BITS)) stbuf_addrff        (.din(stbuf_addrin[i][pt.LSU_SB_BITS-1:0]), .dout(stbuf_addr[i][pt.LSU_SB_BITS-1:0]), .en(stbuf_wr_en[i]), .*);
         rvdffsc #(.WIDTH(BYTE_WIDTH))     stbuf_byteenff      (.din(stbuf_byteenin[i][BYTE_WIDTH-1:0]),   .dout(stbuf_byteen[i][BYTE_WIDTH-1:0]),   .en(stbuf_wr_en[i]), .clear(stbuf_reset[i]), .clk(lsu_stbuf_c1_clk), .*);
         rvdffe  #(.WIDTH(DATA_WIDTH))     stbuf_dataff        (.din(stbuf_datain[i][DATA_WIDTH-1:0]),     .dout(stbuf_data[i][DATA_WIDTH-1:0]),     .en(stbuf_wr_en[i]), .*);
      end
   end else begin: Gen_dccm_disable
      assign stbuf_wr_en[DEPTH-1:0] = '0;
      assign stbuf_reset[DEPTH-1:0] = '0;
      assign stbuf_vld[DEPTH-1:0]   = '0;
      assign stbuf_dma_kill[DEPTH-1:0] = '0;
      assign stbuf_addr[DEPTH-1:0]  = '0;
      assign stbuf_byteen[DEPTH-1:0] = '0;
      assign stbuf_data[DEPTH-1:0]   = '0;
   end

   // Store Buffer drain logic
   assign stbuf_reqvld_flushed_any            = stbuf_vld[RdPtr] & stbuf_dma_kill[RdPtr];
   assign stbuf_reqvld_any                    = stbuf_vld[RdPtr] & ~stbuf_dma_kill[RdPtr] & ~(|stbuf_dma_kill_en[DEPTH-1:0]);  // Don't drain if some kill bit is being set this cycle
   assign stbuf_addr_any[pt.LSU_SB_BITS-1:0]  = stbuf_addr[RdPtr][pt.LSU_SB_BITS-1:0];
   assign stbuf_data_any[DATA_WIDTH-1:0]      = stbuf_data[RdPtr][DATA_WIDTH-1:0];

   // Update the RdPtr/WrPtr logic
   // Need to revert the WrPtr for flush cases. Also revert the pipe WrPtrs
   assign WrPtrEn                  = (ldst_stbuf_reqvld_r  & ~dual_stbuf_write_r & ~(store_coalesce_hi_r | store_coalesce_lo_r))  |  // writing 1 and did not coalesce
                                     (ldst_stbuf_reqvld_r  &  dual_stbuf_write_r & ~(store_coalesce_hi_r & store_coalesce_lo_r));    // writing 2 and atleast 1 did not coalesce
   assign NxtWrPtr[DEPTH_LOG2-1:0] = (ldst_stbuf_reqvld_r & dual_stbuf_write_r & ~(store_coalesce_hi_r | store_coalesce_lo_r)) ? WrPtrPlus2[DEPTH_LOG2-1:0] : WrPtrPlus1[DEPTH_LOG2-1:0];
   assign RdPtrEn                  = lsu_stbuf_commit_any | stbuf_reqvld_flushed_any;
   assign NxtRdPtr[DEPTH_LOG2-1:0] = RdPtrPlus1[DEPTH_LOG2-1:0];

   always_comb begin
      stbuf_numvld_any[3:0] = '0;
      for (int i=0; i<DEPTH; i++) begin
         stbuf_numvld_any[3:0] += {3'b0, stbuf_vld[i]};
      end
   end

    // These go to store buffer to detect full
   assign isdccmst_m = lsu_pkt_m.valid & lsu_pkt_m.store & addr_in_dccm_m & ~lsu_pkt_m.dma;
   assign isdccmst_r = lsu_pkt_r.valid & lsu_pkt_r.store & addr_in_dccm_r & ~lsu_pkt_r.dma;

   assign stbuf_specvld_m[1:0] = {1'b0,isdccmst_m} << (isdccmst_m & ldst_dual_m);
   assign stbuf_specvld_r[1:0] = {1'b0,isdccmst_r} << (isdccmst_r & ldst_dual_r);
   assign stbuf_specvld_any[3:0] = stbuf_numvld_any[3:0] +  {2'b0, stbuf_specvld_m[1:0]} + {2'b0, stbuf_specvld_r[1:0]};

   assign lsu_stbuf_full_any  = (~ldst_dual_d & dec_lsu_valid_raw_d) ? (stbuf_specvld_any[3:0] >= DEPTH) : (stbuf_specvld_any[3:0] >= (DEPTH-1));
   assign lsu_stbuf_empty_any = (stbuf_numvld_any[3:0] == 4'b0);

   // Load forwarding logic from the store queue
   assign cmpaddr_hi_m[pt.LSU_SB_BITS-1:$clog2(BYTE_WIDTH)] = end_addr_m[pt.LSU_SB_BITS-1:$clog2(BYTE_WIDTH)];

   assign cmpaddr_lo_m[pt.LSU_SB_BITS-1:$clog2(BYTE_WIDTH)] = lsu_addr_m[pt.LSU_SB_BITS-1:$clog2(BYTE_WIDTH)];

   always_comb begin: GenLdFwd
      stbuf_fwdbyteen_hi_pre_m[BYTE_WIDTH-1:0]   = '0;
      stbuf_fwdbyteen_lo_pre_m[BYTE_WIDTH-1:0]   = '0;

      for (int i=0; i<DEPTH; i++) begin
         stbuf_match_hi[i] = (stbuf_addr[i][pt.LSU_SB_BITS-1:$clog2(BYTE_WIDTH)] == cmpaddr_hi_m[pt.LSU_SB_BITS-1:$clog2(BYTE_WIDTH)]) & stbuf_vld[i] & ~stbuf_dma_kill[i] & addr_in_dccm_m;
         stbuf_match_lo[i] = (stbuf_addr[i][pt.LSU_SB_BITS-1:$clog2(BYTE_WIDTH)] == cmpaddr_lo_m[pt.LSU_SB_BITS-1:$clog2(BYTE_WIDTH)]) & stbuf_vld[i] & ~stbuf_dma_kill[i] & addr_in_dccm_m;

         // Kill the store buffer entry if there is a dma store since it already updated the dccm
         stbuf_dma_kill_en[i] = (stbuf_match_hi[i] | stbuf_match_lo[i]) & lsu_pkt_m.valid & lsu_pkt_m.dma & lsu_pkt_m.store;

         for (int j=0; j<BYTE_WIDTH; j++) begin
            stbuf_fwdbyteenvec_hi[i][j] = stbuf_match_hi[i] & stbuf_byteen[i][j] & stbuf_vld[i];
            stbuf_fwdbyteen_hi_pre_m[j]  |= stbuf_fwdbyteenvec_hi[i][j];

            stbuf_fwdbyteenvec_lo[i][j] = stbuf_match_lo[i] & stbuf_byteen[i][j] & stbuf_vld[i];
            stbuf_fwdbyteen_lo_pre_m[j]  |= stbuf_fwdbyteenvec_lo[i][j];
         end
      end
   end // block: GenLdFwd

   always_comb begin: GenLdData
      stbuf_fwddata_hi_pre_m[31:0]   = '0;
      stbuf_fwddata_lo_pre_m[31:0]   = '0;

      for (int i=0; i<DEPTH; i++) begin
         stbuf_fwddata_hi_pre_m[31:0] |= {32{stbuf_match_hi[i]}} & stbuf_data[i][31:0];
         stbuf_fwddata_lo_pre_m[31:0] |= {32{stbuf_match_lo[i]}} & stbuf_data[i][31:0];

      end

   end // block: GenLdData

   // Create Hi/Lo signals - needed for the pipe forwarding
   assign ldst_byteen_r[7:0] =  ({8{lsu_pkt_r.by}}    & 8'b0000_0001) |
                                 ({8{lsu_pkt_r.half}}  & 8'b0000_0011) |
                                 ({8{lsu_pkt_r.word}}  & 8'b0000_1111) |
                                 ({8{lsu_pkt_r.dword}} & 8'b1111_1111);

   assign ldst_byteen_ext_r[7:0] = ldst_byteen_r[7:0] << lsu_addr_r[1:0];

   assign ldst_byteen_hi_r[3:0]   = ldst_byteen_ext_r[7:4];
   assign ldst_byteen_lo_r[3:0]   = ldst_byteen_ext_r[3:0];

   assign ld_addr_rhit_lo_lo = (lsu_addr_m[31:2] == lsu_addr_r[31:2]) & lsu_pkt_r.valid & lsu_pkt_r.store & ~lsu_pkt_r.dma;
   assign ld_addr_rhit_lo_hi = (end_addr_m[31:2] == lsu_addr_r[31:2]) & lsu_pkt_r.valid & lsu_pkt_r.store & ~lsu_pkt_r.dma;
   assign ld_addr_rhit_hi_lo = (lsu_addr_m[31:2] == end_addr_r[31:2]) & lsu_pkt_r.valid & lsu_pkt_r.store & ~lsu_pkt_r.dma & dual_stbuf_write_r;
   assign ld_addr_rhit_hi_hi = (end_addr_m[31:2] == end_addr_r[31:2]) & lsu_pkt_r.valid & lsu_pkt_r.store & ~lsu_pkt_r.dma & dual_stbuf_write_r;

   for (genvar i=0; i<BYTE_WIDTH; i++) begin
      assign ld_byte_rhit_lo_lo[i] = ld_addr_rhit_lo_lo & ldst_byteen_lo_r[i];
      assign ld_byte_rhit_lo_hi[i] = ld_addr_rhit_lo_hi & ldst_byteen_lo_r[i];
      assign ld_byte_rhit_hi_lo[i] = ld_addr_rhit_hi_lo & ldst_byteen_hi_r[i];
      assign ld_byte_rhit_hi_hi[i] = ld_addr_rhit_hi_hi & ldst_byteen_hi_r[i];

      assign ld_byte_rhit_lo[i] = ld_byte_rhit_lo_lo[i] | ld_byte_rhit_hi_lo[i];
      assign ld_byte_rhit_hi[i] = ld_byte_rhit_lo_hi[i] | ld_byte_rhit_hi_hi[i];

       assign ld_fwddata_rpipe_lo[(8*i)+7:(8*i)] = ({8{ld_byte_rhit_lo_lo[i]}} & store_data_lo_r[(8*i)+7:(8*i)]) |
                                                     ({8{ld_byte_rhit_hi_lo[i]}} & store_data_hi_r[(8*i)+7:(8*i)]);

       assign ld_fwddata_rpipe_hi[(8*i)+7:(8*i)] = ({8{ld_byte_rhit_lo_hi[i]}} & store_data_lo_r[(8*i)+7:(8*i)]) |
                                                     ({8{ld_byte_rhit_hi_hi[i]}} & store_data_hi_r[(8*i)+7:(8*i)]);

      assign ld_byte_hit_lo[i] = ld_byte_rhit_lo_lo[i] | ld_byte_rhit_hi_lo[i];
      assign ld_byte_hit_hi[i] = ld_byte_rhit_lo_hi[i] | ld_byte_rhit_hi_hi[i];

      assign stbuf_fwdbyteen_hi_m[i] = ld_byte_hit_hi[i] | stbuf_fwdbyteen_hi_pre_m[i];
      assign stbuf_fwdbyteen_lo_m[i] = ld_byte_hit_lo[i] | stbuf_fwdbyteen_lo_pre_m[i];
      // // Pipe vs Store Queue priority
      assign stbuf_fwddata_lo_m[(8*i)+7:(8*i)] = ld_byte_rhit_lo[i]    ? ld_fwddata_rpipe_lo[(8*i)+7:(8*i)] : stbuf_fwddata_lo_pre_m[(8*i)+7:(8*i)];
      // // Pipe vs Store Queue priority
      assign stbuf_fwddata_hi_m[(8*i)+7:(8*i)] = ld_byte_rhit_hi[i]    ? ld_fwddata_rpipe_hi[(8*i)+7:(8*i)] : stbuf_fwddata_hi_pre_m[(8*i)+7:(8*i)];
   end

   // Flops
   rvdffs #(.WIDTH(DEPTH_LOG2)) WrPtrff (.din(NxtWrPtr[DEPTH_LOG2-1:0]), .dout(WrPtr[DEPTH_LOG2-1:0]), .en(WrPtrEn), .clk(lsu_stbuf_c1_clk), .*);
   rvdffs #(.WIDTH(DEPTH_LOG2)) RdPtrff (.din(NxtRdPtr[DEPTH_LOG2-1:0]), .dout(RdPtr[DEPTH_LOG2-1:0]), .en(RdPtrEn), .clk(lsu_stbuf_c1_clk), .*);

`ifdef RV_ASSERT_ON

   assert_stbuf_overflow: assert #0 (stbuf_specvld_any[2:0] <= DEPTH);
   property stbuf_wren_store_dccm;
      @(posedge clk)  disable iff(~rst_l) (|stbuf_wr_en[DEPTH-1:0]) |-> (lsu_pkt_r.valid & lsu_pkt_r.store & addr_in_dccm_r);
   endproperty
   assert_stbuf_wren_store_dccm: assert property (stbuf_wren_store_dccm) else
      $display("Illegal store buffer write");

`endif

endmodule

