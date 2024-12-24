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
// Function: lsu interface with interface queue
// Comments:
//
//********************************************************************************

module el2_lsu_bus_buffer
import el2_pkg::*;
#(
`include "el2_param.vh"
 )(
   input logic                          clk,                                // Clock only while core active.  Through one clock header.  For flops with    second clock header built in.  Connected to ACTIVE_L2CLK.
   input logic                          clk_override,                       // Override non-functional clock gating
   input logic                          rst_l,                              // reset, active low
   // Excluding scan_mode from coverage as its usage is determined by the integrator of the VeeR core.
   /*pragma coverage off*/
   input logic                          scan_mode,                          // scan mode
   /*pragma coverage on*/
   input logic                          dec_tlu_external_ldfwd_disable,     // disable load to load forwarding for externals
   input logic                          dec_tlu_wb_coalescing_disable,      // disable write buffer coalescing
   input logic                          dec_tlu_sideeffect_posted_disable,  // Don't block the sideeffect load store to the bus
   input logic                          dec_tlu_force_halt,

   // various clocks needed for the bus reads and writes
   input logic                          lsu_bus_obuf_c1_clken,
   input logic                          lsu_busm_clken,
   input logic                          lsu_c2_r_clk,
   input logic                          lsu_bus_ibuf_c1_clk,
   input logic                          lsu_bus_obuf_c1_clk,
   input logic                          lsu_bus_buf_c1_clk,
   input logic                          lsu_free_c2_clk,
   input logic                          lsu_busm_clk,


   input logic                          dec_lsu_valid_raw_d,            // Raw valid for address computation
   input el2_lsu_pkt_t                 lsu_pkt_m,                      // lsu packet flowing down the pipe
   input el2_lsu_pkt_t                 lsu_pkt_r,                      // lsu packet flowing down the pipe

   input logic [31:0]                   lsu_addr_m,                     // lsu address flowing down the pipe
   input logic [31:0]                   end_addr_m,                     // lsu address flowing down the pipe
   input logic [31:0]                   lsu_addr_r,                     // lsu address flowing down the pipe
   input logic [31:0]                   end_addr_r,                     // lsu address flowing down the pipe
   input logic [31:0]                   store_data_r,                   // store data flowing down the pipe

   input logic                          no_word_merge_r,                // r store doesn't need to wait in ibuf since it will not coalesce
   input logic                          no_dword_merge_r,               // r store doesn't need to wait in ibuf since it will not coalesce
   input logic                          lsu_busreq_m,                   // bus request is in m
   output logic                         lsu_busreq_r,                   // bus request is in r
   input logic                          ld_full_hit_m,                  // load can get all its byte from a write buffer entry
   input logic                          flush_m_up,                     // flush
   input logic                          flush_r,                        // flush
   input logic                          lsu_commit_r,                   // lsu instruction in r commits
   input logic                          is_sideeffects_r,               // lsu attribute is side_effects
   input logic                          ldst_dual_d,                    // load/store is unaligned at 32 bit boundary
   input logic                          ldst_dual_m,                    // load/store is unaligned at 32 bit boundary
   input logic                          ldst_dual_r,                    // load/store is unaligned at 32 bit boundary

   input logic [7:0]                    ldst_byteen_ext_m,              // HI and LO signals

   output logic                         lsu_bus_buffer_pend_any,          // bus buffer has a pending bus entry
   output logic                         lsu_bus_buffer_full_any,          // bus buffer is full
   output logic                         lsu_bus_buffer_empty_any,         // bus buffer is empty

   output logic [3:0]                   ld_byte_hit_buf_lo, ld_byte_hit_buf_hi,    // Byte enables for forwarding data
   output logic [31:0]                  ld_fwddata_buf_lo, ld_fwddata_buf_hi,      // load forwarding data

   output logic                         lsu_imprecise_error_load_any,     // imprecise load bus error
   output logic                         lsu_imprecise_error_store_any,    // imprecise store bus error
   output logic [31:0]                  lsu_imprecise_error_addr_any,     // address of the imprecise error

   // Non-blocking loads
   output logic                               lsu_nonblock_load_valid_m,     // there is an external load -> put in the cam
   output logic [pt.LSU_NUM_NBLOAD_WIDTH-1:0] lsu_nonblock_load_tag_m,       // the tag of the external non block load
   output logic                               lsu_nonblock_load_inv_r,       // invalidate signal for the cam entry for non block loads
   output logic [pt.LSU_NUM_NBLOAD_WIDTH-1:0] lsu_nonblock_load_inv_tag_r,   // tag of the enrty which needs to be invalidated
   output logic                               lsu_nonblock_load_data_valid,  // the non block is valid - sending information back to the cam
   output logic                               lsu_nonblock_load_data_error,  // non block load has an error
   output logic [pt.LSU_NUM_NBLOAD_WIDTH-1:0] lsu_nonblock_load_data_tag,    // the tag of the non block load sending the data/error
   output logic [31:0]                        lsu_nonblock_load_data,        // Data of the non block load

   // PMU events
   output logic                         lsu_pmu_bus_trxn,
   output logic                         lsu_pmu_bus_misaligned,
   output logic                         lsu_pmu_bus_error,
   output logic                         lsu_pmu_bus_busy,

   // AXI Write Channels
   output logic                            lsu_axi_awvalid,
   input  logic                            lsu_axi_awready,
   output logic [pt.LSU_BUS_TAG-1:0]       lsu_axi_awid,
   output logic [31:0]                     lsu_axi_awaddr,
   output logic [3:0]                      lsu_axi_awregion,
   /* exclude signals that are tied to constant value in this file */
   /*pragma coverage off*/
   output logic [7:0]                      lsu_axi_awlen,
   /*pragma coverage on*/
   output logic [2:0]                      lsu_axi_awsize,
   /* exclude signals that are tied to constant value in this file */
   /*pragma coverage off*/
   output logic [1:0]                      lsu_axi_awburst,
   output logic                            lsu_axi_awlock,
   /*pragma coverage on*/
   output logic [3:0]                      lsu_axi_awcache,
   /* exclude signals that are tied to constant value in this file */
   /*pragma coverage off*/
   output logic [2:0]                      lsu_axi_awprot,
   output logic [3:0]                      lsu_axi_awqos,
   /*pragma coverage on*/

   output logic                            lsu_axi_wvalid,
   input  logic                            lsu_axi_wready,
   output logic [63:0]                     lsu_axi_wdata,
   output logic [7:0]                      lsu_axi_wstrb,
   output logic                            lsu_axi_wlast,

   input  logic                            lsu_axi_bvalid,
   /* exclude signals that are tied to constant value in this file */
   /*pragma coverage off*/
   output logic                            lsu_axi_bready,
   /*pragma coverage on*/
   input  logic [1:0]                      lsu_axi_bresp,
   input  logic [pt.LSU_BUS_TAG-1:0]       lsu_axi_bid,

   // AXI Read Channels
   output logic                            lsu_axi_arvalid,
   input  logic                            lsu_axi_arready,
   output logic [pt.LSU_BUS_TAG-1:0]       lsu_axi_arid,
   output logic [31:0]                     lsu_axi_araddr,
   output logic [3:0]                      lsu_axi_arregion,
   /* exclude signals that are tied to constant value in this file */
   /*pragma coverage off*/
   output logic [7:0]                      lsu_axi_arlen,
   /*pragma coverage on*/
   output logic [2:0]                      lsu_axi_arsize,
   /* exclude signals that are tied to constant value in this file */
   /*pragma coverage off*/
   output logic [1:0]                      lsu_axi_arburst,
   output logic                            lsu_axi_arlock,
   /*pragma coverage on*/
   output logic [3:0]                      lsu_axi_arcache,
   /* exclude signals that are tied to constant value in this file */
   /*pragma coverage off*/
   output logic [2:0]                      lsu_axi_arprot,
   output logic [3:0]                      lsu_axi_arqos,
   /*pragma coverage on*/

   input  logic                            lsu_axi_rvalid,
   /* exclude signals that are tied to constant value in this file */
   /*pragma coverage off*/
   output logic                            lsu_axi_rready,
   /*pragma coverage on*/
   input  logic [pt.LSU_BUS_TAG-1:0]       lsu_axi_rid,
   input  logic [63:0]                     lsu_axi_rdata,
   input  logic [1:0]                      lsu_axi_rresp,

   input logic                             lsu_bus_clk_en,
   input logic                             lsu_bus_clk_en_q

);

   // For Ld: IDLE -> START_WAIT -> CMD -> RESP -> DONE_PARTIAL(?) -> DONE_WAIT(?) -> DONE -> IDLE
   // For St: IDLE -> START_WAIT -> CMD -> RESP(?) -> IDLE
   typedef enum logic [2:0] {IDLE=3'b000, START_WAIT=3'b001, CMD=3'b010, RESP=3'b011, DONE_PARTIAL=3'b100, DONE_WAIT=3'b101, DONE=3'b110} state_t;

   localparam DEPTH     = pt.LSU_NUM_NBLOAD;
   localparam DEPTH_LOG2 = pt.LSU_NUM_NBLOAD_WIDTH;
   localparam TIMER     = 8;   // This can be only power of 2
   localparam TIMER_MAX = TIMER - 1;  // Maximum value of timer
   localparam TIMER_LOG2 = (TIMER < 2) ? 1 : $clog2(TIMER);

   logic [3:0]                          ldst_byteen_hi_m, ldst_byteen_lo_m;
   logic [DEPTH-1:0]                    ld_addr_hitvec_lo, ld_addr_hitvec_hi;
   logic [3:0][DEPTH-1:0]               ld_byte_hitvec_lo, ld_byte_hitvec_hi;
   logic [3:0][DEPTH-1:0]               ld_byte_hitvecfn_lo, ld_byte_hitvecfn_hi;

   logic                                ld_addr_ibuf_hit_lo, ld_addr_ibuf_hit_hi;
   logic [3:0]                          ld_byte_ibuf_hit_lo, ld_byte_ibuf_hit_hi;

   logic [3:0]                          ldst_byteen_r;
   logic [3:0]                          ldst_byteen_hi_r, ldst_byteen_lo_r;
   logic [31:0]                         store_data_hi_r, store_data_lo_r;
   logic                                is_aligned_r;                   // Aligned load/store
   logic                                ldst_samedw_r;

   logic                                lsu_nonblock_load_valid_r;
   logic [31:0]                         lsu_nonblock_load_data_hi, lsu_nonblock_load_data_lo, lsu_nonblock_data_unalgn;
   logic [1:0]                          lsu_nonblock_addr_offset;
   logic [1:0]                          lsu_nonblock_sz;
   logic                                lsu_nonblock_unsign;
   logic                                lsu_nonblock_load_data_ready;

   logic [DEPTH-1:0]                    CmdPtr0Dec, CmdPtr1Dec;
   logic [DEPTH-1:0]                    RspPtrDec;
   logic [DEPTH_LOG2-1:0]               CmdPtr0, CmdPtr1;
   logic [DEPTH_LOG2-1:0]               RspPtr;
   logic [DEPTH_LOG2-1:0]               WrPtr0_m, WrPtr0_r;
   logic [DEPTH_LOG2-1:0]               WrPtr1_m, WrPtr1_r;
   logic                                found_wrptr0, found_wrptr1, found_cmdptr0, found_cmdptr1;
   logic [3:0]                          buf_numvld_any, buf_numvld_wrcmd_any, buf_numvld_cmd_any, buf_numvld_pend_any;
   logic                                any_done_wait_state;
   logic                                bus_sideeffect_pend;
   logic                                bus_coalescing_disable;

   logic                                bus_addr_match_pending;
   logic                                bus_cmd_sent, bus_cmd_ready;
   logic                                bus_wcmd_sent, bus_wdata_sent;
   logic                                bus_rsp_read, bus_rsp_write;
   logic [pt.LSU_BUS_TAG-1:0]           bus_rsp_read_tag, bus_rsp_write_tag;
   logic                                bus_rsp_read_error, bus_rsp_write_error;
   logic [63:0]                         bus_rsp_rdata;

   // Bus buffer signals
   state_t [DEPTH-1:0]                  buf_state;
   logic   [DEPTH-1:0][1:0]             buf_sz;
   logic   [DEPTH-1:0][31:0]            buf_addr;
   logic   [DEPTH-1:0][3:0]             buf_byteen;
   logic   [DEPTH-1:0]                  buf_sideeffect;
   logic   [DEPTH-1:0]                  buf_write;
   logic   [DEPTH-1:0]                  buf_unsign;
   logic   [DEPTH-1:0]                  buf_dual;
   logic   [DEPTH-1:0]                  buf_samedw;
   logic   [DEPTH-1:0]                  buf_nomerge;
   logic   [DEPTH-1:0]                  buf_dualhi;
   logic   [DEPTH-1:0][DEPTH_LOG2-1:0]  buf_dualtag;
   logic   [DEPTH-1:0]                  buf_ldfwd;
   logic   [DEPTH-1:0][DEPTH_LOG2-1:0]  buf_ldfwdtag;
   logic   [DEPTH-1:0]                  buf_error;
   logic   [DEPTH-1:0][31:0]            buf_data;
   logic   [DEPTH-1:0][DEPTH-1:0]       buf_age, buf_age_younger;
   logic   [DEPTH-1:0][DEPTH-1:0]       buf_rspage, buf_rsp_pickage;

   state_t [DEPTH-1:0]                  buf_nxtstate;
   logic   [DEPTH-1:0]                  buf_rst;
   logic   [DEPTH-1:0]                  buf_state_en;
   logic   [DEPTH-1:0]                  buf_cmd_state_bus_en;
   logic   [DEPTH-1:0]                  buf_resp_state_bus_en;
   logic   [DEPTH-1:0]                  buf_state_bus_en;
   logic   [DEPTH-1:0]                  buf_dual_in;
   logic   [DEPTH-1:0]                  buf_samedw_in;
   logic   [DEPTH-1:0]                  buf_nomerge_in;
   logic   [DEPTH-1:0]                  buf_sideeffect_in;
   logic   [DEPTH-1:0]                  buf_unsign_in;
   logic   [DEPTH-1:0][1:0]             buf_sz_in;
   logic   [DEPTH-1:0]                  buf_write_in;
   logic   [DEPTH-1:0]                  buf_wr_en;
   logic   [DEPTH-1:0]                  buf_dualhi_in;
   logic   [DEPTH-1:0][DEPTH_LOG2-1:0]  buf_dualtag_in;
   logic   [DEPTH-1:0]                  buf_ldfwd_en;
   logic   [DEPTH-1:0]                  buf_ldfwd_in;
   logic   [DEPTH-1:0][DEPTH_LOG2-1:0]  buf_ldfwdtag_in;
   logic   [DEPTH-1:0][3:0]             buf_byteen_in;
   logic   [DEPTH-1:0][31:0]            buf_addr_in;
   logic   [DEPTH-1:0][31:0]            buf_data_in;
   logic   [DEPTH-1:0]                  buf_error_en;
   logic   [DEPTH-1:0]                  buf_data_en;
   logic   [DEPTH-1:0][DEPTH-1:0]       buf_age_in;
   logic   [DEPTH-1:0][DEPTH-1:0]       buf_ageQ;
   logic   [DEPTH-1:0][DEPTH-1:0]       buf_rspage_set;
   logic   [DEPTH-1:0][DEPTH-1:0]       buf_rspage_in;
   logic   [DEPTH-1:0][DEPTH-1:0]       buf_rspageQ;

   // Input buffer signals
   logic                               ibuf_valid;
   logic                               ibuf_dual;
   logic                               ibuf_samedw;
   logic                               ibuf_nomerge;
   logic [DEPTH_LOG2-1:0]              ibuf_tag;
   logic [DEPTH_LOG2-1:0]              ibuf_dualtag;
   logic                               ibuf_sideeffect;
   logic                               ibuf_unsign;
   logic                               ibuf_write;
   logic [1:0]                         ibuf_sz;
   logic [3:0]                         ibuf_byteen;
   logic [31:0]                        ibuf_addr;
   logic [31:0]                        ibuf_data;
   logic [TIMER_LOG2-1:0]              ibuf_timer;

   logic                               ibuf_byp;
   logic                               ibuf_wr_en;
   logic                               ibuf_rst;
   logic                               ibuf_force_drain;
   logic                               ibuf_drain_vld;
   logic [DEPTH-1:0]                   ibuf_drainvec_vld;
   logic [DEPTH_LOG2-1:0]              ibuf_tag_in;
   logic [DEPTH_LOG2-1:0]              ibuf_dualtag_in;
   logic [1:0]                         ibuf_sz_in;
   logic [31:0]                        ibuf_addr_in;
   logic [3:0]                         ibuf_byteen_in;
   logic [31:0]                        ibuf_data_in;
   logic [TIMER_LOG2-1:0]              ibuf_timer_in;
   logic [3:0]                         ibuf_byteen_out;
   logic [31:0]                        ibuf_data_out;
   logic                               ibuf_merge_en, ibuf_merge_in;

   // Output buffer signals
   logic                               obuf_valid;
   logic                               obuf_write;
   logic                               obuf_nosend;
   logic                               obuf_rdrsp_pend;
   logic                               obuf_sideeffect;
   logic [31:0]                        obuf_addr;
   logic [63:0]                        obuf_data;
   logic [1:0]                         obuf_sz;
   logic [7:0]                         obuf_byteen;
   logic                               obuf_merge;
   logic                               obuf_cmd_done, obuf_data_done;
   logic [pt.LSU_BUS_TAG-1:0]          obuf_tag0;
   logic [pt.LSU_BUS_TAG-1:0]          obuf_tag1;
   logic [pt.LSU_BUS_TAG-1:0]          obuf_rdrsp_tag;

   logic                               ibuf_buf_byp;
   logic                               obuf_force_wr_en;
   logic                               obuf_wr_wait;
   logic                               obuf_wr_en, obuf_wr_enQ;
   logic                               obuf_rst;
   logic                               obuf_write_in;
   logic                               obuf_nosend_in;
   logic                               obuf_rdrsp_pend_en;
   logic                               obuf_rdrsp_pend_in;
   logic                               obuf_sideeffect_in;
   logic                               obuf_aligned_in;
   logic [31:0]                        obuf_addr_in;
   logic [63:0]                        obuf_data_in;
   logic [1:0]                         obuf_sz_in;
   logic [7:0]                         obuf_byteen_in;
   logic                               obuf_merge_in;
   logic                               obuf_cmd_done_in, obuf_data_done_in;
   logic [pt.LSU_BUS_TAG-1:0]          obuf_tag0_in;
   logic [pt.LSU_BUS_TAG-1:0]          obuf_tag1_in;
   logic [pt.LSU_BUS_TAG-1:0]          obuf_rdrsp_tag_in;

   logic                               obuf_merge_en;
   logic [TIMER_LOG2-1:0]              obuf_wr_timer, obuf_wr_timer_in;
   logic [7:0]                         obuf_byteen0_in, obuf_byteen1_in;
   logic [63:0]                        obuf_data0_in, obuf_data1_in;

   logic                               lsu_axi_awvalid_q, lsu_axi_awready_q;
   logic                               lsu_axi_wvalid_q, lsu_axi_wready_q;
   logic                               lsu_axi_arvalid_q, lsu_axi_arready_q;
   logic                               lsu_axi_bvalid_q, lsu_axi_bready_q;
   logic                               lsu_axi_rvalid_q, lsu_axi_rready_q;
   logic [pt.LSU_BUS_TAG-1:0]          lsu_axi_bid_q, lsu_axi_rid_q;
   logic [1:0]                         lsu_axi_bresp_q, lsu_axi_rresp_q;
   logic [pt.LSU_BUS_TAG-1:0]          lsu_imprecise_error_store_tag;
   logic [63:0]                        lsu_axi_rdata_q;

   //------------------------------------------------------------------------------
   // Load forwarding logic start
   //------------------------------------------------------------------------------

   // Function to do 8 to 3 bit encoding
   function automatic logic [2:0] f_Enc8to3;
      input logic [7:0] Dec_value;

      logic [2:0]       Enc_value;
      Enc_value[0] = Dec_value[1] | Dec_value[3] | Dec_value[5] | Dec_value[7];
      Enc_value[1] = Dec_value[2] | Dec_value[3] | Dec_value[6] | Dec_value[7];
      Enc_value[2] = Dec_value[4] | Dec_value[5] | Dec_value[6] | Dec_value[7];

      return Enc_value[2:0];
   endfunction // f_Enc8to3

   // Buffer hit logic for bus load forwarding
   assign ldst_byteen_hi_m[3:0]   = ldst_byteen_ext_m[7:4];
   assign ldst_byteen_lo_m[3:0]   = ldst_byteen_ext_m[3:0];
   for (genvar i=0; i<DEPTH; i++) begin
      assign ld_addr_hitvec_lo[i] = (lsu_addr_m[31:2] == buf_addr[i][31:2]) & buf_write[i] & (buf_state[i] != IDLE) & lsu_busreq_m;
      assign ld_addr_hitvec_hi[i] = (end_addr_m[31:2] == buf_addr[i][31:2]) & buf_write[i] & (buf_state[i] != IDLE) & lsu_busreq_m;
   end

   for (genvar j=0; j<4; j++) begin
     assign ld_byte_hit_buf_lo[j] = |(ld_byte_hitvecfn_lo[j]) | ld_byte_ibuf_hit_lo[j];
     assign ld_byte_hit_buf_hi[j] = |(ld_byte_hitvecfn_hi[j]) | ld_byte_ibuf_hit_hi[j];
     for (genvar i=0; i<DEPTH; i++) begin
         assign ld_byte_hitvec_lo[j][i] = ld_addr_hitvec_lo[i] & buf_byteen[i][j] & ldst_byteen_lo_m[j];
         assign ld_byte_hitvec_hi[j][i] = ld_addr_hitvec_hi[i] & buf_byteen[i][j] & ldst_byteen_hi_m[j];

         assign ld_byte_hitvecfn_lo[j][i] = ld_byte_hitvec_lo[j][i] & ~(|(ld_byte_hitvec_lo[j] & buf_age_younger[i])) & ~ld_byte_ibuf_hit_lo[j];  // Kill the byte enable if younger entry exists or byte exists in ibuf
         assign ld_byte_hitvecfn_hi[j][i] = ld_byte_hitvec_hi[j][i] & ~(|(ld_byte_hitvec_hi[j] & buf_age_younger[i])) & ~ld_byte_ibuf_hit_hi[j];  // Kill the byte enable if younger entry exists or byte exists in ibuf
      end
   end

   // Hit in the ibuf
   assign ld_addr_ibuf_hit_lo = (lsu_addr_m[31:2] == ibuf_addr[31:2]) & ibuf_write & ibuf_valid & lsu_busreq_m;
   assign ld_addr_ibuf_hit_hi = (end_addr_m[31:2] == ibuf_addr[31:2]) & ibuf_write & ibuf_valid & lsu_busreq_m;

   for (genvar i=0; i<4; i++) begin
      assign ld_byte_ibuf_hit_lo[i] = ld_addr_ibuf_hit_lo & ibuf_byteen[i] & ldst_byteen_lo_m[i];
      assign ld_byte_ibuf_hit_hi[i] = ld_addr_ibuf_hit_hi & ibuf_byteen[i] & ldst_byteen_hi_m[i];
   end

   always_comb begin
      ld_fwddata_buf_lo[31:0] = {{8{ld_byte_ibuf_hit_lo[3]}},{8{ld_byte_ibuf_hit_lo[2]}},{8{ld_byte_ibuf_hit_lo[1]}},{8{ld_byte_ibuf_hit_lo[0]}}} & ibuf_data[31:0];
      ld_fwddata_buf_hi[31:0] = {{8{ld_byte_ibuf_hit_hi[3]}},{8{ld_byte_ibuf_hit_hi[2]}},{8{ld_byte_ibuf_hit_hi[1]}},{8{ld_byte_ibuf_hit_hi[0]}}} & ibuf_data[31:0];
      for (int i=0; i<DEPTH; i++) begin
         ld_fwddata_buf_lo[7:0]   |= {8{ld_byte_hitvecfn_lo[0][i]}} & buf_data[i][7:0];
         ld_fwddata_buf_lo[15:8]  |= {8{ld_byte_hitvecfn_lo[1][i]}} & buf_data[i][15:8];
         ld_fwddata_buf_lo[23:16] |= {8{ld_byte_hitvecfn_lo[2][i]}} & buf_data[i][23:16];
         ld_fwddata_buf_lo[31:24] |= {8{ld_byte_hitvecfn_lo[3][i]}} & buf_data[i][31:24];

         ld_fwddata_buf_hi[7:0]   |= {8{ld_byte_hitvecfn_hi[0][i]}} & buf_data[i][7:0];
         ld_fwddata_buf_hi[15:8]  |= {8{ld_byte_hitvecfn_hi[1][i]}} & buf_data[i][15:8];
         ld_fwddata_buf_hi[23:16] |= {8{ld_byte_hitvecfn_hi[2][i]}} & buf_data[i][23:16];
         ld_fwddata_buf_hi[31:24] |= {8{ld_byte_hitvecfn_hi[3][i]}} & buf_data[i][31:24];
      end
   end

   //------------------------------------------------------------------------------
   // Load forwarding logic end
   //------------------------------------------------------------------------------

   assign bus_coalescing_disable = dec_tlu_wb_coalescing_disable | pt.BUILD_AHB_LITE;

   // Get the hi/lo byte enable
   assign ldst_byteen_r[3:0] = ({4{lsu_pkt_r.by}}   & 4'b0001) |
                                 ({4{lsu_pkt_r.half}} & 4'b0011) |
                                 ({4{lsu_pkt_r.word}} & 4'b1111);

   assign {ldst_byteen_hi_r[3:0], ldst_byteen_lo_r[3:0]} = {4'b0,ldst_byteen_r[3:0]} << lsu_addr_r[1:0];
   assign {store_data_hi_r[31:0], store_data_lo_r[31:0]} = {32'b0,store_data_r[31:0]} << 8*lsu_addr_r[1:0];
   assign ldst_samedw_r    = (lsu_addr_r[3] == end_addr_r[3]);
   assign is_aligned_r    = (lsu_pkt_r.word & (lsu_addr_r[1:0] == 2'b0)) |
                            (lsu_pkt_r.half & (lsu_addr_r[0] == 1'b0))   |
                            lsu_pkt_r.by;

   //------------------------------------------------------------------------------
   // Input buffer logic starts here
   //------------------------------------------------------------------------------

   assign ibuf_byp = lsu_busreq_r & (lsu_pkt_r.load | no_word_merge_r) & ~ibuf_valid;
   assign ibuf_wr_en = lsu_busreq_r & lsu_commit_r & ~ibuf_byp;
   assign ibuf_rst   = (ibuf_drain_vld & ~ibuf_wr_en) | dec_tlu_force_halt;
   assign ibuf_force_drain = lsu_busreq_m & ~lsu_busreq_r & ibuf_valid & (lsu_pkt_m.load | (ibuf_addr[31:2] != lsu_addr_m[31:2]));  // Move the ibuf to buf if there is a non-colaescable ld/st in m but nothing in r
   assign ibuf_drain_vld = ibuf_valid & (((ibuf_wr_en | (ibuf_timer == TIMER_MAX)) & ~(ibuf_merge_en & ibuf_merge_in)) | ibuf_byp | ibuf_force_drain | ibuf_sideeffect | ~ibuf_write | bus_coalescing_disable);
   assign ibuf_tag_in[DEPTH_LOG2-1:0] = (ibuf_merge_en & ibuf_merge_in) ? ibuf_tag[DEPTH_LOG2-1:0] : (ldst_dual_r ? WrPtr1_r : WrPtr0_r);
   assign ibuf_dualtag_in[DEPTH_LOG2-1:0] = WrPtr0_r;
   assign ibuf_sz_in[1:0]   = {lsu_pkt_r.word, lsu_pkt_r.half};
   assign ibuf_addr_in[31:0] = ldst_dual_r ? end_addr_r[31:0] : lsu_addr_r[31:0];
   assign ibuf_byteen_in[3:0] = (ibuf_merge_en & ibuf_merge_in) ? (ibuf_byteen[3:0] | ldst_byteen_lo_r[3:0]) : (ldst_dual_r ? ldst_byteen_hi_r[3:0] : ldst_byteen_lo_r[3:0]);
   for (genvar i=0; i<4; i++) begin
      assign ibuf_data_in[(8*i)+7:(8*i)] = (ibuf_merge_en & ibuf_merge_in) ? (ldst_byteen_lo_r[i] ? store_data_lo_r[(8*i)+7:(8*i)] : ibuf_data[(8*i)+7:(8*i)]) :
                                                                             (ldst_dual_r ? store_data_hi_r[(8*i)+7:(8*i)] : store_data_lo_r[(8*i)+7:(8*i)]);
   end
   assign ibuf_timer_in = ibuf_wr_en ? '0 : (ibuf_timer < TIMER_MAX) ? (ibuf_timer + 1'b1) : ibuf_timer;


   assign ibuf_merge_en = lsu_busreq_r & lsu_commit_r & lsu_pkt_r.store & ibuf_valid & ibuf_write & (lsu_addr_r[31:2] == ibuf_addr[31:2]) & ~is_sideeffects_r & ~bus_coalescing_disable;
   assign ibuf_merge_in = ~ldst_dual_r;   // If it's a unaligned store, merge needs to happen on the way out of ibuf

   // ibuf signals going to bus buffer after merging
   for (genvar i=0; i<4; i++) begin
      assign ibuf_byteen_out[i] = (ibuf_merge_en & ~ibuf_merge_in) ? (ibuf_byteen[i] | ldst_byteen_lo_r[i]) : ibuf_byteen[i];
      assign ibuf_data_out[(8*i)+7:(8*i)] = (ibuf_merge_en & ~ibuf_merge_in) ? (ldst_byteen_lo_r[i] ? store_data_lo_r[(8*i)+7:(8*i)] : ibuf_data[(8*i)+7:(8*i)]) :
                                                                                                        ibuf_data[(8*i)+7:(8*i)];
   end

   rvdffsc #(.WIDTH(1))              ibuf_valid_ff     (.din(1'b1),                      .dout(ibuf_valid),      .en(ibuf_wr_en), .clear(ibuf_rst), .clk(lsu_free_c2_clk), .*);
   rvdffs  #(.WIDTH(DEPTH_LOG2))     ibuf_tagff        (.din(ibuf_tag_in),               .dout(ibuf_tag),        .en(ibuf_wr_en),                   .clk(lsu_bus_ibuf_c1_clk), .*);
   rvdffs  #(.WIDTH(DEPTH_LOG2))     ibuf_dualtagff    (.din(ibuf_dualtag_in),           .dout(ibuf_dualtag),    .en(ibuf_wr_en),                   .clk(lsu_bus_ibuf_c1_clk), .*);
   rvdffs  #(.WIDTH(1))              ibuf_dualff       (.din(ldst_dual_r),               .dout(ibuf_dual),       .en(ibuf_wr_en),                   .clk(lsu_bus_ibuf_c1_clk), .*);
   rvdffs  #(.WIDTH(1))              ibuf_samedwff     (.din(ldst_samedw_r),             .dout(ibuf_samedw),     .en(ibuf_wr_en),                   .clk(lsu_bus_ibuf_c1_clk), .*);
   rvdffs  #(.WIDTH(1))              ibuf_nomergeff    (.din(no_dword_merge_r),          .dout(ibuf_nomerge),    .en(ibuf_wr_en),                   .clk(lsu_bus_ibuf_c1_clk), .*);
   rvdffs  #(.WIDTH(1))              ibuf_sideeffectff (.din(is_sideeffects_r),          .dout(ibuf_sideeffect), .en(ibuf_wr_en),                   .clk(lsu_bus_ibuf_c1_clk), .*);
   rvdffs  #(.WIDTH(1))              ibuf_unsignff     (.din(lsu_pkt_r.unsign),          .dout(ibuf_unsign),     .en(ibuf_wr_en),                   .clk(lsu_bus_ibuf_c1_clk), .*);
   rvdffs  #(.WIDTH(1))              ibuf_writeff      (.din(lsu_pkt_r.store),           .dout(ibuf_write),      .en(ibuf_wr_en),                   .clk(lsu_bus_ibuf_c1_clk), .*);
   rvdffs  #(.WIDTH(2))              ibuf_szff         (.din(ibuf_sz_in[1:0]),           .dout(ibuf_sz),         .en(ibuf_wr_en),                   .clk(lsu_bus_ibuf_c1_clk), .*);
   rvdffe  #(.WIDTH(32))             ibuf_addrff       (.din(ibuf_addr_in[31:0]),        .dout(ibuf_addr),       .en(ibuf_wr_en),                                              .*);
   rvdffs  #(.WIDTH(4))              ibuf_byteenff     (.din(ibuf_byteen_in[3:0]),       .dout(ibuf_byteen),     .en(ibuf_wr_en),                   .clk(lsu_bus_ibuf_c1_clk), .*);
   rvdffe  #(.WIDTH(32))             ibuf_dataff       (.din(ibuf_data_in[31:0]),        .dout(ibuf_data),       .en(ibuf_wr_en),                                              .*);
   rvdff   #(.WIDTH(TIMER_LOG2))     ibuf_timerff      (.din(ibuf_timer_in),             .dout(ibuf_timer),                                         .clk(lsu_free_c2_clk),     .*);


   //------------------------------------------------------------------------------
   // Input buffer logic ends here
   //------------------------------------------------------------------------------


   //------------------------------------------------------------------------------
   // Output buffer logic starts here
   //------------------------------------------------------------------------------

   assign obuf_wr_wait = (buf_numvld_wrcmd_any[3:0] == 4'b1) & (buf_numvld_cmd_any[3:0] == 4'b1) & (obuf_wr_timer != TIMER_MAX) &
                         ~bus_coalescing_disable & ~buf_nomerge[CmdPtr0] & ~buf_sideeffect[CmdPtr0] & ~obuf_force_wr_en;
   assign obuf_wr_timer_in = obuf_wr_en ? 3'b0: (((buf_numvld_cmd_any > 4'b0) & (obuf_wr_timer < TIMER_MAX)) ? (obuf_wr_timer + 1'b1) : obuf_wr_timer);
   assign obuf_force_wr_en = lsu_busreq_m & ~lsu_busreq_r & ~ibuf_valid & (buf_numvld_cmd_any[3:0] == 4'b1) & (lsu_addr_m[31:2] != buf_addr[CmdPtr0][31:2]);   // Entry in m can't merge with entry going to obuf and there is no entry in between
   assign ibuf_buf_byp = ibuf_byp & (buf_numvld_pend_any[3:0] == 4'b0) & (~lsu_pkt_r.store | no_dword_merge_r);

   assign obuf_wr_en = ((ibuf_buf_byp & lsu_commit_r & ~(is_sideeffects_r & bus_sideeffect_pend)) |
                        ((buf_state[CmdPtr0] == CMD) & found_cmdptr0 & ~buf_cmd_state_bus_en[CmdPtr0] & ~(buf_sideeffect[CmdPtr0] & bus_sideeffect_pend) &
                         (~(buf_dual[CmdPtr0] & buf_samedw[CmdPtr0] & ~buf_write[CmdPtr0]) | found_cmdptr1 | buf_nomerge[CmdPtr0] | obuf_force_wr_en))) &
                       (bus_cmd_ready | ~obuf_valid | obuf_nosend) & ~obuf_wr_wait  & ~bus_addr_match_pending & lsu_bus_clk_en;

   assign obuf_rst   = ((bus_cmd_sent | (obuf_valid & obuf_nosend)) & ~obuf_wr_en & lsu_bus_clk_en) | dec_tlu_force_halt;

   assign obuf_write_in      = ibuf_buf_byp ? lsu_pkt_r.store : buf_write[CmdPtr0];
   assign obuf_sideeffect_in = ibuf_buf_byp ? is_sideeffects_r : buf_sideeffect[CmdPtr0];
   assign obuf_addr_in[31:0] = ibuf_buf_byp ? lsu_addr_r[31:0] : buf_addr[CmdPtr0];
   assign obuf_sz_in[1:0]    = ibuf_buf_byp ? {lsu_pkt_r.word, lsu_pkt_r.half} : buf_sz[CmdPtr0];
   assign obuf_merge_in      = obuf_merge_en;
   assign obuf_tag0_in[pt.LSU_BUS_TAG-1:0] = ibuf_buf_byp ? (pt.LSU_BUS_TAG)'(WrPtr0_r) : (pt.LSU_BUS_TAG)'(CmdPtr0);
   assign obuf_tag1_in[pt.LSU_BUS_TAG-1:0] = ibuf_buf_byp ? (pt.LSU_BUS_TAG)'(WrPtr1_r) : (pt.LSU_BUS_TAG)'(CmdPtr1);

   assign obuf_cmd_done_in    = ~(obuf_wr_en | obuf_rst) & (obuf_cmd_done | bus_wcmd_sent);
   assign obuf_data_done_in   = ~(obuf_wr_en | obuf_rst) & (obuf_data_done | bus_wdata_sent);

   assign obuf_aligned_in    = ibuf_buf_byp ? is_aligned_r : ((obuf_sz_in[1:0] == 2'b0) |
                                                              (obuf_sz_in[0] & ~obuf_addr_in[0]) |
                                                              (obuf_sz_in[1] & ~(|obuf_addr_in[1:0])));

   assign obuf_rdrsp_pend_in  = ((~(obuf_wr_en & ~obuf_nosend_in) & obuf_rdrsp_pend & ~(bus_rsp_read & (bus_rsp_read_tag == obuf_rdrsp_tag))) | (bus_cmd_sent & ~obuf_write)) & ~dec_tlu_force_halt;
   assign obuf_rdrsp_pend_en  = lsu_bus_clk_en | dec_tlu_force_halt;
   assign obuf_rdrsp_tag_in[pt.LSU_BUS_TAG-1:0] = (bus_cmd_sent & ~obuf_write) ? obuf_tag0[pt.LSU_BUS_TAG-1:0] : obuf_rdrsp_tag[pt.LSU_BUS_TAG-1:0];
   // No ld to ld fwd for aligned
   assign obuf_nosend_in      = (obuf_addr_in[31:3] == obuf_addr[31:3]) & obuf_aligned_in & ~obuf_sideeffect & ~obuf_write & ~obuf_write_in & ~dec_tlu_external_ldfwd_disable &
                                ((obuf_valid & ~obuf_nosend) | (obuf_rdrsp_pend & ~(bus_rsp_read & (bus_rsp_read_tag == obuf_rdrsp_tag))));

   assign obuf_byteen0_in[7:0] = ibuf_buf_byp ? (lsu_addr_r[2] ? {ldst_byteen_lo_r[3:0],4'b0} : {4'b0,ldst_byteen_lo_r[3:0]}) :
                                                (buf_addr[CmdPtr0][2] ? {buf_byteen[CmdPtr0],4'b0} : {4'b0,buf_byteen[CmdPtr0]});
   assign obuf_byteen1_in[7:0] = ibuf_buf_byp ? (end_addr_r[2] ? {ldst_byteen_hi_r[3:0],4'b0} : {4'b0,ldst_byteen_hi_r[3:0]}) :
                                                (buf_addr[CmdPtr1][2] ? {buf_byteen[CmdPtr1],4'b0} : {4'b0,buf_byteen[CmdPtr1]});
   assign obuf_data0_in[63:0]  = ibuf_buf_byp ? (lsu_addr_r[2] ? {store_data_lo_r[31:0],32'b0} : {32'b0,store_data_lo_r[31:0]}) :
                                                (buf_addr[CmdPtr0][2] ? {buf_data[CmdPtr0],32'b0} : {32'b0,buf_data[CmdPtr0]});
   assign obuf_data1_in[63:0]  = ibuf_buf_byp ? (end_addr_r[2] ? {store_data_hi_r[31:0],32'b0} :{32'b0,store_data_hi_r[31:0]}) :
                                                (buf_addr[CmdPtr1][2] ? {buf_data[CmdPtr1],32'b0} : {32'b0,buf_data[CmdPtr1]});

   for (genvar i=0 ;i<8; i++) begin
      assign obuf_byteen_in[i] = obuf_byteen0_in[i] | (obuf_merge_en & obuf_byteen1_in[i]);
      assign obuf_data_in[(8*i)+7:(8*i)] = (obuf_merge_en & obuf_byteen1_in[i]) ? obuf_data1_in[(8*i)+7:(8*i)] : obuf_data0_in[(8*i)+7:(8*i)];
   end

   // No store obuf merging for AXI since all stores are sent non-posted. Can't track the second id right now
   assign obuf_merge_en = ((CmdPtr0 != CmdPtr1) & found_cmdptr0 & found_cmdptr1 & (buf_state[CmdPtr0] == CMD) & (buf_state[CmdPtr1] == CMD) &
                           ~buf_cmd_state_bus_en[CmdPtr0] & ~buf_sideeffect[CmdPtr0] &
                           (~buf_write[CmdPtr0] & buf_dual[CmdPtr0] & ~buf_dualhi[CmdPtr0] & buf_samedw[CmdPtr0])) |  // CmdPtr0/CmdPtr1 are for same load which is within a DW
                          (ibuf_buf_byp & ldst_samedw_r & ldst_dual_r);


   rvdff_fpga  #(.WIDTH(1))              obuf_wren_ff      (.din(obuf_wr_en),                  .dout(obuf_wr_enQ),                                        .clk(lsu_busm_clk),        .clken(lsu_busm_clken), .rawclk(clk),        .*);
   rvdffsc     #(.WIDTH(1))              obuf_valid_ff     (.din(1'b1),                        .dout(obuf_valid),      .en(obuf_wr_en), .clear(obuf_rst), .clk(lsu_free_c2_clk),                                                  .*);
   rvdffs      #(.WIDTH(1))              obuf_nosend_ff    (.din(obuf_nosend_in),              .dout(obuf_nosend),     .en(obuf_wr_en),                   .clk(lsu_free_c2_clk),                                                  .*);
   rvdffs      #(.WIDTH(1))              obuf_rdrsp_pend_ff(.din(obuf_rdrsp_pend_in),          .dout(obuf_rdrsp_pend), .en(obuf_rdrsp_pend_en),           .clk(lsu_free_c2_clk),                                                  .*);
   rvdff_fpga  #(.WIDTH(1))              obuf_cmd_done_ff  (.din(obuf_cmd_done_in),            .dout(obuf_cmd_done),                                      .clk(lsu_busm_clk),        .clken(lsu_busm_clken),        .rawclk(clk), .*);
   rvdff_fpga  #(.WIDTH(1))              obuf_data_done_ff (.din(obuf_data_done_in),           .dout(obuf_data_done),                                     .clk(lsu_busm_clk),        .clken(lsu_busm_clken),        .rawclk(clk), .*);
   rvdff_fpga  #(.WIDTH(pt.LSU_BUS_TAG)) obuf_rdrsp_tagff  (.din(obuf_rdrsp_tag_in),           .dout(obuf_rdrsp_tag),                                     .clk(lsu_busm_clk),        .clken(lsu_busm_clken),        .rawclk(clk), .*);
   rvdffs_fpga #(.WIDTH(pt.LSU_BUS_TAG)) obuf_tag0ff       (.din(obuf_tag0_in),                .dout(obuf_tag0),       .en(obuf_wr_en),                   .clk(lsu_bus_obuf_c1_clk), .clken(lsu_bus_obuf_c1_clken), .rawclk(clk), .*);
   rvdffs_fpga #(.WIDTH(pt.LSU_BUS_TAG)) obuf_tag1ff       (.din(obuf_tag1_in),                .dout(obuf_tag1),       .en(obuf_wr_en),                   .clk(lsu_bus_obuf_c1_clk), .clken(lsu_bus_obuf_c1_clken), .rawclk(clk), .*);
   rvdffs_fpga #(.WIDTH(1))              obuf_mergeff      (.din(obuf_merge_in),               .dout(obuf_merge),      .en(obuf_wr_en),                   .clk(lsu_bus_obuf_c1_clk), .clken(lsu_bus_obuf_c1_clken), .rawclk(clk), .*);
   rvdffs_fpga #(.WIDTH(1))              obuf_writeff      (.din(obuf_write_in),               .dout(obuf_write),      .en(obuf_wr_en),                   .clk(lsu_bus_obuf_c1_clk), .clken(lsu_bus_obuf_c1_clken), .rawclk(clk), .*);
   rvdffs_fpga #(.WIDTH(1))              obuf_sideeffectff (.din(obuf_sideeffect_in),          .dout(obuf_sideeffect), .en(obuf_wr_en),                   .clk(lsu_bus_obuf_c1_clk), .clken(lsu_bus_obuf_c1_clken), .rawclk(clk), .*);
   rvdffs_fpga #(.WIDTH(2))              obuf_szff         (.din(obuf_sz_in[1:0]),             .dout(obuf_sz),         .en(obuf_wr_en),                   .clk(lsu_bus_obuf_c1_clk), .clken(lsu_bus_obuf_c1_clken), .rawclk(clk), .*);
   rvdffs_fpga #(.WIDTH(8))              obuf_byteenff     (.din(obuf_byteen_in[7:0]),         .dout(obuf_byteen),     .en(obuf_wr_en),                   .clk(lsu_bus_obuf_c1_clk), .clken(lsu_bus_obuf_c1_clken), .rawclk(clk), .*);
   rvdffe     #(.WIDTH(32))              obuf_addrff       (.din(obuf_addr_in[31:0]),          .dout(obuf_addr),       .en(obuf_wr_en),                                                                                           .*);
   rvdffe     #(.WIDTH(64))              obuf_dataff       (.din(obuf_data_in[63:0]),          .dout(obuf_data),       .en(obuf_wr_en),                                                                                           .*);
   rvdff_fpga #(.WIDTH(TIMER_LOG2))      obuf_timerff      (.din(obuf_wr_timer_in),            .dout(obuf_wr_timer),                                      .clk(lsu_busm_clk),        .clken(lsu_busm_clken), .rawclk(clk),        .*);


   //------------------------------------------------------------------------------
   // Output buffer logic ends here
   //------------------------------------------------------------------------------

   // Find the entry to allocate and entry to send
   always_comb begin
      WrPtr0_m[DEPTH_LOG2-1:0] = '0;
      WrPtr1_m[DEPTH_LOG2-1:0] = '0;
      found_wrptr0  = '0;
      found_wrptr1  = '0;

      // Find first write pointer
      for (int i=0; i<DEPTH; i++) begin
         if (~found_wrptr0) begin
            WrPtr0_m[DEPTH_LOG2-1:0] = DEPTH_LOG2'(i);
            found_wrptr0 = (buf_state[i] == IDLE) & ~((ibuf_valid & (ibuf_tag == i))                                               |
                                                      (lsu_busreq_r & ((WrPtr0_r == i) | (ldst_dual_r & (WrPtr1_r == i)))));
         end
      end

      // Find second write pointer
      for (int i=0; i<DEPTH; i++) begin
         if (~found_wrptr1) begin
            WrPtr1_m[DEPTH_LOG2-1:0] = DEPTH_LOG2'(i);
            found_wrptr1 = (buf_state[i] == IDLE) & ~((ibuf_valid & (ibuf_tag == i))                                               |
                                                      (lsu_busreq_m & (WrPtr0_m == i))                                         |
                                                      (lsu_busreq_r & ((WrPtr0_r == i) | (ldst_dual_r & (WrPtr1_r == i)))));
         end
      end
   end

   // Get the command ptr
   for (genvar i=0; i<DEPTH; i++) begin
      // These should be one-hot
      assign CmdPtr0Dec[i] = ~(|buf_age[i]) & (buf_state[i] == CMD) & ~buf_cmd_state_bus_en[i];
      assign CmdPtr1Dec[i] = ~(|(buf_age[i] & ~CmdPtr0Dec)) & ~CmdPtr0Dec[i] & (buf_state[i] == CMD) & ~buf_cmd_state_bus_en[i];
      assign RspPtrDec[i]  = ~(|buf_rsp_pickage[i]) & (buf_state[i] == DONE_WAIT);
   end

   assign found_cmdptr0 = |CmdPtr0Dec;
   assign found_cmdptr1 = |CmdPtr1Dec;
   assign CmdPtr0 = f_Enc8to3(8'(CmdPtr0Dec[DEPTH-1:0]));
   assign CmdPtr1 = f_Enc8to3(8'(CmdPtr1Dec[DEPTH-1:0]));
   assign RspPtr  = f_Enc8to3(8'(RspPtrDec[DEPTH-1:0]));

   // Age vector
   for (genvar i=0; i<DEPTH; i++) begin: GenAgeVec
      for (genvar j=0; j<DEPTH; j++) begin
         assign buf_age_in[i][j] = (((buf_state[i] == IDLE) & buf_state_en[i]) &
                                    (((buf_state[j] == START_WAIT) | ((buf_state[j] == CMD) & ~buf_cmd_state_bus_en[j]))                   |       // Set age bit for older entries
                                     (ibuf_drain_vld & lsu_busreq_r & (ibuf_byp | ldst_dual_r) & (i == WrPtr0_r) & (j == ibuf_tag))  |       // Set case for dual lo
                                     (ibuf_byp & lsu_busreq_r & ldst_dual_r & (i == WrPtr1_r) & (j == WrPtr0_r))))                      |     // ibuf bypass case
                                   buf_age[i][j];


         assign buf_age[i][j]    = buf_ageQ[i][j] & ~((buf_state[j] == CMD) & buf_cmd_state_bus_en[j]) & ~dec_tlu_force_halt;  // Reset case

         assign buf_age_younger[i][j] = (i == j) ? 1'b0: (~buf_age[i][j] & (buf_state[j] != IDLE));   // Younger entries
      end
   end

   // Age vector for responses
   for (genvar i=0; i<DEPTH; i++) begin: GenRspAgeVec
      for (genvar j=0; j<DEPTH; j++) begin
         assign buf_rspage_set[i][j] = ((buf_state[i] == IDLE) & buf_state_en[i]) &
                                           (~((buf_state[j] == IDLE) | (buf_state[j] == DONE))                                         |       // Set age bit for older entries
                                            (ibuf_drain_vld & lsu_busreq_r & (ibuf_byp | ldst_dual_r) & (DEPTH_LOG2'(i) == WrPtr0_r) & (DEPTH_LOG2'(j) == ibuf_tag))  |       // Set case for dual lo
                                            (ibuf_byp & lsu_busreq_r & ldst_dual_r & (DEPTH_LOG2'(i) == WrPtr1_r) & (DEPTH_LOG2'(j) == WrPtr0_r)));
         assign buf_rspage_in[i][j] = buf_rspage_set[i][j] | buf_rspage[i][j];
         assign buf_rspage[i][j]    = buf_rspageQ[i][j] & ~((buf_state[j] == DONE) | (buf_state[j] == IDLE)) & ~dec_tlu_force_halt;  // Reset case
         assign buf_rsp_pickage[i][j] = buf_rspageQ[i][j] & (buf_state[j] == DONE_WAIT);
     end
   end

   //------------------------------------------------------------------------------
   // Buffer logic
   //------------------------------------------------------------------------------
   for (genvar i=0; i<DEPTH; i++) begin : genblock

      assign ibuf_drainvec_vld[i] = (ibuf_drain_vld & (i == ibuf_tag));
      assign buf_byteen_in[i]     = ibuf_drainvec_vld[i] ? ibuf_byteen_out[3:0] : ((ibuf_byp & ldst_dual_r & (i == WrPtr1_r)) ? ldst_byteen_hi_r[3:0] : ldst_byteen_lo_r[3:0]);
      assign buf_addr_in[i]       = ibuf_drainvec_vld[i] ? ibuf_addr[31:0] : ((ibuf_byp & ldst_dual_r & (i == WrPtr1_r)) ? end_addr_r[31:0] : lsu_addr_r[31:0]);
      assign buf_dual_in[i]       = ibuf_drainvec_vld[i] ? ibuf_dual : ldst_dual_r;
      assign buf_samedw_in[i]     = ibuf_drainvec_vld[i] ? ibuf_samedw : ldst_samedw_r;
      assign buf_nomerge_in[i]    = ibuf_drainvec_vld[i] ? (ibuf_nomerge | ibuf_force_drain) : no_dword_merge_r;
      assign buf_dualhi_in[i]     = ibuf_drainvec_vld[i] ? ibuf_dual : (ibuf_byp & ldst_dual_r & (i == WrPtr1_r));   // If it's dual, ibuf will always have the high
      assign buf_dualtag_in[i]    = ibuf_drainvec_vld[i] ? ibuf_dualtag : ((ibuf_byp & ldst_dual_r & (i == WrPtr1_r)) ? WrPtr0_r : WrPtr1_r);
      assign buf_sideeffect_in[i] = ibuf_drainvec_vld[i] ? ibuf_sideeffect : is_sideeffects_r;
      assign buf_unsign_in[i]     = ibuf_drainvec_vld[i] ? ibuf_unsign : lsu_pkt_r.unsign;
      assign buf_sz_in[i]         = ibuf_drainvec_vld[i] ? ibuf_sz : {lsu_pkt_r.word, lsu_pkt_r.half};
      assign buf_write_in[i]      = ibuf_drainvec_vld[i] ? ibuf_write : lsu_pkt_r.store;

      // Buffer entry state machine
      always_comb begin
         buf_nxtstate[i]          = IDLE;
         buf_state_en[i]          = '0;
         buf_resp_state_bus_en[i] = '0;
         buf_state_bus_en[i]      = '0;
         buf_wr_en[i]             = '0;
         buf_data_in[i]           = '0;
         buf_data_en[i]           = '0;
         buf_error_en[i]          = '0;
         buf_rst[i]               = dec_tlu_force_halt;
         buf_ldfwd_en[i]          = dec_tlu_force_halt;
         buf_ldfwd_in[i]          = '0;
         buf_ldfwdtag_in[i]       = '0;

         case (buf_state[i])
            IDLE: begin
                     buf_nxtstate[i] = lsu_bus_clk_en ? CMD : START_WAIT;
                     buf_state_en[i] = (lsu_busreq_r & lsu_commit_r & (((ibuf_byp | ldst_dual_r) & ~ibuf_merge_en & (i == WrPtr0_r)) | (ibuf_byp & ldst_dual_r & (i == WrPtr1_r)))) |
                                       (ibuf_drain_vld & (i == ibuf_tag));
                     buf_wr_en[i]    = buf_state_en[i];
                     buf_data_en[i]  = buf_state_en[i];
                     buf_data_in[i]   = (ibuf_drain_vld & (i == ibuf_tag)) ? ibuf_data_out[31:0] : store_data_lo_r[31:0];
                     buf_cmd_state_bus_en[i]  = '0;
            end
            START_WAIT: begin
                     buf_nxtstate[i] = dec_tlu_force_halt ? IDLE : CMD;
                     buf_state_en[i] = lsu_bus_clk_en | dec_tlu_force_halt;
                     buf_cmd_state_bus_en[i]  = '0;
            end
            CMD: begin
                     buf_nxtstate[i]          = dec_tlu_force_halt ? IDLE : (obuf_nosend & bus_rsp_read & (bus_rsp_read_tag == obuf_rdrsp_tag)) ? DONE_WAIT : RESP;
                     buf_cmd_state_bus_en[i]  = ((obuf_tag0 == i) | (obuf_merge & (obuf_tag1 == i))) & obuf_valid & obuf_wr_enQ;  // Just use the recently written obuf_valid
                     buf_state_bus_en[i]      = buf_cmd_state_bus_en[i];
                     buf_state_en[i]          = (buf_state_bus_en[i] & lsu_bus_clk_en) | dec_tlu_force_halt;
                     buf_ldfwd_in[i]          = 1'b1;
                     buf_ldfwd_en[i]          = buf_state_en[i] & ~buf_write[i] & obuf_nosend & ~dec_tlu_force_halt;
                     buf_ldfwdtag_in[i]       = DEPTH_LOG2'(obuf_rdrsp_tag[pt.LSU_BUS_TAG-2:0]);
                     buf_data_en[i]           = buf_state_bus_en[i] & lsu_bus_clk_en & obuf_nosend & bus_rsp_read;
                     buf_error_en[i]          = buf_state_bus_en[i] & lsu_bus_clk_en & obuf_nosend & bus_rsp_read_error;
                     buf_data_in[i]           = buf_error_en[i] ? bus_rsp_rdata[31:0] : (buf_addr[i][2] ? bus_rsp_rdata[63:32] : bus_rsp_rdata[31:0]);
            end
            RESP: begin
                     buf_nxtstate[i]           = (dec_tlu_force_halt | (buf_write[i] & ~bus_rsp_write_error)) ? IDLE :    // Side-effect writes will be non-posted
                                                      (buf_dual[i] & ~buf_samedw[i] & ~buf_write[i] & (buf_state[buf_dualtag[i]] != DONE_PARTIAL)) ? DONE_PARTIAL : // Goto DONE_PARTIAL if this is the first return of dual
                                                           (buf_ldfwd[i] | any_done_wait_state |
                                                            (buf_dual[i] & ~buf_samedw[i] & ~buf_write[i] & buf_ldfwd[buf_dualtag[i]] &
                                                             (buf_state[buf_dualtag[i]] == DONE_PARTIAL) & any_done_wait_state)) ? DONE_WAIT : DONE;
                     buf_resp_state_bus_en[i]  = (bus_rsp_write & (bus_rsp_write_tag == (pt.LSU_BUS_TAG)'(i))) |
                                                 (bus_rsp_read  & ((bus_rsp_read_tag == (pt.LSU_BUS_TAG)'(i)) |
                                                                   (buf_ldfwd[i] & (bus_rsp_read_tag == (pt.LSU_BUS_TAG)'(buf_ldfwdtag[i]))) |
                                                                   (buf_dual[i] & buf_dualhi[i] & ~buf_write[i] & buf_samedw[i] & (bus_rsp_read_tag == (pt.LSU_BUS_TAG)'(buf_dualtag[i])))));
                     buf_state_bus_en[i]       = buf_resp_state_bus_en[i];
                     buf_state_en[i]           = (buf_state_bus_en[i] & lsu_bus_clk_en) | dec_tlu_force_halt;
                     buf_data_en[i]            = buf_state_bus_en[i] & bus_rsp_read & lsu_bus_clk_en;
                      // Need to capture the error for stores as well for AXI
                     buf_error_en[i]           = buf_state_bus_en[i] & lsu_bus_clk_en & ((bus_rsp_read_error  & (bus_rsp_read_tag  == (pt.LSU_BUS_TAG)'(i))) |
                                                                                         (bus_rsp_read_error  & buf_ldfwd[i] & (bus_rsp_read_tag == (pt.LSU_BUS_TAG)'(buf_ldfwdtag[i]))) |
                                                                                         (bus_rsp_write_error & (bus_rsp_write_tag == (pt.LSU_BUS_TAG)'(i))));
                     buf_data_in[i][31:0]      = (buf_state_en[i] & ~buf_error_en[i]) ? (buf_addr[i][2] ? bus_rsp_rdata[63:32] : bus_rsp_rdata[31:0]) : bus_rsp_rdata[31:0];
                     buf_cmd_state_bus_en[i]  = '0;
            end
            DONE_PARTIAL: begin   // Other part of dual load hasn't returned
                     buf_nxtstate[i]           = dec_tlu_force_halt ? IDLE : (buf_ldfwd[i] | buf_ldfwd[buf_dualtag[i]] | any_done_wait_state) ? DONE_WAIT : DONE;
                     buf_state_bus_en[i]       = bus_rsp_read & ((bus_rsp_read_tag == (pt.LSU_BUS_TAG)'(buf_dualtag[i])) |
                                                                 (buf_ldfwd[buf_dualtag[i]] & (bus_rsp_read_tag == (pt.LSU_BUS_TAG)'(buf_ldfwdtag[buf_dualtag[i]]))));
                     buf_state_en[i]           = (buf_state_bus_en[i] & lsu_bus_clk_en) | dec_tlu_force_halt;
                     buf_cmd_state_bus_en[i]  = '0;
            end
            DONE_WAIT: begin  // START_WAIT state if there are multiple outstanding nb returns
                      buf_nxtstate[i]           = dec_tlu_force_halt ? IDLE : DONE;
                      buf_state_en[i]           = ((RspPtr == DEPTH_LOG2'(i)) | (buf_dual[i] & (buf_dualtag[i] == RspPtr))) | dec_tlu_force_halt;
                      buf_cmd_state_bus_en[i]  = '0;
            end
            DONE: begin
                     buf_nxtstate[i]           = IDLE;
                     buf_rst[i]                = 1'b1;
                     buf_state_en[i]           = 1'b1;
                     buf_ldfwd_in[i]           = 1'b0;
                     buf_ldfwd_en[i]           = buf_state_en[i];
                     buf_cmd_state_bus_en[i]  = '0;
            end
            /* buf_state is an enum and the existing members are handled above */
            /*pragma coverage off*/
            default : begin
                     buf_nxtstate[i]          = IDLE;
                     buf_state_en[i]          = '0;
                     buf_resp_state_bus_en[i] = '0;
                     buf_state_bus_en[i]      = '0;
                     buf_wr_en[i]             = '0;
                     buf_data_in[i]           = '0;
                     buf_data_en[i]           = '0;
                     buf_error_en[i]          = '0;
                     buf_rst[i]               = '0;
                     buf_cmd_state_bus_en[i]  = '0;
            end
            /*pragma coverage on*/
         endcase
      end

      rvdffs  #(.WIDTH($bits(state_t))) buf_state_ff     (.din(buf_nxtstate[i]),             .dout({buf_state[i]}),    .en(buf_state_en[i]),                                        .clk(lsu_bus_buf_c1_clk), .*);
      rvdff   #(.WIDTH(DEPTH))          buf_ageff        (.din(buf_age_in[i]),               .dout(buf_ageQ[i]),                                                                    .clk(lsu_bus_buf_c1_clk), .*);
      rvdff   #(.WIDTH(DEPTH))          buf_rspageff     (.din(buf_rspage_in[i]),            .dout(buf_rspageQ[i]),                                                                 .clk(lsu_bus_buf_c1_clk), .*);
      rvdffs  #(.WIDTH(DEPTH_LOG2))     buf_dualtagff    (.din(buf_dualtag_in[i]),           .dout(buf_dualtag[i]),    .en(buf_wr_en[i]),                                           .clk(lsu_bus_buf_c1_clk), .*);
      rvdffs  #(.WIDTH(1))              buf_dualff       (.din(buf_dual_in[i]),              .dout(buf_dual[i]),       .en(buf_wr_en[i]),                                           .clk(lsu_bus_buf_c1_clk), .*);
      rvdffs  #(.WIDTH(1))              buf_samedwff     (.din(buf_samedw_in[i]),            .dout(buf_samedw[i]),     .en(buf_wr_en[i]),                                           .clk(lsu_bus_buf_c1_clk), .*);
      rvdffs  #(.WIDTH(1))              buf_nomergeff    (.din(buf_nomerge_in[i]),           .dout(buf_nomerge[i]),    .en(buf_wr_en[i]),                                           .clk(lsu_bus_buf_c1_clk), .*);
      rvdffs  #(.WIDTH(1))              buf_dualhiff     (.din(buf_dualhi_in[i]),            .dout(buf_dualhi[i]),     .en(buf_wr_en[i]),                                           .clk(lsu_bus_buf_c1_clk), .*);
      rvdffs  #(.WIDTH(1))              buf_ldfwdff      (.din(buf_ldfwd_in[i]),             .dout(buf_ldfwd[i]),      .en(buf_ldfwd_en[i]),                                        .clk(lsu_bus_buf_c1_clk), .*);
      rvdffs  #(.WIDTH(DEPTH_LOG2))     buf_ldfwdtagff   (.din(buf_ldfwdtag_in[i]),          .dout(buf_ldfwdtag[i]),   .en(buf_ldfwd_en[i]),                                        .clk(lsu_bus_buf_c1_clk), .*);
      rvdffs  #(.WIDTH(1))              buf_sideeffectff (.din(buf_sideeffect_in[i]),        .dout(buf_sideeffect[i]), .en(buf_wr_en[i]),                                           .clk(lsu_bus_buf_c1_clk), .*);
      rvdffs  #(.WIDTH(1))              buf_unsignff     (.din(buf_unsign_in[i]),            .dout(buf_unsign[i]),     .en(buf_wr_en[i]),                                           .clk(lsu_bus_buf_c1_clk), .*);
      rvdffs  #(.WIDTH(1))              buf_writeff      (.din(buf_write_in[i]),             .dout(buf_write[i]),      .en(buf_wr_en[i]),                                           .clk(lsu_bus_buf_c1_clk), .*);
      rvdffs  #(.WIDTH(2))              buf_szff         (.din(buf_sz_in[i]),                .dout(buf_sz[i]),         .en(buf_wr_en[i]),                                           .clk(lsu_bus_buf_c1_clk), .*);
      rvdffe  #(.WIDTH(32))             buf_addrff       (.din(buf_addr_in[i][31:0]),        .dout(buf_addr[i]),       .en(buf_wr_en[i]),                                                                     .*);
      rvdffs  #(.WIDTH(4))              buf_byteenff     (.din(buf_byteen_in[i][3:0]),       .dout(buf_byteen[i]),     .en(buf_wr_en[i]),                                           .clk(lsu_bus_buf_c1_clk), .*);
      rvdffe  #(.WIDTH(32))             buf_dataff       (.din(buf_data_in[i][31:0]),        .dout(buf_data[i]),       .en(buf_data_en[i]),                                                                   .*);
      rvdffsc #(.WIDTH(1))              buf_errorff      (.din(1'b1),                        .dout(buf_error[i]),      .en(buf_error_en[i]),                    .clear(buf_rst[i]), .clk(lsu_bus_buf_c1_clk), .*);

   end

   // buffer full logic
   always_comb begin
      buf_numvld_any[3:0] =  4'(({1'b0,lsu_busreq_m} << ldst_dual_m) +
                                ({1'b0,lsu_busreq_r} << ldst_dual_r) +
                                ibuf_valid);
      buf_numvld_wrcmd_any[3:0] = 4'b0;
      buf_numvld_cmd_any[3:0] = 4'b0;
      buf_numvld_pend_any[3:0] = 4'b0;
      any_done_wait_state = 1'b0;
      for (int i=0; i<DEPTH; i++) begin
         buf_numvld_any[3:0] += {3'b0, (buf_state[i] != IDLE)};
         buf_numvld_wrcmd_any[3:0] += {3'b0, (buf_write[i] & (buf_state[i] == CMD) & ~buf_cmd_state_bus_en[i])};
         buf_numvld_cmd_any[3:0]   += {3'b0, ((buf_state[i] == CMD) & ~buf_cmd_state_bus_en[i])};
         buf_numvld_pend_any[3:0]   += {3'b0, ((buf_state[i] == START_WAIT) | ((buf_state[i] == CMD) & ~buf_cmd_state_bus_en[i]))};
         any_done_wait_state |= (buf_state[i] == DONE_WAIT);
      end
   end

   assign lsu_bus_buffer_pend_any = (buf_numvld_pend_any != 0);
   assign lsu_bus_buffer_full_any = (ldst_dual_d & dec_lsu_valid_raw_d) ? (buf_numvld_any[3:0] >= (DEPTH-1)) : (buf_numvld_any[3:0] == DEPTH);
   assign lsu_bus_buffer_empty_any = ~(|buf_state[DEPTH-1:0]) & ~ibuf_valid & ~obuf_valid;


   // Non blocking ports
   assign lsu_nonblock_load_valid_m = lsu_busreq_m & lsu_pkt_m.valid & lsu_pkt_m.load & ~flush_m_up & ~ld_full_hit_m;
   assign lsu_nonblock_load_tag_m[DEPTH_LOG2-1:0] = WrPtr0_m[DEPTH_LOG2-1:0];
   assign lsu_nonblock_load_inv_r = lsu_nonblock_load_valid_r & ~lsu_commit_r;
   assign lsu_nonblock_load_inv_tag_r[DEPTH_LOG2-1:0] = WrPtr0_r[DEPTH_LOG2-1:0];      // r tag needs to be accurate even if there is no invalidate

   always_comb begin
      lsu_nonblock_load_data_ready = '0;
      lsu_nonblock_load_data_error = '0;
      lsu_nonblock_load_data_tag[DEPTH_LOG2-1:0] = '0;
      lsu_nonblock_load_data_lo[31:0] = '0;
      lsu_nonblock_load_data_hi[31:0] = '0;
      for (int i=0; i<DEPTH; i++) begin
          // Use buf_rst[i] instead of buf_state_en[i] for timing
          lsu_nonblock_load_data_ready      |= (buf_state[i] == DONE) & ~buf_write[i];
          lsu_nonblock_load_data_error      |= (buf_state[i] == DONE) & buf_error[i] & ~buf_write[i];
          lsu_nonblock_load_data_tag[DEPTH_LOG2-1:0]   |= DEPTH_LOG2'(i) & {DEPTH_LOG2{((buf_state[i] == DONE) & ~buf_write[i] & (~buf_dual[i] | ~buf_dualhi[i]))}};
          lsu_nonblock_load_data_lo[31:0]     |= buf_data[i][31:0] & {32{((buf_state[i] == DONE) & ~buf_write[i] & (~buf_dual[i] | ~buf_dualhi[i]))}};
          lsu_nonblock_load_data_hi[31:0]     |= buf_data[i][31:0] & {32{((buf_state[i] == DONE) & ~buf_write[i] & (buf_dual[i] & buf_dualhi[i]))}};
      end
   end

   assign lsu_nonblock_addr_offset[1:0] = buf_addr[lsu_nonblock_load_data_tag][1:0];
   assign lsu_nonblock_sz[1:0]          = buf_sz[lsu_nonblock_load_data_tag][1:0];
   assign lsu_nonblock_unsign           = buf_unsign[lsu_nonblock_load_data_tag];
   assign lsu_nonblock_data_unalgn[31:0] = 32'({lsu_nonblock_load_data_hi[31:0], lsu_nonblock_load_data_lo[31:0]} >> 8*lsu_nonblock_addr_offset[1:0]);

   assign lsu_nonblock_load_data_valid = lsu_nonblock_load_data_ready & ~lsu_nonblock_load_data_error;
   assign lsu_nonblock_load_data[31:0] = ({32{ lsu_nonblock_unsign & (lsu_nonblock_sz[1:0] == 2'b00)}} & {24'b0,lsu_nonblock_data_unalgn[7:0]}) |
                                         ({32{ lsu_nonblock_unsign & (lsu_nonblock_sz[1:0] == 2'b01)}} & {16'b0,lsu_nonblock_data_unalgn[15:0]}) |
                                         ({32{~lsu_nonblock_unsign & (lsu_nonblock_sz[1:0] == 2'b00)}} & {{24{lsu_nonblock_data_unalgn[7]}}, lsu_nonblock_data_unalgn[7:0]}) |
                                         ({32{~lsu_nonblock_unsign & (lsu_nonblock_sz[1:0] == 2'b01)}} & {{16{lsu_nonblock_data_unalgn[15]}},lsu_nonblock_data_unalgn[15:0]}) |
                                         ({32{(lsu_nonblock_sz[1:0] == 2'b10)}} & lsu_nonblock_data_unalgn[31:0]);

   // Determine if there is a pending return to sideeffect load/store
   always_comb begin
      bus_sideeffect_pend = obuf_valid & obuf_sideeffect & dec_tlu_sideeffect_posted_disable;
      for (int i=0; i<DEPTH; i++) begin
         bus_sideeffect_pend |= ((buf_state[i] == RESP) & buf_sideeffect[i] & dec_tlu_sideeffect_posted_disable);
      end
   end

   // We have no ordering rules for AXI. Need to check outstanding trxns to same address for AXI
   always_comb begin
      bus_addr_match_pending = '0;
      for (int i=0; i<DEPTH; i++) begin
         bus_addr_match_pending |= (obuf_valid & (obuf_addr[31:3] == buf_addr[i][31:3]) & (buf_state[i] == RESP) & ~((obuf_tag0 == (pt.LSU_BUS_TAG)'(i)) | (obuf_merge & (obuf_tag1 == (pt.LSU_BUS_TAG)'(i)))));
      end
   end

   // Generic bus signals
   assign bus_cmd_ready                      = obuf_write ? ((obuf_cmd_done | obuf_data_done) ? (obuf_cmd_done ? lsu_axi_wready : lsu_axi_awready) : (lsu_axi_awready & lsu_axi_wready)) : lsu_axi_arready;
   assign bus_wcmd_sent                      = lsu_axi_awvalid & lsu_axi_awready;
   assign bus_wdata_sent                     = lsu_axi_wvalid & lsu_axi_wready;
   assign bus_cmd_sent                       = ((obuf_cmd_done | bus_wcmd_sent) & (obuf_data_done | bus_wdata_sent)) | (lsu_axi_arvalid & lsu_axi_arready);

   assign bus_rsp_read                       = lsu_axi_rvalid & lsu_axi_rready;
   assign bus_rsp_write                      = lsu_axi_bvalid & lsu_axi_bready;
   assign bus_rsp_read_tag[pt.LSU_BUS_TAG-1:0]  = lsu_axi_rid[pt.LSU_BUS_TAG-1:0];
   assign bus_rsp_write_tag[pt.LSU_BUS_TAG-1:0] = lsu_axi_bid[pt.LSU_BUS_TAG-1:0];
   assign bus_rsp_write_error                = bus_rsp_write & (lsu_axi_bresp[1:0] != 2'b0);
   assign bus_rsp_read_error                 = bus_rsp_read  & (lsu_axi_rresp[1:0] != 2'b0);
   assign bus_rsp_rdata[63:0]                = lsu_axi_rdata[63:0];

   // AXI command signals
   assign lsu_axi_awvalid               = obuf_valid & obuf_write & ~obuf_cmd_done & ~bus_addr_match_pending;
   assign lsu_axi_awid[pt.LSU_BUS_TAG-1:0] = (pt.LSU_BUS_TAG)'(obuf_tag0);
   assign lsu_axi_awaddr[31:0]          = obuf_sideeffect ? obuf_addr[31:0] : {obuf_addr[31:3],3'b0};
   assign lsu_axi_awsize[2:0]           = obuf_sideeffect ? {1'b0, obuf_sz[1:0]} : 3'b011;
   assign lsu_axi_awprot[2:0]           = 3'b001;
   assign lsu_axi_awcache[3:0]          = obuf_sideeffect ? 4'b0 : 4'b1111;
   assign lsu_axi_awregion[3:0]         = obuf_addr[31:28];
   assign lsu_axi_awlen[7:0]            = '0;
   assign lsu_axi_awburst[1:0]          = 2'b01;
   assign lsu_axi_awqos[3:0]            = '0;
   assign lsu_axi_awlock                = '0;

   assign lsu_axi_wvalid                = obuf_valid & obuf_write & ~obuf_data_done & ~bus_addr_match_pending;
   assign lsu_axi_wstrb[7:0]            = obuf_byteen[7:0] & {8{obuf_write}};
   assign lsu_axi_wdata[63:0]           = obuf_data[63:0];
   assign lsu_axi_wlast                 = '1;

   assign lsu_axi_arvalid               = obuf_valid & ~obuf_write & ~obuf_nosend & ~bus_addr_match_pending;
   assign lsu_axi_arid[pt.LSU_BUS_TAG-1:0] = (pt.LSU_BUS_TAG)'(obuf_tag0);
   assign lsu_axi_araddr[31:0]          = obuf_sideeffect ? obuf_addr[31:0] : {obuf_addr[31:3],3'b0};
   assign lsu_axi_arsize[2:0]           = obuf_sideeffect ? {1'b0, obuf_sz[1:0]} : 3'b011;
   assign lsu_axi_arprot[2:0]           = 3'b001;
   assign lsu_axi_arcache[3:0]          = obuf_sideeffect ? 4'b0 : 4'b1111;
   assign lsu_axi_arregion[3:0]         = obuf_addr[31:28];
   assign lsu_axi_arlen[7:0]            = '0;
   assign lsu_axi_arburst[1:0]          = 2'b01;
   assign lsu_axi_arqos[3:0]            = '0;
   assign lsu_axi_arlock                = '0;

   assign lsu_axi_bready = 1;
   assign lsu_axi_rready = 1;

   always_comb begin
      lsu_imprecise_error_store_any = '0;
      lsu_imprecise_error_store_tag = '0;
      for (int i=0; i<DEPTH; i++) begin
         lsu_imprecise_error_store_any |= lsu_bus_clk_en_q & (buf_state[i] == DONE) & buf_error[i] & buf_write[i];
         lsu_imprecise_error_store_tag |= DEPTH_LOG2'(i) & {DEPTH_LOG2{((buf_state[i] == DONE) & buf_error[i] & buf_write[i])}};
      end
   end
   assign lsu_imprecise_error_load_any       = lsu_nonblock_load_data_error & ~lsu_imprecise_error_store_any;   // This is to make sure we send only one imprecise error for load/store
   assign lsu_imprecise_error_addr_any[31:0] = lsu_imprecise_error_store_any ? buf_addr[lsu_imprecise_error_store_tag[DEPTH_LOG2-1:0]] : buf_addr[lsu_nonblock_load_data_tag[DEPTH_LOG2-1:0]];

   // PMU signals
   assign lsu_pmu_bus_trxn  = (lsu_axi_awvalid & lsu_axi_awready) | (lsu_axi_wvalid & lsu_axi_wready) | (lsu_axi_arvalid & lsu_axi_arready);
   assign lsu_pmu_bus_misaligned = lsu_busreq_r & ldst_dual_r & lsu_commit_r;
   assign lsu_pmu_bus_error = lsu_imprecise_error_load_any | lsu_imprecise_error_store_any;
   assign lsu_pmu_bus_busy  = (lsu_axi_awvalid & ~lsu_axi_awready) | (lsu_axi_wvalid & ~lsu_axi_wready) | (lsu_axi_arvalid & ~lsu_axi_arready);

   rvdff_fpga #(.WIDTH(1))               lsu_axi_awvalid_ff (.din(lsu_axi_awvalid),                .dout(lsu_axi_awvalid_q),                .clk(lsu_busm_clk), .clken(lsu_busm_clken), .rawclk(clk), .*);
   rvdff_fpga #(.WIDTH(1))               lsu_axi_awready_ff (.din(lsu_axi_awready),                .dout(lsu_axi_awready_q),                .clk(lsu_busm_clk), .clken(lsu_busm_clken), .rawclk(clk), .*);
   rvdff_fpga #(.WIDTH(1))               lsu_axi_wvalid_ff  (.din(lsu_axi_wvalid),                 .dout(lsu_axi_wvalid_q),                 .clk(lsu_busm_clk), .clken(lsu_busm_clken), .rawclk(clk), .*);
   rvdff_fpga #(.WIDTH(1))               lsu_axi_wready_ff  (.din(lsu_axi_wready),                 .dout(lsu_axi_wready_q),                 .clk(lsu_busm_clk), .clken(lsu_busm_clken), .rawclk(clk), .*);
   rvdff_fpga #(.WIDTH(1))               lsu_axi_arvalid_ff (.din(lsu_axi_arvalid),                .dout(lsu_axi_arvalid_q),                .clk(lsu_busm_clk), .clken(lsu_busm_clken), .rawclk(clk), .*);
   rvdff_fpga #(.WIDTH(1))               lsu_axi_arready_ff (.din(lsu_axi_arready),                .dout(lsu_axi_arready_q),                .clk(lsu_busm_clk), .clken(lsu_busm_clken), .rawclk(clk), .*);

   rvdff_fpga  #(.WIDTH(1))              lsu_axi_bvalid_ff  (.din(lsu_axi_bvalid),                 .dout(lsu_axi_bvalid_q),                 .clk(lsu_busm_clk), .clken(lsu_busm_clken), .rawclk(clk), .*);
   rvdff_fpga  #(.WIDTH(1))              lsu_axi_bready_ff  (.din(lsu_axi_bready),                 .dout(lsu_axi_bready_q),                 .clk(lsu_busm_clk), .clken(lsu_busm_clken), .rawclk(clk), .*);
   rvdff_fpga  #(.WIDTH(2))              lsu_axi_bresp_ff   (.din(lsu_axi_bresp[1:0]),             .dout(lsu_axi_bresp_q[1:0]),             .clk(lsu_busm_clk), .clken(lsu_busm_clken), .rawclk(clk), .*);
   rvdff_fpga  #(.WIDTH(pt.LSU_BUS_TAG)) lsu_axi_bid_ff     (.din(lsu_axi_bid[pt.LSU_BUS_TAG-1:0]),.dout(lsu_axi_bid_q[pt.LSU_BUS_TAG-1:0]),.clk(lsu_busm_clk), .clken(lsu_busm_clken), .rawclk(clk), .*);
   rvdffe      #(.WIDTH(64))             lsu_axi_rdata_ff   (.din(lsu_axi_rdata[63:0]),            .dout(lsu_axi_rdata_q[63:0]),            .en((lsu_axi_rvalid | clk_override) & lsu_bus_clk_en), .*);

   rvdff_fpga  #(.WIDTH(1))              lsu_axi_rvalid_ff  (.din(lsu_axi_rvalid),                 .dout(lsu_axi_rvalid_q),                 .clk(lsu_busm_clk), .clken(lsu_busm_clken), .rawclk(clk), .*);
   rvdff_fpga  #(.WIDTH(1))              lsu_axi_rready_ff  (.din(lsu_axi_rready),                 .dout(lsu_axi_rready_q),                 .clk(lsu_busm_clk), .clken(lsu_busm_clken), .rawclk(clk), .*);
   rvdff_fpga  #(.WIDTH(2))              lsu_axi_rresp_ff   (.din(lsu_axi_rresp[1:0]),             .dout(lsu_axi_rresp_q[1:0]),             .clk(lsu_busm_clk), .clken(lsu_busm_clken), .rawclk(clk), .*);
   rvdff_fpga  #(.WIDTH(pt.LSU_BUS_TAG)) lsu_axi_rid_ff     (.din(lsu_axi_rid[pt.LSU_BUS_TAG-1:0]),.dout(lsu_axi_rid_q[pt.LSU_BUS_TAG-1:0]),.clk(lsu_busm_clk), .clken(lsu_busm_clken), .rawclk(clk), .*);

   rvdff #(.WIDTH(DEPTH_LOG2)) lsu_WrPtr0_rff (.din(WrPtr0_m), .dout(WrPtr0_r), .clk(lsu_c2_r_clk), .*);
   rvdff #(.WIDTH(DEPTH_LOG2)) lsu_WrPtr1_rff (.din(WrPtr1_m), .dout(WrPtr1_r), .clk(lsu_c2_r_clk), .*);

   rvdff #(.WIDTH(1)) lsu_busreq_rff (.din(lsu_busreq_m & ~flush_r & ~ld_full_hit_m),      .dout(lsu_busreq_r), .clk(lsu_c2_r_clk), .*);
   rvdff #(.WIDTH(1)) lsu_nonblock_load_valid_rff  (.din(lsu_nonblock_load_valid_m),  .dout(lsu_nonblock_load_valid_r), .clk(lsu_c2_r_clk), .*);

`ifdef RV_ASSERT_ON

   for (genvar i=0; i<4; i++) begin: GenByte
      assert_ld_byte_hitvecfn_lo_onehot: assert #0 ($onehot0(ld_byte_hitvecfn_lo[i][DEPTH-1:0]));
      assert_ld_byte_hitvecfn_hi_onehot: assert #0 ($onehot0(ld_byte_hitvecfn_hi[i][DEPTH-1:0]));
   end

   for (genvar i=0; i<DEPTH; i++) begin: GenAssertAge
      assert_bufempty_agevec: assert #0 (~(lsu_bus_buffer_empty_any & |(buf_age[i])));
   end

   assert_CmdPtr0Dec_onehot: assert #0 ($onehot0(CmdPtr0Dec[DEPTH-1:0] & ~{DEPTH{dec_tlu_force_halt}}));
   assert_CmdPtr1Dec_onehot: assert #0 ($onehot0(CmdPtr1Dec[DEPTH-1:0] & ~{DEPTH{dec_tlu_force_halt}}));

`endif

endmodule // el2_lsu_bus_buffer
