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
// Function: LSU control
// Comments:
//
//
// DC1 -> DC2 -> DC3 -> DC4 (Commit)
//
//********************************************************************************
module el2_lsu_lsc_ctl
import el2_pkg::*;
#(
`include "el2_param.vh"
 )(
   input logic                rst_l,                     // reset, active low
   input logic                clk_override,              // Override non-functional clock gating
   input logic                clk,                       // Clock only while core active.  Through one clock header.  For flops with    second clock header built in.  Connected to ACTIVE_L2CLK.

   // clocks per pipe
   input logic                lsu_c1_m_clk,
   input logic                lsu_c1_r_clk,
   input logic                lsu_c2_m_clk,
   input logic                lsu_c2_r_clk,
   input logic                lsu_store_c1_m_clk,

   input logic [31:0]         lsu_ld_data_r,             // Load data R-stage
   input logic [31:0]         lsu_ld_data_corr_r,        // ECC corrected data R-stage
   input logic                lsu_single_ecc_error_r,    // ECC single bit error R-stage
   input logic                lsu_double_ecc_error_r,    // ECC double bit error R-stage

   input logic [31:0]         lsu_ld_data_m,             // Load data M-stage
   input logic                lsu_single_ecc_error_m,    // ECC single bit error M-stage
   input logic                lsu_double_ecc_error_m,    // ECC double bit error M-stage

   input logic                flush_m_up,                // Flush M and D stage
   input logic                flush_r,                   // Flush R-stage
   input logic                ldst_dual_d,               // load/store is unaligned at 32 bit boundary D-stage
   input logic                ldst_dual_m,               // load/store is unaligned at 32 bit boundary M-stage
   input logic                ldst_dual_r,               // load/store is unaligned at 32 bit boundary R-stage

   input logic [31:0]         exu_lsu_rs1_d,             // address
   input logic [31:0]         exu_lsu_rs2_d,             // store data

   input el2_lsu_pkt_t       lsu_p,                     // lsu control packet
   input logic                dec_lsu_valid_raw_d,       // Raw valid for address computation
   input logic [11:0]         dec_lsu_offset_d,          // 12b offset for load/store addresses

   input  logic [31:0]        picm_mask_data_m,          // PIC data M-stage
   input  logic [31:0]        bus_read_data_m,           // the bus return data
   output logic [31:0]        lsu_result_m,              // lsu load data
   output logic [31:0]        lsu_result_corr_r,         // This is the ECC corrected data going to RF
   // lsu address down the pipe
   output logic [31:0]        lsu_addr_d,
   output logic [31:0]        lsu_addr_m,
   output logic [31:0]        lsu_addr_r,
   // lsu address down the pipe - needed to check unaligned
   output logic [31:0]        end_addr_d,
   output logic [31:0]        end_addr_m,
   output logic [31:0]        end_addr_r,
   // store data down the pipe
   output logic [31:0]        store_data_m,

   input  logic [31:0]         dec_tlu_mrac_ff,          // CSR for memory region control
   output logic                lsu_exc_m,                // Access or misaligned fault
   output logic                is_sideeffects_m,         // is sideffects space
   output logic                lsu_commit_r,             // lsu instruction in r commits
   output logic                lsu_single_ecc_error_incr,// LSU inc SB error counter
   output el2_lsu_error_pkt_t lsu_error_pkt_r,          // lsu exception packet

   output logic [31:1]         lsu_fir_addr,             // fast interrupt address
   output logic [1:0]          lsu_fir_error,            // Error during fast interrupt lookup

   // address in dccm/pic/external per pipe stage
   output logic               addr_in_dccm_d,
   output logic               addr_in_dccm_m,
   output logic               addr_in_dccm_r,

   output logic               addr_in_pic_d,
   output logic               addr_in_pic_m,
   output logic               addr_in_pic_r,

   output logic               addr_external_m,

   // DMA slave
   input logic                dma_dccm_req,
   input logic [31:0]         dma_mem_addr,
   input logic [2:0]          dma_mem_sz,
   input logic                dma_mem_write,
   input logic [63:0]         dma_mem_wdata,

   // Store buffer related signals
   output el2_lsu_pkt_t      lsu_pkt_d,
   output el2_lsu_pkt_t      lsu_pkt_m,
   output el2_lsu_pkt_t      lsu_pkt_r,

    input logic lsu_pmp_error_start,
    input logic lsu_pmp_error_end,

   input  logic               scan_mode                  // Scan mode

   );

   logic [31:3]        end_addr_pre_m, end_addr_pre_r;
   logic [31:0]        full_addr_d;
   logic [31:0]        full_end_addr_d;
   logic [31:0]        lsu_rs1_d;
   logic [11:0]        lsu_offset_d;
   logic [31:0]        rs1_d;
   logic [11:0]        offset_d;
   logic [12:0]        end_addr_offset_d;
   logic [2:0]         addr_offset_d;

   logic [63:0]        dma_mem_wdata_shifted;
   logic               addr_external_d;
   logic               addr_external_r;
   logic               access_fault_d, misaligned_fault_d;
   logic               access_fault_m, misaligned_fault_m;

   logic               fir_dccm_access_error_d, fir_nondccm_access_error_d;
   logic               fir_dccm_access_error_m, fir_nondccm_access_error_m;

   logic [3:0]         exc_mscause_d, exc_mscause_m;
   logic [31:0]        rs1_d_raw;
   logic [31:0]        store_data_d, store_data_pre_m, store_data_m_in;
   logic [31:0]        bus_read_data_r;

   el2_lsu_pkt_t           dma_pkt_d;
   el2_lsu_pkt_t           lsu_pkt_m_in, lsu_pkt_r_in;
   el2_lsu_error_pkt_t     lsu_error_pkt_m;


   // Premux the rs1/offset for dma
   assign lsu_rs1_d[31:0]    = dec_lsu_valid_raw_d ? exu_lsu_rs1_d[31:0] : dma_mem_addr[31:0];
   assign lsu_offset_d[11:0] = dec_lsu_offset_d[11:0] & {12{dec_lsu_valid_raw_d}};
   assign rs1_d_raw[31:0]    = lsu_rs1_d[31:0];
   assign offset_d[11:0]     = lsu_offset_d[11:0];

   assign rs1_d[31:0] = (lsu_pkt_d.load_ldst_bypass_d) ? lsu_result_m[31:0] : rs1_d_raw[31:0];

   // generate the ls address
   rvlsadder   lsadder  (.rs1(rs1_d[31:0]),
                       .offset(offset_d[11:0]),
                       .dout(full_addr_d[31:0])
                       );

   // Module to generate the memory map of the address
   el2_lsu_addrcheck addrcheck (
              .start_addr_d(full_addr_d[31:0]),
              .end_addr_d(full_end_addr_d[31:0]),
              .rs1_region_d(rs1_d[31:28]),
              .*
  );

   // Calculate start/end address for load/store
   assign addr_offset_d[2:0]      = ({3{lsu_pkt_d.half}} & 3'b01) | ({3{lsu_pkt_d.word}} & 3'b11) | ({3{lsu_pkt_d.dword}} & 3'b111);
   assign end_addr_offset_d[12:0] = {offset_d[11],offset_d[11:0]} + {9'b0,addr_offset_d[2:0]};
   assign full_end_addr_d[31:0]   = rs1_d[31:0] + {{19{end_addr_offset_d[12]}},end_addr_offset_d[12:0]};
   assign end_addr_d[31:0]        = full_end_addr_d[31:0];
   assign lsu_exc_m               = access_fault_m | misaligned_fault_m;

   // Goes to TLU to increment the ECC error counter
   assign lsu_single_ecc_error_incr = (lsu_single_ecc_error_r & ~lsu_double_ecc_error_r) & (lsu_commit_r | lsu_pkt_r.dma) & lsu_pkt_r.valid;

   if (pt.LOAD_TO_USE_PLUS1 == 1) begin: L2U_Plus1_1
      logic               access_fault_r, misaligned_fault_r;
      logic [3:0]         exc_mscause_r;
      logic               fir_dccm_access_error_r, fir_nondccm_access_error_r;

      // Generate exception packet
      assign lsu_error_pkt_r.exc_valid = (access_fault_r | misaligned_fault_r | lsu_double_ecc_error_r) & lsu_pkt_r.valid & ~lsu_pkt_r.dma & ~lsu_pkt_r.fast_int;
      assign lsu_error_pkt_r.single_ecc_error = lsu_single_ecc_error_r & ~lsu_error_pkt_r.exc_valid & ~lsu_pkt_r.dma;
      assign lsu_error_pkt_r.inst_type = lsu_pkt_r.store;
      assign lsu_error_pkt_r.exc_type  = ~misaligned_fault_r;
      assign lsu_error_pkt_r.mscause[3:0] = (lsu_double_ecc_error_r & ~misaligned_fault_r & ~access_fault_r) ? 4'h1 : exc_mscause_r[3:0];
      assign lsu_error_pkt_r.addr[31:0] = lsu_addr_r[31:0];

      assign lsu_fir_error[1:0] = fir_nondccm_access_error_r ? 2'b11 : (fir_dccm_access_error_r ? 2'b10 : ((lsu_pkt_r.fast_int & lsu_double_ecc_error_r) ? 2'b01 : 2'b00));

      rvdff #(1) access_fault_rff             (.din(access_fault_m),             .dout(access_fault_r),             .clk(lsu_c1_r_clk), .*);
      rvdff #(1) misaligned_fault_rff         (.din(misaligned_fault_m),         .dout(misaligned_fault_r),         .clk(lsu_c1_r_clk), .*);
      rvdff #(4) exc_mscause_rff              (.din(exc_mscause_m[3:0]),         .dout(exc_mscause_r[3:0]),         .clk(lsu_c1_r_clk), .*);
      rvdff #(1) fir_dccm_access_error_mff    (.din(fir_dccm_access_error_m),    .dout(fir_dccm_access_error_r),    .clk(lsu_c1_r_clk), .*);
      rvdff #(1) fir_nondccm_access_error_mff (.din(fir_nondccm_access_error_m), .dout(fir_nondccm_access_error_r), .clk(lsu_c1_r_clk), .*);

   end else begin: L2U_Plus1_0
      logic [1:0] lsu_fir_error_m;

      // Generate exception packet
      assign lsu_error_pkt_m.exc_valid = (access_fault_m | misaligned_fault_m | lsu_double_ecc_error_m) & lsu_pkt_m.valid & ~lsu_pkt_m.dma & ~lsu_pkt_m.fast_int & ~flush_m_up;
      assign lsu_error_pkt_m.single_ecc_error = lsu_single_ecc_error_m & ~lsu_error_pkt_m.exc_valid & ~lsu_pkt_m.dma;
      assign lsu_error_pkt_m.inst_type = lsu_pkt_m.store;
      assign lsu_error_pkt_m.exc_type  = ~misaligned_fault_m;
      assign lsu_error_pkt_m.mscause[3:0] = (lsu_double_ecc_error_m & ~misaligned_fault_m & ~access_fault_m) ? 4'h1 : exc_mscause_m[3:0];
      assign lsu_error_pkt_m.addr[31:0] = lsu_addr_m[31:0];

      assign lsu_fir_error_m[1:0] = fir_nondccm_access_error_m ? 2'b11 : (fir_dccm_access_error_m ? 2'b10 : ((lsu_pkt_m.fast_int & lsu_double_ecc_error_m) ? 2'b01 : 2'b00));

      rvdff  #(1)                             lsu_exc_valid_rff       (.*, .din(lsu_error_pkt_m.exc_valid),                        .dout(lsu_error_pkt_r.exc_valid),                        .clk(lsu_c2_r_clk));
      rvdff  #(1)                             lsu_single_ecc_error_rff(.*, .din(lsu_error_pkt_m.single_ecc_error),                 .dout(lsu_error_pkt_r.single_ecc_error),                 .clk(lsu_c2_r_clk));
      rvdffe #($bits(el2_lsu_error_pkt_t)-2) lsu_error_pkt_rff       (.*, .din(lsu_error_pkt_m[$bits(el2_lsu_error_pkt_t)-1:2]), .dout(lsu_error_pkt_r[$bits(el2_lsu_error_pkt_t)-1:2]), .en(lsu_error_pkt_m.exc_valid | lsu_error_pkt_m.single_ecc_error | clk_override));
      rvdff #(2)                              lsu_fir_error_rff       (.*, .din(lsu_fir_error_m[1:0]),                             .dout(lsu_fir_error[1:0]),                               .clk(lsu_c2_r_clk));
   end

   //Create DMA packet
   always_comb begin
      dma_pkt_d = '0;
      dma_pkt_d.valid   = dma_dccm_req;
      dma_pkt_d.dma     = 1'b1;
      dma_pkt_d.store   = dma_mem_write;
      dma_pkt_d.load    = ~dma_mem_write;
      dma_pkt_d.by      = (dma_mem_sz[2:0] == 3'b0);
      dma_pkt_d.half    = (dma_mem_sz[2:0] == 3'b1);
      dma_pkt_d.word    = (dma_mem_sz[2:0] == 3'b10);
      dma_pkt_d.dword   = (dma_mem_sz[2:0] == 3'b11);
   end

   always_comb begin
      lsu_pkt_d = dec_lsu_valid_raw_d ? lsu_p : dma_pkt_d;
      lsu_pkt_m_in = lsu_pkt_d;
      lsu_pkt_r_in = lsu_pkt_m;

      lsu_pkt_d.valid = (lsu_p.valid & ~(flush_m_up & ~lsu_p.fast_int)) | dma_dccm_req;
      lsu_pkt_m_in.valid = lsu_pkt_d.valid & ~(flush_m_up & ~lsu_pkt_d.dma);
      lsu_pkt_r_in.valid = lsu_pkt_m.valid & ~(flush_m_up & ~lsu_pkt_m.dma) ;
   end

   // C2 clock for valid and C1 for other bits of packet
   rvdff #(1) lsu_pkt_vldmff (.*, .din(lsu_pkt_m_in.valid), .dout(lsu_pkt_m.valid), .clk(lsu_c2_m_clk));
   rvdff #(1) lsu_pkt_vldrff (.*, .din(lsu_pkt_r_in.valid), .dout(lsu_pkt_r.valid), .clk(lsu_c2_r_clk));

   rvdff #($bits(el2_lsu_pkt_t)-1) lsu_pkt_mff (.*, .din(lsu_pkt_m_in[$bits(el2_lsu_pkt_t)-1:1]), .dout(lsu_pkt_m[$bits(el2_lsu_pkt_t)-1:1]), .clk(lsu_c1_m_clk));
   rvdff #($bits(el2_lsu_pkt_t)-1) lsu_pkt_rff (.*, .din(lsu_pkt_r_in[$bits(el2_lsu_pkt_t)-1:1]), .dout(lsu_pkt_r[$bits(el2_lsu_pkt_t)-1:1]), .clk(lsu_c1_r_clk));



   if (pt.LOAD_TO_USE_PLUS1 == 1) begin: L2U1_Plus1_1
      logic [31:0] lsu_ld_datafn_r, lsu_ld_datafn_corr_r;

      assign lsu_ld_datafn_r[31:0]  = addr_external_r ? bus_read_data_r[31:0] : lsu_ld_data_r[31:0];
      assign lsu_ld_datafn_corr_r[31:0]  = addr_external_r ? bus_read_data_r[31:0] : lsu_ld_data_corr_r[31:0];

      // this is really R stage signal
      assign lsu_result_m[31:0] = ({32{ lsu_pkt_r.unsign & lsu_pkt_r.by  }} & {24'b0,lsu_ld_datafn_r[7:0]}) |
                                                                    ({32{ lsu_pkt_r.unsign & lsu_pkt_r.half}} & {16'b0,lsu_ld_datafn_r[15:0]}) |
                                                                    ({32{~lsu_pkt_r.unsign & lsu_pkt_r.by  }} & {{24{  lsu_ld_datafn_r[7]}}, lsu_ld_datafn_r[7:0]}) |
                                                                    ({32{~lsu_pkt_r.unsign & lsu_pkt_r.half}} & {{16{  lsu_ld_datafn_r[15]}},lsu_ld_datafn_r[15:0]}) |
                                                                    ({32{lsu_pkt_r.word}}                     & lsu_ld_datafn_r[31:0]);

      // this signal is used for gpr update
      assign lsu_result_corr_r[31:0] = ({32{ lsu_pkt_r.unsign & lsu_pkt_r.by  }} & {24'b0,lsu_ld_datafn_corr_r[7:0]}) |
                                                                              ({32{ lsu_pkt_r.unsign & lsu_pkt_r.half}} & {16'b0,lsu_ld_datafn_corr_r[15:0]}) |
                                                                              ({32{~lsu_pkt_r.unsign & lsu_pkt_r.by  }} & {{24{  lsu_ld_datafn_corr_r[7]}}, lsu_ld_datafn_corr_r[7:0]}) |
                                                                              ({32{~lsu_pkt_r.unsign & lsu_pkt_r.half}} & {{16{  lsu_ld_datafn_corr_r[15]}},lsu_ld_datafn_corr_r[15:0]}) |
                                                                              ({32{lsu_pkt_r.word}}                     & lsu_ld_datafn_corr_r[31:0]);

   end else begin: L2U1_Plus1_0 // block: L2U1_Plus1_1
      logic [31:0] lsu_ld_datafn_m, lsu_ld_datafn_corr_r;

      assign lsu_ld_datafn_m[31:0] = addr_external_m ? bus_read_data_m[31:0] : lsu_ld_data_m[31:0];
      assign lsu_ld_datafn_corr_r[31:0] = addr_external_r ? bus_read_data_r[31:0] : lsu_ld_data_corr_r[31:0];

      // this result must look at prior stores and merge them in
      assign lsu_result_m[31:0] = ({32{ lsu_pkt_m.unsign & lsu_pkt_m.by  }} & {24'b0,lsu_ld_datafn_m[7:0]}) |
                                                                    ({32{ lsu_pkt_m.unsign & lsu_pkt_m.half}} & {16'b0,lsu_ld_datafn_m[15:0]}) |
                                                                    ({32{~lsu_pkt_m.unsign & lsu_pkt_m.by  }} & {{24{  lsu_ld_datafn_m[7]}}, lsu_ld_datafn_m[7:0]}) |
                                                                    ({32{~lsu_pkt_m.unsign & lsu_pkt_m.half}} & {{16{  lsu_ld_datafn_m[15]}},lsu_ld_datafn_m[15:0]}) |
                                                                    ({32{lsu_pkt_m.word}}                     & lsu_ld_datafn_m[31:0]);

      // this signal is used for gpr update
      assign lsu_result_corr_r[31:0] = ({32{ lsu_pkt_r.unsign & lsu_pkt_r.by  }} & {24'b0,lsu_ld_datafn_corr_r[7:0]}) |
                                                                              ({32{ lsu_pkt_r.unsign & lsu_pkt_r.half}} & {16'b0,lsu_ld_datafn_corr_r[15:0]}) |
                                                                              ({32{~lsu_pkt_r.unsign & lsu_pkt_r.by  }} & {{24{  lsu_ld_datafn_corr_r[7]}}, lsu_ld_datafn_corr_r[7:0]}) |
                                                                              ({32{~lsu_pkt_r.unsign & lsu_pkt_r.half}} & {{16{  lsu_ld_datafn_corr_r[15]}},lsu_ld_datafn_corr_r[15:0]}) |
                                                                              ({32{lsu_pkt_r.word}}                     & lsu_ld_datafn_corr_r[31:0]);
   end

   // Fast interrupt address
   assign lsu_fir_addr[31:1]    = lsu_ld_data_corr_r[31:1];

   // absence load/store all 0's
   assign lsu_addr_d[31:0] = full_addr_d[31:0];

   // Interrupt as a flush source allows the WB to occur
   assign lsu_commit_r = lsu_pkt_r.valid & (lsu_pkt_r.store | lsu_pkt_r.load) & ~flush_r & ~lsu_pkt_r.dma;

   assign dma_mem_wdata_shifted[63:0] = 64'(dma_mem_wdata[63:0] >> {dma_mem_addr[2:0], 3'b000});   // Shift the dma data to lower bits to make it consistent to lsu stores
   assign store_data_d[31:0] = dma_dccm_req ? dma_mem_wdata_shifted[31:0] : exu_lsu_rs2_d[31:0];  // Write to PIC still happens in r stage

   assign store_data_m_in[31:0] = (lsu_pkt_d.store_data_bypass_d) ? lsu_result_m[31:0] : store_data_d[31:0];

   assign store_data_m[31:0] = (picm_mask_data_m[31:0] | {32{~addr_in_pic_m}}) & ((lsu_pkt_m.store_data_bypass_m) ? lsu_result_m[31:0] : store_data_pre_m[31:0]);


   rvdff #(32)  sdmff (.*, .din(store_data_m_in[31:0]), .dout(store_data_pre_m[31:0]),                       .clk(lsu_store_c1_m_clk));

   rvdff #(32) samff (.*, .din(lsu_addr_d[31:0]), .dout(lsu_addr_m[31:0]), .clk(lsu_c1_m_clk));
   rvdff #(32) sarff (.*, .din(lsu_addr_m[31:0]), .dout(lsu_addr_r[31:0]), .clk(lsu_c1_r_clk));

   assign end_addr_m[31:3] = ldst_dual_m ? end_addr_pre_m[31:3] : lsu_addr_m[31:3];       // This is for power saving
   assign end_addr_r[31:3] = ldst_dual_r ? end_addr_pre_r[31:3] : lsu_addr_r[31:3];       // This is for power saving

   rvdffe #(29) end_addr_hi_mff (.*, .din(end_addr_d[31:3]), .dout(end_addr_pre_m[31:3]), .en((lsu_pkt_d.valid & ldst_dual_d) | clk_override));
   rvdffe #(29) end_addr_hi_rff (.*, .din(end_addr_m[31:3]), .dout(end_addr_pre_r[31:3]), .en((lsu_pkt_m.valid & ldst_dual_m) | clk_override));

   rvdff #(3)  end_addr_lo_mff (.*, .din(end_addr_d[2:0]), .dout(end_addr_m[2:0]), .clk(lsu_c1_m_clk));
   rvdff #(3)  end_addr_lo_rff (.*, .din(end_addr_m[2:0]), .dout(end_addr_r[2:0]), .clk(lsu_c1_r_clk));

   rvdff #(1) addr_in_dccm_mff(.din(addr_in_dccm_d), .dout(addr_in_dccm_m), .clk(lsu_c1_m_clk), .*);
   rvdff #(1) addr_in_dccm_rff(.din(addr_in_dccm_m), .dout(addr_in_dccm_r), .clk(lsu_c1_r_clk), .*);

   rvdff #(1) addr_in_pic_mff(.din(addr_in_pic_d), .dout(addr_in_pic_m), .clk(lsu_c1_m_clk), .*);
   rvdff #(1) addr_in_pic_rff(.din(addr_in_pic_m), .dout(addr_in_pic_r), .clk(lsu_c1_r_clk), .*);

   rvdff #(1) addr_external_mff(.din(addr_external_d), .dout(addr_external_m), .clk(lsu_c1_m_clk), .*);
   rvdff #(1) addr_external_rff(.din(addr_external_m), .dout(addr_external_r), .clk(lsu_c1_r_clk), .*);

   rvdff #(1) access_fault_mff     (.din(access_fault_d),     .dout(access_fault_m),     .clk(lsu_c1_m_clk), .*);
   rvdff #(1) misaligned_fault_mff (.din(misaligned_fault_d), .dout(misaligned_fault_m), .clk(lsu_c1_m_clk), .*);
   rvdff #(4) exc_mscause_mff      (.din(exc_mscause_d[3:0]), .dout(exc_mscause_m[3:0]), .clk(lsu_c1_m_clk), .*);

   rvdff #(1) fir_dccm_access_error_mff    (.din(fir_dccm_access_error_d),    .dout(fir_dccm_access_error_m),    .clk(lsu_c1_m_clk), .*);
   rvdff #(1) fir_nondccm_access_error_mff (.din(fir_nondccm_access_error_d), .dout(fir_nondccm_access_error_m), .clk(lsu_c1_m_clk), .*);

   rvdffe #(32) bus_read_data_r_ff (.*, .din(bus_read_data_m[31:0]), .dout(bus_read_data_r[31:0]), .en(addr_external_m | clk_override));

endmodule
