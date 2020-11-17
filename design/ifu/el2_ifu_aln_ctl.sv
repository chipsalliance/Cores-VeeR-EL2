//********************************************************************************
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

//********************************************************************************
// Function: Instruction aligner
//********************************************************************************
module el2_ifu_aln_ctl
import el2_pkg::*;
#(
`include "el2_param.vh"
 )
  (

   input logic                                    scan_mode,                // Flop scan mode control
   input logic                                    rst_l,                    // reset, active low
   input logic                                    clk,                      // Clock only while core active.  Through one clock header.  For flops with    second clock header built in.  Connected to ACTIVE_L2CLK.
   input logic                                    active_clk,               // Clock only while core active.  Through two clock headers. For flops without second clock header built in.

   input logic                                    ifu_async_error_start,    // ecc/parity related errors with current fetch - not sent down the pipe

   input logic [1:0]                              iccm_rd_ecc_double_err,   // This fetch has a double ICCM ecc  error.

   input logic [1:0]                              ic_access_fault_f,        // Instruction access fault for the current fetch.
   input logic [1:0]                              ic_access_fault_type_f,   // Instruction access fault types

   input logic                                    exu_flush_final,          // Flush from the pipeline.

   input logic                                    dec_i0_decode_d,          // Valid instruction at D-stage and not blocked

   input logic [31:0]                             ifu_fetch_data_f,         // fetch data in memory format - not right justified

   input logic [1:0]                              ifu_fetch_val,            // valids on a 2B boundary, right justified
   input logic [31:1]                             ifu_fetch_pc,             // starting pc of fetch



   output logic                                   ifu_i0_valid,             // Instruction 0 is valid
   output logic                                   ifu_i0_icaf,              // Instruction 0 has access fault
   output logic [1:0]                             ifu_i0_icaf_type,         // Instruction 0 access fault type
   output logic                                   ifu_i0_icaf_second,       // Instruction 0 has access fault on second 2B of 4B inst

   output logic                                   ifu_i0_dbecc,             // Instruction 0 has double bit ecc error
   output logic [31:0]                            ifu_i0_instr,             // Instruction 0
   output logic [31:1]                            ifu_i0_pc,                // Instruction 0 PC
   output logic                                   ifu_i0_pc4,

   output logic                                   ifu_fb_consume1,          // Consumed one buffer. To fetch control fetch for buffer mass balance
   output logic                                   ifu_fb_consume2,          // Consumed two buffers.To fetch control fetch for buffer mass balance


   input logic [pt.BHT_GHR_SIZE-1:0]              ifu_bp_fghr_f,            // fetch GHR
   input logic [31:1]                             ifu_bp_btb_target_f,      // predicted RET target
   input logic [11:0]                             ifu_bp_poffset_f,         // predicted target offset
   input logic [1:0] [$clog2(pt.BTB_SIZE)-1:0]    ifu_bp_fa_index_f,        // predicted branch index (fully associative option)

   input logic [1:0]                              ifu_bp_hist0_f,           // history counters for all 4 potential branches, bit 1, right justified
   input logic [1:0]                              ifu_bp_hist1_f,           // history counters for all 4 potential branches, bit 1, right justified
   input logic [1:0]                              ifu_bp_pc4_f,             // pc4 indication, right justified
   input logic [1:0]                              ifu_bp_way_f,             // way indication, right justified
   input logic [1:0]                              ifu_bp_valid_f,           // branch valid, right justified
   input logic [1:0]                              ifu_bp_ret_f,             // predicted ret indication, right justified


   output el2_br_pkt_t                           i0_brp,                   // Branch packet for I0.
   output logic [pt.BTB_ADDR_HI:pt.BTB_ADDR_LO]   ifu_i0_bp_index,          // BP index
   output logic [pt.BHT_GHR_SIZE-1:0]             ifu_i0_bp_fghr,           // BP FGHR
   output logic [pt.BTB_BTAG_SIZE-1:0]            ifu_i0_bp_btag,           // BP tag

   output logic [$clog2(pt.BTB_SIZE)-1:0]         ifu_i0_fa_index,          // Fully associt btb index

   output logic                                   ifu_pmu_instr_aligned,    // number of inst aligned this cycle

   output logic [15:0]                            ifu_i0_cinst              // 16b compress inst for i0
   );



   logic                                          ifvalid;
   logic                                          shift_f1_f0, shift_f2_f0, shift_f2_f1;
   logic                                          fetch_to_f0, fetch_to_f1, fetch_to_f2;

   logic [1:0]                                    f2val_in, f2val;
   logic [1:0]                                    f1val_in, f1val;
   logic [1:0]                                    f0val_in, f0val;
   logic [1:0]                                    sf1val, sf0val;

   logic [31:0]                                   aligndata;
   logic                                          first4B, first2B;

   logic [31:0]                                   uncompress0;
   logic                                          i0_shift;
   logic                                          shift_2B, shift_4B;
   logic                                          f1_shift_2B;
   logic                                          f2_valid, sf1_valid, sf0_valid;

   logic [31:0]                                   ifirst;
   logic [1:0]                                    alignval;
   logic [31:1]                                   firstpc, secondpc;

   logic [11:0]                                   f1poffset;
   logic [11:0]                                   f0poffset;
   logic [pt.BHT_GHR_SIZE-1:0]                    f1fghr;
   logic [pt.BHT_GHR_SIZE-1:0]                    f0fghr;
   logic [1:0]                                    f1hist1;
   logic [1:0]                                    f0hist1;
   logic [1:0]                                    f1hist0;
   logic [1:0]                                    f0hist0;

   logic [1:0][$clog2(pt.BTB_SIZE)-1:0]           f0index, f1index, alignindex;

   logic [1:0]                                    f1ictype;
   logic [1:0]                                    f0ictype;

   logic [1:0]                                    f1pc4;
   logic [1:0]                                    f0pc4;

   logic [1:0]                                    f1ret;
   logic [1:0]                                    f0ret;
   logic [1:0]                                    f1way;
   logic [1:0]                                    f0way;

   logic [1:0]                                    f1brend;
   logic [1:0]                                    f0brend;

   logic [1:0]                                    alignbrend;
   logic [1:0]                                    alignpc4;

   logic [1:0]                                    alignret;
   logic [1:0]                                    alignway;
   logic [1:0]                                    alignhist1;
   logic [1:0]                                    alignhist0;
   logic [1:1]                                    alignfromf1;
   logic                                          i0_ends_f1;
   logic                                          i0_br_start_error;

   logic [31:1]                                   f1prett;
   logic [31:1]                                   f0prett;
   logic [1:0]                                    f1dbecc;
   logic [1:0]                                    f0dbecc;
   logic [1:0]                                    f1icaf;
   logic [1:0]                                    f0icaf;

   logic [1:0]                                    aligndbecc;
   logic [1:0]                                    alignicaf;
   logic                                          i0_brp_pc4;

   logic [pt.BTB_ADDR_HI:pt.BTB_ADDR_LO]          firstpc_hash, secondpc_hash;

   logic                                          first_legal;

   logic [1:0]                                    wrptr, wrptr_in;
   logic [1:0]                                    rdptr, rdptr_in;
   logic [2:0]                                    qwen;
   logic [31:0]                                   q2,q1,q0;
   logic                                          q2off_in, q2off;
   logic                                          q1off_in, q1off;
   logic                                          q0off_in, q0off;
   logic                                          f0_shift_2B;

   logic [31:0]                                   q0eff;
   logic [31:0]                                   q0final;
   logic                                          q0ptr;
   logic [1:0]                                    q0sel;

   logic [31:0]                                   q1eff;
   logic [15:0]                                   q1final;
   logic                                          q1ptr;
   logic [1:0]                                    q1sel;

   logic [2:0]                                    qren;

   logic                                          consume_fb1, consume_fb0;
   logic [1:0]                                    icaf_eff;

   localparam                                     BRDATA_SIZE  = pt.BTB_ENABLE ? 16+($clog2(pt.BTB_SIZE)*2*pt.BTB_FULLYA) : 2;
   localparam                                     BRDATA_WIDTH = pt.BTB_ENABLE ? 8+($clog2(pt.BTB_SIZE)*pt.BTB_FULLYA) : 1;
   logic [BRDATA_SIZE-1:0]                        brdata_in, brdata2, brdata1, brdata0;
   logic [BRDATA_SIZE-1:0]                        brdata1eff, brdata0eff;
   logic [BRDATA_SIZE-1:0]                        brdata1final, brdata0final;

   localparam                                     MHI   = 1+(pt.BTB_ENABLE * (43+pt.BHT_GHR_SIZE));
   localparam                                     MSIZE = 2+(pt.BTB_ENABLE * (43+pt.BHT_GHR_SIZE));

   logic [MHI:0]                                  misc_data_in, misc2, misc1, misc0;
   logic [MHI:0]                                  misc1eff, misc0eff;

   logic [pt.BTB_BTAG_SIZE-1:0]                  firstbrtag_hash, secondbrtag_hash;

   logic                                         error_stall_in, error_stall;

   assign error_stall_in = (error_stall | ifu_async_error_start) & ~exu_flush_final;

   rvdff #(.WIDTH(7))  bundle1ff (.*,
                                  .clk(active_clk),
                                  .din ({wrptr_in[1:0],rdptr_in[1:0],q2off_in,q1off_in,q0off_in}),
                                  .dout({wrptr[1:0],   rdptr[1:0],   q2off,   q1off,   q0off})
                                  );

   rvdffie #(.WIDTH(7),.OVERRIDE(1))  bundle2ff (.*,
                                                 .din ({error_stall_in,f2val_in[1:0],f1val_in[1:0],f0val_in[1:0]}),
                                                 .dout({error_stall,   f2val[1:0],   f1val[1:0],   f0val[1:0]   })
                                                 );

if(pt.BTB_ENABLE==1) begin
   rvdffe #(BRDATA_SIZE)  brdata2ff   (.*, .clk(clk), .en(qwen[2]),        .din(brdata_in[BRDATA_SIZE-1:0]), .dout(brdata2[BRDATA_SIZE-1:0]));
   rvdffe #(BRDATA_SIZE)  brdata1ff   (.*, .clk(clk), .en(qwen[1]),        .din(brdata_in[BRDATA_SIZE-1:0]), .dout(brdata1[BRDATA_SIZE-1:0]));
   rvdffe #(BRDATA_SIZE)  brdata0ff   (.*, .clk(clk), .en(qwen[0]),        .din(brdata_in[BRDATA_SIZE-1:0]), .dout(brdata0[BRDATA_SIZE-1:0]));
   rvdffe #(MSIZE)        misc2ff     (.*, .clk(clk), .en(qwen[2]),        .din(misc_data_in[MHI:0]),        .dout(misc2[MHI:0]));
   rvdffe #(MSIZE)        misc1ff     (.*, .clk(clk), .en(qwen[1]),        .din(misc_data_in[MHI:0]),        .dout(misc1[MHI:0]));
   rvdffe #(MSIZE)        misc0ff     (.*, .clk(clk), .en(qwen[0]),        .din(misc_data_in[MHI:0]),        .dout(misc0[MHI:0]));
end
else begin

   rvdffie #((MSIZE*3)+(BRDATA_SIZE*3))    miscff      (.*,
                                                        .din({qwen[2] ? {misc_data_in[MHI:0], brdata_in[BRDATA_SIZE-1:0]} : {misc2[MHI:0], brdata2[BRDATA_SIZE-1:0]},
                                                              qwen[1] ? {misc_data_in[MHI:0], brdata_in[BRDATA_SIZE-1:0]} : {misc1[MHI:0], brdata1[BRDATA_SIZE-1:0]},
                                                              qwen[0] ? {misc_data_in[MHI:0], brdata_in[BRDATA_SIZE-1:0]} : {misc0[MHI:0], brdata0[BRDATA_SIZE-1:0]}}),
                                                        .dout({misc2[MHI:0],misc1[MHI:0],misc0[MHI:0],
                                                               brdata2[BRDATA_SIZE-1:0], brdata1[BRDATA_SIZE-1:0], brdata0[BRDATA_SIZE-1:0]})
                                                        );
end

  logic [31:1] q2pc, q1pc, q0pc;

   rvdffe #(31)           q2pcff        (.*, .clk(clk), .en(qwen[2]),        .din(ifu_fetch_pc[31:1]),     .dout(q2pc[31:1]));
   rvdffe #(31)           q1pcff        (.*, .clk(clk), .en(qwen[1]),        .din(ifu_fetch_pc[31:1]),     .dout(q1pc[31:1]));
   rvdffe #(31)           q0pcff        (.*, .clk(clk), .en(qwen[0]),        .din(ifu_fetch_pc[31:1]),     .dout(q0pc[31:1]));

   rvdffe #(32)           q2ff        (.*, .clk(clk), .en(qwen[2]),        .din(ifu_fetch_data_f[31:0]),     .dout(q2[31:0]));
   rvdffe #(32)           q1ff        (.*, .clk(clk), .en(qwen[1]),        .din(ifu_fetch_data_f[31:0]),     .dout(q1[31:0]));
   rvdffe #(32)           q0ff        (.*, .clk(clk), .en(qwen[0]),        .din(ifu_fetch_data_f[31:0]),     .dout(q0[31:0]));


   // new queue control logic

   assign qren[2:0]          = {  rdptr[1:0] == 2'b10,
                                  rdptr[1:0] == 2'b01,
                                  rdptr[1:0] == 2'b00 };

   assign qwen[2:0]          = { (wrptr[1:0] == 2'b10) & ifvalid,
                                 (wrptr[1:0] == 2'b01) & ifvalid,
                                 (wrptr[1:0] == 2'b00) & ifvalid };


   assign rdptr_in[1:0]      = ({2{ qren[0]         &  ifu_fb_consume1 & ~exu_flush_final}} & 2'b01     ) |
                               ({2{ qren[1]         &  ifu_fb_consume1 & ~exu_flush_final}} & 2'b10     ) |
                               ({2{ qren[2]         &  ifu_fb_consume1 & ~exu_flush_final}} & 2'b00     ) |
                               ({2{ qren[0]         &  ifu_fb_consume2 & ~exu_flush_final}} & 2'b10     ) |
                               ({2{ qren[1]         &  ifu_fb_consume2 & ~exu_flush_final}} & 2'b00     ) |
                               ({2{ qren[2]         &  ifu_fb_consume2 & ~exu_flush_final}} & 2'b01     ) |
                               ({2{~ifu_fb_consume1 & ~ifu_fb_consume2 & ~exu_flush_final}} & rdptr[1:0]);

   assign wrptr_in[1:0]      = ({2{ qwen[0] & ~exu_flush_final}} & 2'b01     ) |
                               ({2{ qwen[1] & ~exu_flush_final}} & 2'b10     ) |
                               ({2{ qwen[2] & ~exu_flush_final}} & 2'b00     ) |
                               ({2{~ifvalid & ~exu_flush_final}} & wrptr[1:0]);



   assign q2off_in          = ( ~qwen[2] & (rdptr[1:0]==2'd2)  &  (q2off | f0_shift_2B) ) |
                              ( ~qwen[2] & (rdptr[1:0]==2'd1)  &  (q2off | f1_shift_2B) ) |
                              ( ~qwen[2] & (rdptr[1:0]==2'd0)  &   q2off                );

   assign q1off_in          = ( ~qwen[1] & (rdptr[1:0]==2'd1)  &  (q1off | f0_shift_2B) ) |
                              ( ~qwen[1] & (rdptr[1:0]==2'd0)  &  (q1off | f1_shift_2B) ) |
                              ( ~qwen[1] & (rdptr[1:0]==2'd2)  &   q1off                );

   assign q0off_in          = ( ~qwen[0] & (rdptr[1:0]==2'd0)  &  (q0off | f0_shift_2B) ) |
                              ( ~qwen[0] & (rdptr[1:0]==2'd2)  &  (q0off | f1_shift_2B) ) |
                              ( ~qwen[0] & (rdptr[1:0]==2'd1)  &   q0off                );



   assign q0ptr              = ( (rdptr[1:0]==2'b00) & q0off ) |
                               ( (rdptr[1:0]==2'b01) & q1off ) |
                               ( (rdptr[1:0]==2'b10) & q2off );

   assign q1ptr              = ( (rdptr[1:0]==2'b00) & q1off ) |
                               ( (rdptr[1:0]==2'b01) & q2off ) |
                               ( (rdptr[1:0]==2'b10) & q0off );

   assign q0sel[1:0]         = {q0ptr,~q0ptr};

   assign q1sel[1:0]         = {q1ptr,~q1ptr};

   // end new queue control logic


   // misc data that is associated with each fetch buffer

   if(pt.BTB_ENABLE==1)
     assign misc_data_in[MHI:0] = {

                                    ic_access_fault_type_f[1:0],
                                    ifu_bp_btb_target_f[31:1],
                                    ifu_bp_poffset_f[11:0],
                                    ifu_bp_fghr_f[pt.BHT_GHR_SIZE-1:0]
                                    };
   else
     assign misc_data_in[MHI:0] = {
                                    ic_access_fault_type_f[1:0]
                                    };


   assign {misc1eff[MHI:0],misc0eff[MHI:0]} = (({MSIZE*2{qren[0]}} & {misc1[MHI:0],misc0[MHI:0]}) |
                                               ({MSIZE*2{qren[1]}} & {misc2[MHI:0],misc1[MHI:0]}) |
                                               ({MSIZE*2{qren[2]}} & {misc0[MHI:0],misc2[MHI:0]}));

   if(pt.BTB_ENABLE==1) begin
   assign {
            f1ictype[1:0],
            f1prett[31:1],
            f1poffset[11:0],
            f1fghr[pt.BHT_GHR_SIZE-1:0]
            } = misc1eff[MHI:0];

   assign {
            f0ictype[1:0],
            f0prett[31:1],
            f0poffset[11:0],
            f0fghr[pt.BHT_GHR_SIZE-1:0]
            } = misc0eff[MHI:0];

      if(pt.BTB_FULLYA) begin
         assign brdata_in[BRDATA_SIZE-1:0] = {
                                               ifu_bp_fa_index_f[1], iccm_rd_ecc_double_err[1],ic_access_fault_f[1],ifu_bp_hist1_f[1],ifu_bp_hist0_f[1],ifu_bp_pc4_f[1],ifu_bp_way_f[1],ifu_bp_valid_f[1],ifu_bp_ret_f[1],
                                               ifu_bp_fa_index_f[0], iccm_rd_ecc_double_err[0],ic_access_fault_f[0],ifu_bp_hist1_f[0],ifu_bp_hist0_f[0],ifu_bp_pc4_f[0],ifu_bp_way_f[0],ifu_bp_valid_f[0],ifu_bp_ret_f[0]
                                               };
         assign {f0index[1],f0dbecc[1],f0icaf[1],f0hist1[1],f0hist0[1],f0pc4[1],f0way[1],f0brend[1],f0ret[1],
                 f0index[0],f0dbecc[0],f0icaf[0],f0hist1[0],f0hist0[0],f0pc4[0],f0way[0],f0brend[0],f0ret[0]} = brdata0final[BRDATA_SIZE-1:0];

         assign {f1index[1],f1dbecc[1],f1icaf[1],f1hist1[1],f1hist0[1],f1pc4[1],f1way[1],f1brend[1],f1ret[1],
                 f1index[0],f1dbecc[0],f1icaf[0],f1hist1[0],f1hist0[0],f1pc4[0],f1way[0],f1brend[0],f1ret[0]} = brdata1final[BRDATA_SIZE-1:0];

      end
      else begin
         assign brdata_in[BRDATA_SIZE-1:0] = {
                                               iccm_rd_ecc_double_err[1],ic_access_fault_f[1],ifu_bp_hist1_f[1],ifu_bp_hist0_f[1],ifu_bp_pc4_f[1],ifu_bp_way_f[1],ifu_bp_valid_f[1],ifu_bp_ret_f[1],
                                               iccm_rd_ecc_double_err[0],ic_access_fault_f[0],ifu_bp_hist1_f[0],ifu_bp_hist0_f[0],ifu_bp_pc4_f[0],ifu_bp_way_f[0],ifu_bp_valid_f[0],ifu_bp_ret_f[0]
                                               };
         assign {f0dbecc[1],f0icaf[1],f0hist1[1],f0hist0[1],f0pc4[1],f0way[1],f0brend[1],f0ret[1],
                 f0dbecc[0],f0icaf[0],f0hist1[0],f0hist0[0],f0pc4[0],f0way[0],f0brend[0],f0ret[0]} = brdata0final[BRDATA_SIZE-1:0];

         assign {f1dbecc[1],f1icaf[1],f1hist1[1],f1hist0[1],f1pc4[1],f1way[1],f1brend[1],f1ret[1],
                 f1dbecc[0],f1icaf[0],f1hist1[0],f1hist0[0],f1pc4[0],f1way[0],f1brend[0],f1ret[0]} = brdata1final[BRDATA_SIZE-1:0];

      end




   assign {brdata1eff[BRDATA_SIZE-1:0],brdata0eff[BRDATA_SIZE-1:0]} = (({BRDATA_SIZE*2{qren[0]}} & {brdata1[BRDATA_SIZE-1:0],brdata0[BRDATA_SIZE-1:0]}) |
                                                                       ({BRDATA_SIZE*2{qren[1]}} & {brdata2[BRDATA_SIZE-1:0],brdata1[BRDATA_SIZE-1:0]}) |
                                                                       ({BRDATA_SIZE*2{qren[2]}} & {brdata0[BRDATA_SIZE-1:0],brdata2[BRDATA_SIZE-1:0]}));

   assign brdata0final[BRDATA_SIZE-1:0] = (({BRDATA_SIZE{q0sel[0]}} & {                     brdata0eff[2*BRDATA_WIDTH-1:0]}) |
                                           ({BRDATA_SIZE{q0sel[1]}} & {{BRDATA_WIDTH{1'b0}},brdata0eff[BRDATA_SIZE-1:BRDATA_WIDTH]}));

   assign brdata1final[BRDATA_SIZE-1:0] = (({BRDATA_SIZE{q1sel[0]}} & {                     brdata1eff[2*BRDATA_WIDTH-1:0]}) |
                                           ({BRDATA_SIZE{q1sel[1]}} & {{BRDATA_WIDTH{1'b0}},brdata1eff[BRDATA_SIZE-1:BRDATA_WIDTH]}));

   end // if (pt.BTB_ENABLE==1)
   else begin
      assign {
               f1ictype[1:0]
               } = misc1eff[MHI:0];

      assign {
               f0ictype[1:0]
               } = misc0eff[MHI:0];

      assign brdata_in[BRDATA_SIZE-1:0] = {
                                            iccm_rd_ecc_double_err[1],ic_access_fault_f[1],
                                            iccm_rd_ecc_double_err[0],ic_access_fault_f[0]
                                            };
      assign {f0dbecc[1],f0icaf[1],
              f0dbecc[0],f0icaf[0]} = brdata0final[BRDATA_SIZE-1:0];

      assign {f1dbecc[1],f1icaf[1],
              f1dbecc[0],f1icaf[0]} = brdata1final[BRDATA_SIZE-1:0];

      assign {brdata1eff[BRDATA_SIZE-1:0],brdata0eff[BRDATA_SIZE-1:0]} = (({BRDATA_SIZE*2{qren[0]}} & {brdata1[BRDATA_SIZE-1:0],brdata0[BRDATA_SIZE-1:0]}) |
                                                                          ({BRDATA_SIZE*2{qren[1]}} & {brdata2[BRDATA_SIZE-1:0],brdata1[BRDATA_SIZE-1:0]}) |
                                                                       ({BRDATA_SIZE*2{qren[2]}} & {brdata0[BRDATA_SIZE-1:0],brdata2[BRDATA_SIZE-1:0]}));

      assign brdata0final[BRDATA_SIZE-1:0] = (({BRDATA_SIZE{q0sel[0]}} & {                     brdata0eff[2*BRDATA_WIDTH-1:0]}) |
                                              ({BRDATA_SIZE{q0sel[1]}} & {{BRDATA_WIDTH{1'b0}},brdata0eff[BRDATA_SIZE-1:BRDATA_WIDTH]}));

      assign brdata1final[BRDATA_SIZE-1:0] = (({BRDATA_SIZE{q1sel[0]}} & {                     brdata1eff[2*BRDATA_WIDTH-1:0]}) |
                                              ({BRDATA_SIZE{q1sel[1]}} & {{BRDATA_WIDTH{1'b0}},brdata1eff[BRDATA_SIZE-1:BRDATA_WIDTH]}));

   end // else: !if(pt.BTB_ENABLE==1)


   // possible states of { sf0_valid, sf1_valid, f2_valid }
   //
   // 000    if->f0
   // 100    if->f1
   // 101    illegal
   // 010    if->f1, f1->f0
   // 110    if->f2
   // 001    if->f1, f2->f0
   // 011    if->f2, f2->f1, f1->f0
   // 111   !if,     no shift

   assign f2_valid           =  f2val[0];
   assign sf1_valid          =  sf1val[0];
   assign sf0_valid          =  sf0val[0];

   // interface to fetch

   assign consume_fb0        = ~sf0val[0] & f0val[0];

   assign consume_fb1        = ~sf1val[0] & f1val[0];

   assign ifu_fb_consume1    =  consume_fb0 & ~consume_fb1 & ~exu_flush_final;
   assign ifu_fb_consume2    =  consume_fb0 &  consume_fb1 & ~exu_flush_final;

   assign ifvalid            =  ifu_fetch_val[0];

   assign shift_f1_f0        =  ~sf0_valid &  sf1_valid;
   assign shift_f2_f0        =  ~sf0_valid & ~sf1_valid &  f2_valid;
   assign shift_f2_f1        =  ~sf0_valid &  sf1_valid &  f2_valid;

   assign fetch_to_f0        =  ~sf0_valid & ~sf1_valid & ~f2_valid & ifvalid;

   assign fetch_to_f1        = (~sf0_valid & ~sf1_valid &  f2_valid & ifvalid)  |
                               (~sf0_valid &  sf1_valid & ~f2_valid & ifvalid)  |
                               ( sf0_valid & ~sf1_valid & ~f2_valid & ifvalid);

   assign fetch_to_f2        = (~sf0_valid &  sf1_valid &  f2_valid & ifvalid)  |
                               ( sf0_valid &  sf1_valid & ~f2_valid & ifvalid);


   assign f2val_in[1:0]      = ({2{ fetch_to_f2 &                               ~exu_flush_final}} & ifu_fetch_val[1:0]) |
                               ({2{~fetch_to_f2 & ~shift_f2_f1 & ~shift_f2_f0 & ~exu_flush_final}} & f2val[1:0]        );


   assign sf1val[1:0]        = ({2{ f1_shift_2B}} & {1'b0,f1val[1]}) |
                               ({2{~f1_shift_2B}} & f1val[1:0]     );

   assign f1val_in[1:0]      = ({2{ fetch_to_f1                               & ~exu_flush_final}} & ifu_fetch_val[1:0]) |
                               ({2{                shift_f2_f1                & ~exu_flush_final}} & f2val[1:0]        ) |
                               ({2{~fetch_to_f1 & ~shift_f2_f1 & ~shift_f1_f0 & ~exu_flush_final}} & sf1val[1:0]       );



   assign sf0val[1:0]        = ({2{ shift_2B            }} & {1'b0,f0val[1]}) |
                               ({2{~shift_2B & ~shift_4B}} & f0val[1:0]);

   assign f0val_in[1:0]      = ({2{fetch_to_f0                                & ~exu_flush_final}} & ifu_fetch_val[1:0]) |
                               ({2{                shift_f2_f0                & ~exu_flush_final}} & f2val[1:0]        ) |
                               ({2{                               shift_f1_f0 & ~exu_flush_final}} & sf1val[1:0]       ) |
                               ({2{~fetch_to_f0 & ~shift_f2_f0 & ~shift_f1_f0 & ~exu_flush_final}} & sf0val[1:0]       );

   assign {q1eff[31:0],q0eff[31:0]} = (({64{qren[0]}} & {q1[31:0],q0[31:0]}) |
                                       ({64{qren[1]}} & {q2[31:0],q1[31:0]}) |
                                       ({64{qren[2]}} & {q0[31:0],q2[31:0]}));

   assign q0final[31:0]      = ({32{q0sel[0]}} & {      q0eff[31:0]}) |
                               ({32{q0sel[1]}} & {16'b0,q0eff[31:16]});

   assign q1final[15:0]      = ({16{q1sel[0]}} & q1eff[15:0] ) |
                               ({16{q1sel[1]}} & q1eff[31:16]);
   logic [31:1] q0pceff, q0pcfinal;
   logic [31:1] q1pceff;

   assign {q1pceff[31:1],q0pceff[31:1]} = (({62{qren[0]}} & {q1pc[31:1],q0pc[31:1]}) |
                                           ({62{qren[1]}} & {q2pc[31:1],q1pc[31:1]}) |
                                           ({62{qren[2]}} & {q0pc[31:1],q2pc[31:1]}));


   assign q0pcfinal[31:1]      = ({31{q0sel[0]}} & ( q0pceff[31:1])) |
                                 ({31{q0sel[1]}} & ( q0pceff[31:1] + 31'd1));

   assign aligndata[31:0]    = ({32{ f0val[1]           }} & {q0final[31:0]}) |
                               ({32{~f0val[1] & f0val[0]}} & {q1final[15:0],q0final[15:0]});

   assign alignval[1:0]      = ({ 2{ f0val[1]           }} & {2'b11}) |
                               ({ 2{~f0val[1] & f0val[0]}} & {f1val[0],1'b1});

   assign alignicaf[1:0]    = ({ 2{ f0val[1]           }} &  f0icaf[1:0]          ) |
                              ({ 2{~f0val[1] & f0val[0]}} & {f1icaf[0],f0icaf[0]});

   assign aligndbecc[1:0]    = ({ 2{ f0val[1]           }} &  f0dbecc[1:0]          ) |
                              ({ 2{~f0val[1] & f0val[0]}} & {f1dbecc[0],f0dbecc[0]});

   if (pt.BTB_ENABLE==1) begin

   // for branch prediction

   assign alignbrend[1:0]    = ({ 2{ f0val[1]           }} &  f0brend[1:0]          ) |
                               ({ 2{~f0val[1] & f0val[0]}} & {f1brend[0],f0brend[0]});

   assign alignpc4[1:0]      = ({ 2{ f0val[1]           }} &  f0pc4[1:0]        ) |
                               ({ 2{~f0val[1] & f0val[0]}} & {f1pc4[0],f0pc4[0]});

      if(pt.BTB_FULLYA) begin
         assign alignindex[0]      = f0index[0];
         assign alignindex[1]      = f0val[1] ? f0index[1] : f1index[0];
      end

   assign alignret[1:0]      = ({ 2{ f0val[1]           }} &  f0ret[1:0]        ) |
                               ({ 2{~f0val[1] & f0val[0]}} & {f1ret[0],f0ret[0]});

   assign alignway[1:0]      = ({ 2{ f0val[1]           }} &  f0way[1:0]        ) |
                               ({ 2{~f0val[1] & f0val[0]}} & {f1way[0],f0way[0]});

   assign alignhist1[1:0]    = ({ 2{ f0val[1]           }} &  f0hist1[1:0]          ) |
                               ({ 2{~f0val[1] & f0val[0]}} & {f1hist1[0],f0hist1[0]});

   assign alignhist0[1:0]    = ({ 2{ f0val[1]           }} &  f0hist0[1:0]          ) |
                               ({ 2{~f0val[1] & f0val[0]}} & {f1hist0[0],f0hist0[0]});

   assign secondpc[31:1]     = ({31{ f0val[1]           }} &  (q0pceff[31:1] + 31'd1)) |
                               // you need the base pc for 2nd one only (4B max, 2B for the 1st and 2B for the 2nd)
                               ({31{~f0val[1] & f0val[0]}} &   q1pceff[31:1]      );


   assign firstpc[31:1]      =  q0pcfinal[31:1];
      end // if (pt.BTB_ENABLE==1)

   assign alignfromf1[1]     =      ~f0val[1] & f0val[0];


   assign ifu_i0_pc[31:1]    =  q0pcfinal[31:1];


   assign ifu_i0_pc4         =  first4B;


   assign ifu_i0_cinst[15:0] = aligndata[15:0];

   assign first4B            = (aligndata[1:0] == 2'b11);
   assign first2B            = ~first4B;

   assign ifu_i0_valid       = (first4B & alignval[1]) |
                               (first2B & alignval[0]);

   // inst access fault on any byte of inst results in access fault for the inst
   assign ifu_i0_icaf        = (first4B & (|alignicaf[1:0])) |
                               (first2B &   alignicaf[0]   );

   assign ifu_i0_icaf_type[1:0] = (first4B & ~f0val[1] & f0val[0] & ~alignicaf[0] & ~aligndbecc[0]) ? f1ictype[1:0] : f0ictype[1:0];


   assign icaf_eff[1:0] = alignicaf[1:0] | aligndbecc[1:0];

   assign ifu_i0_icaf_second = first4B & ~icaf_eff[0] & icaf_eff[1];

   assign ifu_i0_dbecc       = (first4B & (|aligndbecc[1:0])) |
                               (first2B &   aligndbecc[0]   );


   assign ifirst[31:0]       =  aligndata[31:0];


   assign ifu_i0_instr[31:0] = ({32{first4B & alignval[1]}} & ifirst[31:0]) |
                               ({32{first2B & alignval[0]}} & uncompress0[31:0]);

if(pt.BTB_ENABLE==1) begin

   // if you detect br does not start on instruction boundary

   el2_btb_addr_hash #(.pt(pt)) firsthash (.pc(firstpc [pt.BTB_INDEX3_HI:pt.BTB_INDEX1_LO]),
                                            .hash(firstpc_hash [pt.BTB_ADDR_HI:pt.BTB_ADDR_LO]));
   el2_btb_addr_hash #(.pt(pt)) secondhash(.pc(secondpc[pt.BTB_INDEX3_HI:pt.BTB_INDEX1_LO]),
                                            .hash(secondpc_hash[pt.BTB_ADDR_HI:pt.BTB_ADDR_LO]));

   if(pt.BTB_FULLYA) begin
      assign firstbrtag_hash = firstpc;
      assign secondbrtag_hash = secondpc;
   end
   else begin
      if(pt.BTB_BTAG_FOLD) begin : btbfold
         el2_btb_tag_hash_fold #(.pt(pt)) first_brhash (.pc(firstpc [pt.BTB_ADDR_HI+pt.BTB_BTAG_SIZE+pt.BTB_BTAG_SIZE:pt.BTB_ADDR_HI+1]),
                                                         .hash(firstbrtag_hash [pt.BTB_BTAG_SIZE-1:0]));
         el2_btb_tag_hash_fold #(.pt(pt)) second_brhash(.pc(secondpc[pt.BTB_ADDR_HI+pt.BTB_BTAG_SIZE+pt.BTB_BTAG_SIZE:pt.BTB_ADDR_HI+1]),
                                                         .hash(secondbrtag_hash[pt.BTB_BTAG_SIZE-1:0]));
      end
      else begin
         el2_btb_tag_hash #(.pt(pt)) first_brhash (.pc(firstpc [pt.BTB_ADDR_HI+pt.BTB_BTAG_SIZE+pt.BTB_BTAG_SIZE+pt.BTB_BTAG_SIZE:pt.BTB_ADDR_HI+1]),
                                                    .hash(firstbrtag_hash [pt.BTB_BTAG_SIZE-1:0]));
         el2_btb_tag_hash #(.pt(pt)) second_brhash(.pc(secondpc[pt.BTB_ADDR_HI+pt.BTB_BTAG_SIZE+pt.BTB_BTAG_SIZE+pt.BTB_BTAG_SIZE:pt.BTB_ADDR_HI+1]),
                                                    .hash(secondbrtag_hash[pt.BTB_BTAG_SIZE-1:0]));
      end
   end // else: !if(pt.BTB_FULLYA)


   // start_indexing - you want pc to be based on where the end of branch is prediction
   // normal indexing pc based that's incorrect now for pc4 cases it's pc4 + 2

   always_comb begin

      i0_brp                 = '0;

      i0_br_start_error      = (first4B & alignval[1] & alignbrend[0]);

      i0_brp.valid           = (first2B & alignbrend[0]) |
                               (first4B & alignbrend[1]) |
                                i0_br_start_error;

      i0_brp_pc4             = (first2B & alignpc4[0]) |
                               (first4B & alignpc4[1]);

      i0_brp.ret             = (first2B & alignret[0]) |
                               (first4B & alignret[1]);

      i0_brp.way             = (first2B | alignbrend[0])  ?  alignway[0]  :  alignway[1];

      i0_brp.hist[1]         = (first2B & alignhist1[0]) |
                               (first4B & alignhist1[1]);

      i0_brp.hist[0]         = (first2B & alignhist0[0]) |
                               (first4B & alignhist0[1]);

      i0_ends_f1             =  first4B & alignfromf1[1];

      i0_brp.toffset[11:0]   = (i0_ends_f1)  ?  f1poffset[11:0]  :  f0poffset[11:0];

      i0_brp.prett[31:1]     = (i0_ends_f1)  ?  f1prett[31:1]    :  f0prett[31:1];

      i0_brp.br_start_error  = i0_br_start_error;

      i0_brp.bank            = (first2B | alignbrend[0])  ?  firstpc[1]  :  secondpc[1];

      i0_brp.br_error        = (i0_brp.valid &  i0_brp_pc4 &  first2B) |
                               (i0_brp.valid & ~i0_brp_pc4 &  first4B);

      if(pt.BTB_FULLYA)
        ifu_i0_fa_index = (first2B | alignbrend[0])  ?  alignindex[0]  :  alignindex[1];
      else
        ifu_i0_fa_index = '0;

 end


   assign ifu_i0_bp_index[pt.BTB_ADDR_HI:pt.BTB_ADDR_LO] = (first2B | alignbrend[0])  ?  firstpc_hash[pt.BTB_ADDR_HI:pt.BTB_ADDR_LO]  :
                                                                                         secondpc_hash[pt.BTB_ADDR_HI:pt.BTB_ADDR_LO];

   assign ifu_i0_bp_fghr[pt.BHT_GHR_SIZE-1:0]            = (i0_ends_f1)               ?  f1fghr[pt.BHT_GHR_SIZE-1:0]  :
                                                                                         f0fghr[pt.BHT_GHR_SIZE-1:0];

   assign ifu_i0_bp_btag[pt.BTB_BTAG_SIZE-1:0]           = (first2B | alignbrend[0])  ?  firstbrtag_hash[pt.BTB_BTAG_SIZE-1:0]  :
                                                                                         secondbrtag_hash[pt.BTB_BTAG_SIZE-1:0];
end
else begin
   assign i0_brp = '0;
   assign ifu_i0_bp_index = '0;
   assign ifu_i0_bp_fghr = '0;
   assign ifu_i0_bp_btag = '0;
end // else: !if(pt.BTB_ENABLE==1)

   // decompress

   // quiet inputs for 4B inst
   el2_ifu_compress_ctl compress0 (.din((first2B) ? aligndata[15:0] : '0), .dout(uncompress0[31:0]));



   assign i0_shift           =  dec_i0_decode_d & ~error_stall;

   assign ifu_pmu_instr_aligned = i0_shift;


   // compute how many bytes are being shifted from f0

   assign shift_2B           =  i0_shift & first2B;

   assign shift_4B           =  i0_shift & first4B;

   // exact equations for the queue logic
   assign f0_shift_2B        = (shift_2B & f0val[0]            ) |
                               (shift_4B & f0val[0] & ~f0val[1]);


   // f0 valid states
   //     11
   //     10
   //     00

   assign f1_shift_2B        =  f0val[0] & ~f0val[1] & shift_4B;



endmodule
