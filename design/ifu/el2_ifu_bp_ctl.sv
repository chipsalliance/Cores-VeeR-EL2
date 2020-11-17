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
// Function: Branch predictor
// Comments:
//
//
//  Bank3 : Bank2 : Bank1 : Bank0
//  FA  C       8       4       0
//********************************************************************************

module el2_ifu_bp_ctl
import el2_pkg::*;
#(
`include "el2_param.vh"
 )
  (

   input logic clk,
   input logic rst_l,

   input logic ic_hit_f,      // Icache hit, enables F address capture

   input logic [31:1] ifc_fetch_addr_f, // look up btb address
   input logic ifc_fetch_req_f,  // F1 valid

   input el2_br_tlu_pkt_t dec_tlu_br0_r_pkt, // BP commit update packet, includes errors
   input logic [pt.BHT_GHR_SIZE-1:0] exu_i0_br_fghr_r, // fghr to bp
   input logic [pt.BTB_ADDR_HI:pt.BTB_ADDR_LO] exu_i0_br_index_r, // bp index

   input logic [$clog2(pt.BTB_SIZE)-1:0] dec_fa_error_index, // Fully associative btb error index

   input logic dec_tlu_flush_lower_wb, // used to move EX4 RS to EX1 and F
   input logic dec_tlu_flush_leak_one_wb, // don't hit for leak one fetches

   input logic dec_tlu_bpred_disable, // disable all branch prediction

   input el2_predict_pkt_t  exu_mp_pkt, // mispredict packet

   input logic [pt.BHT_GHR_SIZE-1:0] exu_mp_eghr, // execute ghr (for patching fghr)
   input logic [pt.BHT_GHR_SIZE-1:0]  exu_mp_fghr,                    // Mispredict fghr
   input logic [pt.BTB_ADDR_HI:pt.BTB_ADDR_LO]  exu_mp_index,         // Mispredict index
   input logic [pt.BTB_BTAG_SIZE-1:0]  exu_mp_btag,                   // Mispredict btag

   input logic exu_flush_final, // all flushes

   output logic ifu_bp_hit_taken_f, // btb hit, select target
   output logic [31:1] ifu_bp_btb_target_f, //  predicted target PC
   output logic ifu_bp_inst_mask_f, // tell ic which valids to kill because of a taken branch, right justified

   output logic [pt.BHT_GHR_SIZE-1:0] ifu_bp_fghr_f, // fetch ghr

   output logic [1:0] ifu_bp_way_f, // way
   output logic [1:0] ifu_bp_ret_f, // predicted ret
   output logic [1:0] ifu_bp_hist1_f, // history counters for all 4 potential branches, bit 1, right justified
   output logic [1:0] ifu_bp_hist0_f, // history counters for all 4 potential branches, bit 0, right justified
   output logic [1:0] ifu_bp_pc4_f, // pc4 indication, right justified
   output logic [1:0] ifu_bp_valid_f, // branch valid, right justified
   output logic [11:0] ifu_bp_poffset_f, // predicted target

   output logic [1:0] [$clog2(pt.BTB_SIZE)-1:0]    ifu_bp_fa_index_f, // predicted branch index (fully associative option)

   input  logic       scan_mode
   );


   localparam BTB_DWIDTH =  pt.BTB_TOFFSET_SIZE+pt.BTB_BTAG_SIZE+5;
   localparam BTB_DWIDTH_TOP =  int'(pt.BTB_TOFFSET_SIZE)+int'(pt.BTB_BTAG_SIZE)+4;
   localparam BTB_FA_INDEX = $clog2(pt.BTB_SIZE)-1;
   localparam FA_CMP_LOWER = $clog2(pt.ICACHE_LN_SZ);
   localparam FA_TAG_END_UPPER= 5+int'(pt.BTB_TOFFSET_SIZE)+int'(FA_CMP_LOWER)-1; // must cast to int or vcs build fails
   localparam FA_TAG_START_LOWER = 3+int'(pt.BTB_TOFFSET_SIZE)+int'(FA_CMP_LOWER);
   localparam FA_TAG_END_LOWER = 5+int'(pt.BTB_TOFFSET_SIZE);

   localparam TAG_START=BTB_DWIDTH-1;
   localparam PC4=4;
   localparam BOFF=3;
   localparam CALL=2;
   localparam RET=1;
   localparam BV=0;

   localparam LRU_SIZE=pt.BTB_ARRAY_DEPTH;
   localparam NUM_BHT_LOOP = (pt.BHT_ARRAY_DEPTH > 16 ) ? 16 : pt.BHT_ARRAY_DEPTH;
   localparam NUM_BHT_LOOP_INNER_HI =  (pt.BHT_ARRAY_DEPTH > 16 ) ?pt.BHT_ADDR_LO+3 : pt.BHT_ADDR_HI;
   localparam NUM_BHT_LOOP_OUTER_LO =  (pt.BHT_ARRAY_DEPTH > 16 ) ?pt.BHT_ADDR_LO+4 : pt.BHT_ADDR_LO;
   localparam BHT_NO_ADDR_MATCH  = ( pt.BHT_ARRAY_DEPTH <= 16 );


   logic exu_mp_valid_write;
   logic exu_mp_ataken;
   logic exu_mp_valid; // conditional branch mispredict
   logic exu_mp_boffset; // branch offsett
   logic exu_mp_pc4; // branch is a 4B inst
   logic exu_mp_call; // branch is a call inst
   logic exu_mp_ret; // branch is a ret inst
   logic exu_mp_ja; // branch is a jump always
   logic [1:0] exu_mp_hist; // new history
   logic [11:0] exu_mp_tgt; // target offset
   logic [pt.BTB_ADDR_HI:pt.BTB_ADDR_LO] exu_mp_addr; // BTB/BHT address
   logic                                   dec_tlu_br0_v_wb; // WB stage history update
   logic [1:0]                             dec_tlu_br0_hist_wb; // new history
   logic [pt.BTB_ADDR_HI:pt.BTB_ADDR_LO] dec_tlu_br0_addr_wb; // addr
   logic                                   dec_tlu_br0_error_wb; // error; invalidate bank
   logic                                   dec_tlu_br0_start_error_wb; // error; invalidate all 4 banks in fg
   logic [pt.BHT_GHR_SIZE-1:0]             exu_i0_br_fghr_wb;

   logic use_mp_way, use_mp_way_p1;
   logic [pt.RET_STACK_SIZE-1:0][31:0] rets_out, rets_in;
   logic [pt.RET_STACK_SIZE-1:0]        rsenable;


   logic [11:0]       btb_rd_tgt_f;
   logic              btb_rd_pc4_f, btb_rd_call_f, btb_rd_ret_f;
   logic [1:1]        bp_total_branch_offset_f;

   logic [31:1]       bp_btb_target_adder_f;
   logic [31:1]       bp_rs_call_target_f;
   logic              rs_push, rs_pop, rs_hold;
   logic [pt.BTB_ADDR_HI:pt.BTB_ADDR_LO] btb_rd_addr_p1_f, btb_wr_addr, btb_rd_addr_f;
   logic [pt.BTB_BTAG_SIZE-1:0] btb_wr_tag, fetch_rd_tag_f, fetch_rd_tag_p1_f;
   logic [BTB_DWIDTH-1:0]        btb_wr_data;
   logic               btb_wr_en_way0, btb_wr_en_way1;


   logic               dec_tlu_error_wb, btb_valid, dec_tlu_br0_middle_wb;
   logic [pt.BTB_ADDR_HI:pt.BTB_ADDR_LO]        btb_error_addr_wb;
   logic branch_error_collision_f, fetch_mp_collision_f, branch_error_collision_p1_f, fetch_mp_collision_p1_f;

   logic  branch_error_bank_conflict_f;
   logic [pt.BHT_GHR_SIZE-1:0] merged_ghr, fghr_ns, fghr;
   logic [1:0] num_valids;
   logic [LRU_SIZE-1:0] btb_lru_b0_f, btb_lru_b0_hold, btb_lru_b0_ns,
                        fetch_wrindex_dec, fetch_wrindex_p1_dec, fetch_wrlru_b0, fetch_wrlru_p1_b0,
                        mp_wrindex_dec, mp_wrlru_b0;
   logic                btb_lru_rd_f, btb_lru_rd_p1_f, lru_update_valid_f;
   logic  tag_match_way0_f, tag_match_way1_f;
   logic [1:0] way_raw, bht_dir_f, btb_sel_f, wayhit_f, vwayhit_f, wayhit_p1_f;
   logic [1:0] bht_valid_f, bht_force_taken_f;

   logic leak_one_f, leak_one_f_d1;

   logic [LRU_SIZE-1:0][BTB_DWIDTH-1:0]  btb_bank0_rd_data_way0_out ;

   logic [LRU_SIZE-1:0][BTB_DWIDTH-1:0]  btb_bank0_rd_data_way1_out ;

   logic                [BTB_DWIDTH-1:0] btb_bank0_rd_data_way0_f ;
   logic                [BTB_DWIDTH-1:0] btb_bank0_rd_data_way1_f ;

   logic                [BTB_DWIDTH-1:0] btb_bank0_rd_data_way0_p1_f ;
   logic                [BTB_DWIDTH-1:0] btb_bank0_rd_data_way1_p1_f ;

   logic                [BTB_DWIDTH-1:0] btb_vbank0_rd_data_f, btb_vbank1_rd_data_f;

   logic                                         final_h;
   logic                                         btb_fg_crossing_f;
   logic                                         middle_of_bank;


   logic [1:0]                                   bht_vbank0_rd_data_f, bht_vbank1_rd_data_f;
   logic                                         branch_error_bank_conflict_p1_f;
   logic                                         tag_match_way0_p1_f, tag_match_way1_p1_f;

   logic [1:0]                                   btb_vlru_rd_f, fetch_start_f, tag_match_vway1_expanded_f, tag_match_way0_expanded_p1_f, tag_match_way1_expanded_p1_f;
   logic [31:2] fetch_addr_p1_f;


   logic exu_mp_way, exu_mp_way_f, dec_tlu_br0_way_wb, dec_tlu_way_wb;
   logic                [BTB_DWIDTH-1:0] btb_bank0e_rd_data_f, btb_bank0e_rd_data_p1_f;

   logic                [BTB_DWIDTH-1:0] btb_bank0o_rd_data_f;

   logic [1:0] tag_match_way0_expanded_f, tag_match_way1_expanded_f;


    logic [1:0]                                  bht_bank0_rd_data_f;
    logic [1:0]                                  bht_bank1_rd_data_f;
    logic [1:0]                                  bht_bank0_rd_data_p1_f;
   genvar                                        j, i;

   assign exu_mp_valid = exu_mp_pkt.misp & ~leak_one_f; // conditional branch mispredict
   assign exu_mp_boffset = exu_mp_pkt.boffset;  // branch offset
   assign exu_mp_pc4 = exu_mp_pkt.pc4;  // branch is a 4B inst
   assign exu_mp_call = exu_mp_pkt.pcall;  // branch is a call inst
   assign exu_mp_ret = exu_mp_pkt.pret;  // branch is a ret inst
   assign exu_mp_ja = exu_mp_pkt.pja;  // branch is a jump always
   assign exu_mp_way = exu_mp_pkt.way;  // repl way
   assign exu_mp_hist[1:0] = exu_mp_pkt.hist[1:0];  // new history
   assign exu_mp_tgt[11:0]  = exu_mp_pkt.toffset[11:0] ;  // target offset
   assign exu_mp_addr[pt.BTB_ADDR_HI:pt.BTB_ADDR_LO]  = exu_mp_index[pt.BTB_ADDR_HI:pt.BTB_ADDR_LO] ;  // BTB/BHT address
   assign exu_mp_ataken = exu_mp_pkt.ataken;


   assign dec_tlu_br0_v_wb = dec_tlu_br0_r_pkt.valid;
   assign dec_tlu_br0_hist_wb[1:0]  = dec_tlu_br0_r_pkt.hist[1:0];
   assign dec_tlu_br0_addr_wb[pt.BTB_ADDR_HI:pt.BTB_ADDR_LO] = exu_i0_br_index_r[pt.BTB_ADDR_HI:pt.BTB_ADDR_LO];
   assign dec_tlu_br0_error_wb = dec_tlu_br0_r_pkt.br_error;
   assign dec_tlu_br0_middle_wb = dec_tlu_br0_r_pkt.middle;
   assign dec_tlu_br0_way_wb = dec_tlu_br0_r_pkt.way;
   assign dec_tlu_br0_start_error_wb = dec_tlu_br0_r_pkt.br_start_error;
   assign exu_i0_br_fghr_wb[pt.BHT_GHR_SIZE-1:0] = exu_i0_br_fghr_r[pt.BHT_GHR_SIZE-1:0];




   // ----------------------------------------------------------------------
   // READ
   // ----------------------------------------------------------------------

   // hash the incoming fetch PC, first guess at hashing algorithm
   el2_btb_addr_hash #(.pt(pt)) f1hash(.pc(ifc_fetch_addr_f[pt.BTB_INDEX3_HI:pt.BTB_INDEX1_LO]), .hash(btb_rd_addr_f[pt.BTB_ADDR_HI:pt.BTB_ADDR_LO]));


   assign fetch_addr_p1_f[31:2] = ifc_fetch_addr_f[31:2] + 30'b1;
   el2_btb_addr_hash #(.pt(pt)) f1hash_p1(.pc(fetch_addr_p1_f[pt.BTB_INDEX3_HI:pt.BTB_INDEX1_LO]), .hash(btb_rd_addr_p1_f[pt.BTB_ADDR_HI:pt.BTB_ADDR_LO]));

   assign btb_sel_f[1] = ~bht_dir_f[0];
   assign btb_sel_f[0] =  bht_dir_f[0];

   assign fetch_start_f[1:0] = {ifc_fetch_addr_f[1], ~ifc_fetch_addr_f[1]};

   // Errors colliding with fetches must kill the btb/bht hit.

   assign branch_error_collision_f = dec_tlu_error_wb & (btb_error_addr_wb[pt.BTB_ADDR_HI:pt.BTB_ADDR_LO] == btb_rd_addr_f[pt.BTB_ADDR_HI:pt.BTB_ADDR_LO]);
   assign branch_error_collision_p1_f = dec_tlu_error_wb & (btb_error_addr_wb[pt.BTB_ADDR_HI:pt.BTB_ADDR_LO] == btb_rd_addr_p1_f[pt.BTB_ADDR_HI:pt.BTB_ADDR_LO]);

   assign branch_error_bank_conflict_f = branch_error_collision_f & dec_tlu_error_wb;
   assign branch_error_bank_conflict_p1_f = branch_error_collision_p1_f & dec_tlu_error_wb;

   // set on leak one, hold until next flush without leak one
   assign leak_one_f = (dec_tlu_flush_leak_one_wb & dec_tlu_flush_lower_wb) | (leak_one_f_d1 & ~dec_tlu_flush_lower_wb);

logic exu_flush_final_d1;

 if(!pt.BTB_FULLYA) begin
   assign fetch_mp_collision_f = ( (exu_mp_btag[pt.BTB_BTAG_SIZE-1:0] == fetch_rd_tag_f[pt.BTB_BTAG_SIZE-1:0]) &
                                    exu_mp_valid & ifc_fetch_req_f &
                                    (exu_mp_addr[pt.BTB_ADDR_HI:pt.BTB_ADDR_LO] == btb_rd_addr_f[pt.BTB_ADDR_HI:pt.BTB_ADDR_LO])
                                    );
   assign fetch_mp_collision_p1_f = ( (exu_mp_btag[pt.BTB_BTAG_SIZE-1:0] == fetch_rd_tag_p1_f[pt.BTB_BTAG_SIZE-1:0]) &
                                       exu_mp_valid & ifc_fetch_req_f &
                                       (exu_mp_addr[pt.BTB_ADDR_HI:pt.BTB_ADDR_LO] == btb_rd_addr_p1_f[pt.BTB_ADDR_HI:pt.BTB_ADDR_LO])
                                       );
   // 2 -way SA, figure out the way hit and mux accordingly
   assign tag_match_way0_f = btb_bank0_rd_data_way0_f[BV] & (btb_bank0_rd_data_way0_f[TAG_START:17] == fetch_rd_tag_f[pt.BTB_BTAG_SIZE-1:0]) &
                              ~(dec_tlu_way_wb & branch_error_bank_conflict_f) & ifc_fetch_req_f & ~leak_one_f;

   assign tag_match_way1_f = btb_bank0_rd_data_way1_f[BV] & (btb_bank0_rd_data_way1_f[TAG_START:17] == fetch_rd_tag_f[pt.BTB_BTAG_SIZE-1:0]) &
                              ~(dec_tlu_way_wb & branch_error_bank_conflict_f) & ifc_fetch_req_f & ~leak_one_f;

   assign tag_match_way0_p1_f = btb_bank0_rd_data_way0_p1_f[BV] & (btb_bank0_rd_data_way0_p1_f[TAG_START:17] == fetch_rd_tag_p1_f[pt.BTB_BTAG_SIZE-1:0]) &
                              ~(dec_tlu_way_wb & branch_error_bank_conflict_p1_f) & ifc_fetch_req_f & ~leak_one_f;

   assign tag_match_way1_p1_f = btb_bank0_rd_data_way1_p1_f[BV] & (btb_bank0_rd_data_way1_p1_f[TAG_START:17] == fetch_rd_tag_p1_f[pt.BTB_BTAG_SIZE-1:0]) &
                              ~(dec_tlu_way_wb & branch_error_bank_conflict_p1_f) & ifc_fetch_req_f & ~leak_one_f;


   // Both ways could hit, use the offset bit to reorder

   assign tag_match_way0_expanded_f[1:0] = {tag_match_way0_f &  (btb_bank0_rd_data_way0_f[BOFF] ^ btb_bank0_rd_data_way0_f[PC4]),
                                             tag_match_way0_f & ~(btb_bank0_rd_data_way0_f[BOFF] ^ btb_bank0_rd_data_way0_f[PC4])};

   assign tag_match_way1_expanded_f[1:0] = {tag_match_way1_f &  (btb_bank0_rd_data_way1_f[BOFF] ^ btb_bank0_rd_data_way1_f[PC4]),
                                             tag_match_way1_f & ~(btb_bank0_rd_data_way1_f[BOFF] ^ btb_bank0_rd_data_way1_f[PC4])};

   assign tag_match_way0_expanded_p1_f[1:0] = {tag_match_way0_p1_f &  (btb_bank0_rd_data_way0_p1_f[BOFF] ^ btb_bank0_rd_data_way0_p1_f[PC4]),
                                                tag_match_way0_p1_f & ~(btb_bank0_rd_data_way0_p1_f[BOFF] ^ btb_bank0_rd_data_way0_p1_f[PC4])};

   assign tag_match_way1_expanded_p1_f[1:0] = {tag_match_way1_p1_f &  (btb_bank0_rd_data_way1_p1_f[BOFF] ^ btb_bank0_rd_data_way1_p1_f[PC4]),
                                                tag_match_way1_p1_f & ~(btb_bank0_rd_data_way1_p1_f[BOFF] ^ btb_bank0_rd_data_way1_p1_f[PC4])};

   assign wayhit_f[1:0] = tag_match_way0_expanded_f[1:0] | tag_match_way1_expanded_f[1:0];
   assign wayhit_p1_f[1:0] = tag_match_way0_expanded_p1_f[1:0] | tag_match_way1_expanded_p1_f[1:0];

   assign btb_bank0o_rd_data_f[BTB_DWIDTH-1:0] = ( ({17+pt.BTB_BTAG_SIZE{tag_match_way0_expanded_f[1]}} & btb_bank0_rd_data_way0_f[BTB_DWIDTH-1:0]) |
                                                            ({17+pt.BTB_BTAG_SIZE{tag_match_way1_expanded_f[1]}} & btb_bank0_rd_data_way1_f[BTB_DWIDTH-1:0]) );
   assign btb_bank0e_rd_data_f[BTB_DWIDTH-1:0] = ( ({17+pt.BTB_BTAG_SIZE{tag_match_way0_expanded_f[0]}} & btb_bank0_rd_data_way0_f[BTB_DWIDTH-1:0]) |
                                                            ({17+pt.BTB_BTAG_SIZE{tag_match_way1_expanded_f[0]}} & btb_bank0_rd_data_way1_f[BTB_DWIDTH-1:0]) );

   assign btb_bank0e_rd_data_p1_f[BTB_DWIDTH-1:0] = ( ({17+pt.BTB_BTAG_SIZE{tag_match_way0_expanded_p1_f[0]}} & btb_bank0_rd_data_way0_p1_f[BTB_DWIDTH-1:0]) |
                                                               ({17+pt.BTB_BTAG_SIZE{tag_match_way1_expanded_p1_f[0]}} & btb_bank0_rd_data_way1_p1_f[BTB_DWIDTH-1:0]) );

   // virtual bank order

   assign btb_vbank0_rd_data_f[BTB_DWIDTH-1:0] = ( ({17+pt.BTB_BTAG_SIZE{fetch_start_f[0]}} &  btb_bank0e_rd_data_f[BTB_DWIDTH-1:0]) |
                                                            ({17+pt.BTB_BTAG_SIZE{fetch_start_f[1]}} &  btb_bank0o_rd_data_f[BTB_DWIDTH-1:0]) );
   assign btb_vbank1_rd_data_f[BTB_DWIDTH-1:0] = ( ({17+pt.BTB_BTAG_SIZE{fetch_start_f[0]}} &  btb_bank0o_rd_data_f[BTB_DWIDTH-1:0]) |
                                                            ({17+pt.BTB_BTAG_SIZE{fetch_start_f[1]}} &  btb_bank0e_rd_data_p1_f[BTB_DWIDTH-1:0]) );

   assign way_raw[1:0] =  tag_match_vway1_expanded_f[1:0] | (~vwayhit_f[1:0] & btb_vlru_rd_f[1:0]);

   // --------------------------------------------------------------------------------
   // --------------------------------------------------------------------------------
   // update lru
   // mp

   // create a onehot lru write vector
   assign mp_wrindex_dec[LRU_SIZE-1:0] = {{LRU_SIZE-1{1'b0}},1'b1} <<  exu_mp_addr[pt.BTB_ADDR_HI:pt.BTB_ADDR_LO];

   // fetch
   assign fetch_wrindex_dec[LRU_SIZE-1:0] = {{LRU_SIZE-1{1'b0}},1'b1} <<  btb_rd_addr_f[pt.BTB_ADDR_HI:pt.BTB_ADDR_LO];
   assign fetch_wrindex_p1_dec[LRU_SIZE-1:0] = {{LRU_SIZE-1{1'b0}},1'b1} <<  btb_rd_addr_p1_f[pt.BTB_ADDR_HI:pt.BTB_ADDR_LO];

   assign mp_wrlru_b0[LRU_SIZE-1:0] = mp_wrindex_dec[LRU_SIZE-1:0] & {LRU_SIZE{exu_mp_valid}};


   assign btb_lru_b0_hold[LRU_SIZE-1:0] = ~mp_wrlru_b0[LRU_SIZE-1:0] & ~fetch_wrlru_b0[LRU_SIZE-1:0];

   // Forward the mp lru information to the fetch, avoids multiple way hits later
   assign use_mp_way = fetch_mp_collision_f;
   assign use_mp_way_p1 = fetch_mp_collision_p1_f;

   assign lru_update_valid_f = (vwayhit_f[0] | vwayhit_f[1]) & ifc_fetch_req_f & ~leak_one_f;


   assign fetch_wrlru_b0[LRU_SIZE-1:0] = fetch_wrindex_dec[LRU_SIZE-1:0] &
                                         {LRU_SIZE{lru_update_valid_f}};
   assign fetch_wrlru_p1_b0[LRU_SIZE-1:0] = fetch_wrindex_p1_dec[LRU_SIZE-1:0] &
                                         {LRU_SIZE{lru_update_valid_f}};

   assign btb_lru_b0_ns[LRU_SIZE-1:0] = ( (btb_lru_b0_hold[LRU_SIZE-1:0] & btb_lru_b0_f[LRU_SIZE-1:0]) |
                                          (mp_wrlru_b0[LRU_SIZE-1:0] & {LRU_SIZE{~exu_mp_way}}) |
                                          (fetch_wrlru_b0[LRU_SIZE-1:0] & {LRU_SIZE{tag_match_way0_f}}) |
                                          (fetch_wrlru_p1_b0[LRU_SIZE-1:0] & {LRU_SIZE{tag_match_way0_p1_f}}) );



   assign btb_lru_rd_f = use_mp_way ? exu_mp_way_f : |(fetch_wrindex_dec[LRU_SIZE-1:0] & btb_lru_b0_f[LRU_SIZE-1:0]);

   assign btb_lru_rd_p1_f = use_mp_way_p1 ? exu_mp_way_f : |(fetch_wrindex_p1_dec[LRU_SIZE-1:0] & btb_lru_b0_f[LRU_SIZE-1:0]);

   // rotated
   assign btb_vlru_rd_f[1:0] = ( ({2{fetch_start_f[0]}} & {btb_lru_rd_f, btb_lru_rd_f}) |
                                  ({2{fetch_start_f[1]}} & {btb_lru_rd_p1_f, btb_lru_rd_f}));

   assign tag_match_vway1_expanded_f[1:0] = ( ({2{fetch_start_f[0]}} & {tag_match_way1_expanded_f[1:0]}) |
                                               ({2{fetch_start_f[1]}} & {tag_match_way1_expanded_p1_f[0], tag_match_way1_expanded_f[1]}) );


   rvdffe #(LRU_SIZE) btb_lru_ff (.*, .en(ifc_fetch_req_f | exu_mp_valid),
                                    .din(btb_lru_b0_ns[(LRU_SIZE)-1:0]),
                                   .dout(btb_lru_b0_f[(LRU_SIZE)-1:0]));

 end // if (!pt.BTB_FULLYA)
   // Detect end of cache line and mask as needed
   logic eoc_near;
   logic eoc_mask;
   assign eoc_near = &ifc_fetch_addr_f[pt.ICACHE_BEAT_ADDR_HI:3];
   assign eoc_mask = ~eoc_near| (|(~ifc_fetch_addr_f[2:1]));



   // --------------------------------------------------------------------------------
   // --------------------------------------------------------------------------------

   // mux out critical hit bank for pc computation
   // This is only useful for the first taken branch in the fetch group
   logic [16:1] btb_sel_data_f;

   assign btb_rd_tgt_f[11:0] = btb_sel_data_f[16:5];
   assign btb_rd_pc4_f       = btb_sel_data_f[4];
   assign btb_rd_call_f      = btb_sel_data_f[2];
   assign btb_rd_ret_f       = btb_sel_data_f[1];

   assign btb_sel_data_f[16:1] = ( ({16{btb_sel_f[1]}} & btb_vbank1_rd_data_f[16:1]) |
                                    ({16{btb_sel_f[0]}} & btb_vbank0_rd_data_f[16:1]) );


   logic [1:0] hist0_raw, hist1_raw, pc4_raw, pret_raw;

   // a valid taken target needs to kill the next fetch as we compute the target address
   assign ifu_bp_hit_taken_f = |(vwayhit_f[1:0] & hist1_raw[1:0]) & ifc_fetch_req_f & ~leak_one_f_d1 & ~dec_tlu_bpred_disable;


   // Don't put calls/rets/ja in the predictor, force the bht taken instead
   assign bht_force_taken_f[1:0] = {(btb_vbank1_rd_data_f[CALL] | btb_vbank1_rd_data_f[RET]),
                                     (btb_vbank0_rd_data_f[CALL] | btb_vbank0_rd_data_f[RET])};


   // taken and valid, otherwise, branch errors must clear the bht
   assign bht_valid_f[1:0] = vwayhit_f[1:0];

   assign bht_vbank0_rd_data_f[1:0] = ( ({2{fetch_start_f[0]}} & bht_bank0_rd_data_f[1:0]) |
                                         ({2{fetch_start_f[1]}} & bht_bank1_rd_data_f[1:0]) );

   assign bht_vbank1_rd_data_f[1:0] = ( ({2{fetch_start_f[0]}} & bht_bank1_rd_data_f[1:0]) |
                                         ({2{fetch_start_f[1]}} & bht_bank0_rd_data_p1_f[1:0]) );


   assign bht_dir_f[1:0] = {(bht_force_taken_f[1] | bht_vbank1_rd_data_f[1]) & bht_valid_f[1],
                             (bht_force_taken_f[0] | bht_vbank0_rd_data_f[1]) & bht_valid_f[0]};

   assign ifu_bp_inst_mask_f = (ifu_bp_hit_taken_f & btb_sel_f[1]) | ~ifu_bp_hit_taken_f;




   // Branch prediction info is sent with the 2byte lane associated with the end of the branch.
   // Cases
   //       BANK1         BANK0
   // -------------------------------
   // |      :       |      :       |
   // -------------------------------
   //         <------------>                   : PC4 branch, offset, should be in B1 (indicated on [2])
   //                <------------>            : PC4 branch, no offset, indicate PC4, VALID, HIST on [1]
   //                       <------------>     : PC4 branch, offset, indicate PC4, VALID, HIST on [0]
   //                <------>                  : PC2 branch, offset, indicate VALID, HIST on [1]
   //                       <------>           : PC2 branch, no offset, indicate VALID, HIST on [0]
   //



   assign hist1_raw[1:0] = bht_force_taken_f[1:0] | {bht_vbank1_rd_data_f[1],
                                                      bht_vbank0_rd_data_f[1]};

   assign hist0_raw[1:0] = {bht_vbank1_rd_data_f[0],
                            bht_vbank0_rd_data_f[0]};


   assign pc4_raw[1:0] = {vwayhit_f[1] & btb_vbank1_rd_data_f[PC4],
                          vwayhit_f[0] & btb_vbank0_rd_data_f[PC4]};

   assign pret_raw[1:0] = {vwayhit_f[1] & ~btb_vbank1_rd_data_f[CALL] & btb_vbank1_rd_data_f[RET],
                           vwayhit_f[0] & ~btb_vbank0_rd_data_f[CALL] & btb_vbank0_rd_data_f[RET]};

   // GHR


  // count the valids with masking based on first taken
   assign num_valids[1:0] = countones(bht_valid_f[1:0]);

   // Note that the following property holds
   // P: prior ghr, H: history bit of last valid branch in line (could be 1 or 0)
   // Num valid branches   What new GHR must be
   // 2                    0H
   // 1                    PH
   // 0                    PP

   assign final_h = |(btb_sel_f[1:0] & bht_dir_f[1:0]);

   assign merged_ghr[pt.BHT_GHR_SIZE-1:0] = (
                                            ({pt.BHT_GHR_SIZE{num_valids[1:0] == 2'h2}} & {fghr[pt.BHT_GHR_SIZE-3:0], 1'b0, final_h}) | // 0H
                                            ({pt.BHT_GHR_SIZE{num_valids[1:0] == 2'h1}} & {fghr[pt.BHT_GHR_SIZE-2:0], final_h}) | // PH
                                            ({pt.BHT_GHR_SIZE{num_valids[1:0] == 2'h0}} & {fghr[pt.BHT_GHR_SIZE-1:0]}) ); // PP

   logic [pt.BHT_GHR_SIZE-1:0] exu_flush_ghr;
   assign exu_flush_ghr[pt.BHT_GHR_SIZE-1:0] = exu_mp_fghr[pt.BHT_GHR_SIZE-1:0];

   assign fghr_ns[pt.BHT_GHR_SIZE-1:0] = ( ({pt.BHT_GHR_SIZE{exu_flush_final_d1}} & exu_flush_ghr[pt.BHT_GHR_SIZE-1:0]) |
                                         ({pt.BHT_GHR_SIZE{~exu_flush_final_d1 & ifc_fetch_req_f & ic_hit_f & ~leak_one_f_d1}} & merged_ghr[pt.BHT_GHR_SIZE-1:0]) |
                                         ({pt.BHT_GHR_SIZE{~exu_flush_final_d1 & ~(ifc_fetch_req_f & ic_hit_f & ~leak_one_f_d1)}} & fghr[pt.BHT_GHR_SIZE-1:0]));

   rvdffie #(.WIDTH(pt.BHT_GHR_SIZE+3),.OVERRIDE(1)) fetchghr (.*,
                                          .din ({exu_flush_final, exu_mp_way, leak_one_f, fghr_ns[pt.BHT_GHR_SIZE-1:0]}),
                                          .dout({exu_flush_final_d1, exu_mp_way_f, leak_one_f_d1, fghr[pt.BHT_GHR_SIZE-1:0]}));

   assign ifu_bp_fghr_f[pt.BHT_GHR_SIZE-1:0] = fghr[pt.BHT_GHR_SIZE-1:0];


   assign ifu_bp_way_f[1:0] = way_raw[1:0];
   assign ifu_bp_hist1_f[1:0]    = hist1_raw[1:0];
   assign ifu_bp_hist0_f[1:0]    = hist0_raw[1:0];
   assign ifu_bp_pc4_f[1:0]     = pc4_raw[1:0];

   assign ifu_bp_valid_f[1:0]   = vwayhit_f[1:0] & ~{2{dec_tlu_bpred_disable}};
   assign ifu_bp_ret_f[1:0]     = pret_raw[1:0];


   // compute target
   // Form the fetch group offset based on the btb hit location and the location of the branch within the 4 byte chunk

//  .i 5
//  .o 3
//  .ilb bht_dir_f[1] bht_dir_f[0] fetch_start_f[1] fetch_start_f[0] btb_rd_pc4_f
//  .ob bloc_f[1] bloc_f[0] use_fa_plus
//  .type fr
//
//
//  ## rotdir[1:0]  fs   pc4  off fapl
//    -1            01 -  01  0
//    10            01 -  10  0
//
//    -1            10 -  10  0
//    10            10 0  01  1
//    10            10 1  01  0
logic [1:0] bloc_f;
logic use_fa_plus;
assign bloc_f[1] = (bht_dir_f[0] & ~fetch_start_f[0]) | (~bht_dir_f[0]
     & fetch_start_f[0]);
assign bloc_f[0] = (bht_dir_f[0] & fetch_start_f[0]) | (~bht_dir_f[0]
     & ~fetch_start_f[0]);
assign use_fa_plus = (~bht_dir_f[0] & ~fetch_start_f[0] & ~btb_rd_pc4_f);




    assign btb_fg_crossing_f = fetch_start_f[0] & btb_sel_f[0] & btb_rd_pc4_f;

   assign bp_total_branch_offset_f =  bloc_f[1] ^ btb_rd_pc4_f;

   logic [31:2] adder_pc_in_f, ifc_fetch_adder_prior;
   rvdfflie #(.WIDTH(30), .LEFT(19)) faddrf_ff (.*, .en(ifc_fetch_req_f & ~ifu_bp_hit_taken_f & ic_hit_f), .din(ifc_fetch_addr_f[31:2]), .dout(ifc_fetch_adder_prior[31:2]));


   assign ifu_bp_poffset_f[11:0] = btb_rd_tgt_f[11:0];

   assign adder_pc_in_f[31:2] = ( ({30{ use_fa_plus}} & fetch_addr_p1_f[31:2]) |
                                   ({30{ btb_fg_crossing_f}} & ifc_fetch_adder_prior[31:2]) |
                                   ({30{~btb_fg_crossing_f & ~use_fa_plus}} & ifc_fetch_addr_f[31:2]));

   rvbradder predtgt_addr (.pc({adder_pc_in_f[31:2], bp_total_branch_offset_f}),
                         .offset(btb_rd_tgt_f[11:0]),
                         .dout(bp_btb_target_adder_f[31:1])
                         );
   // mux in the return stack address here for a predicted return assuming the RS is valid, quite if no prediction
   assign ifu_bp_btb_target_f[31:1] = (({31{btb_rd_ret_f & ~btb_rd_call_f & rets_out[0][0] & ifu_bp_hit_taken_f}} & rets_out[0][31:1]) |
                                       ({31{~(btb_rd_ret_f & ~btb_rd_call_f & rets_out[0][0]) & ifu_bp_hit_taken_f}} & bp_btb_target_adder_f[31:1]) );


   // ----------------------------------------------------------------------
   // Return Stack
   // ----------------------------------------------------------------------

   rvbradder rs_addr (.pc({adder_pc_in_f[31:2], bp_total_branch_offset_f}),
                    .offset({11'b0,  ~btb_rd_pc4_f}),
                    .dout(bp_rs_call_target_f[31:1])
                         );

   assign rs_push = (btb_rd_call_f & ~btb_rd_ret_f & ifu_bp_hit_taken_f);
   assign rs_pop = (btb_rd_ret_f & ~btb_rd_call_f & ifu_bp_hit_taken_f);
   assign rs_hold = ~rs_push & ~rs_pop;



   // Fetch based (bit 0 is a valid)
   assign rets_in[0][31:0] = ( ({32{rs_push}} & {bp_rs_call_target_f[31:1], 1'b1}) | // target[31:1], valid
                               ({32{rs_pop}}  & rets_out[1][31:0]) );

   assign rsenable[0] = ~rs_hold;

   for (i=0; i<pt.RET_STACK_SIZE; i++) begin : retstack

      // for the last entry in the stack, we don't have a pop position
      if(i==pt.RET_STACK_SIZE-1) begin
         assign rets_in[i][31:0] = rets_out[i-1][31:0];
         assign rsenable[i] = rs_push;
      end
      else if(i>0) begin
        assign rets_in[i][31:0] = ( ({32{rs_push}} & rets_out[i-1][31:0]) |
                                    ({32{rs_pop}}  & rets_out[i+1][31:0]) );
         assign rsenable[i] = rs_push | rs_pop;
      end
      rvdffe #(32) rets_ff (.*, .en(rsenable[i]), .din(rets_in[i][31:0]), .dout(rets_out[i][31:0]));

   end : retstack

   // ----------------------------------------------------------------------
   // WRITE
   // ----------------------------------------------------------------------


   assign dec_tlu_error_wb = dec_tlu_br0_start_error_wb | dec_tlu_br0_error_wb;

   assign btb_error_addr_wb[pt.BTB_ADDR_HI:pt.BTB_ADDR_LO] = dec_tlu_br0_addr_wb[pt.BTB_ADDR_HI:pt.BTB_ADDR_LO];

   assign dec_tlu_way_wb = dec_tlu_br0_way_wb;

   assign btb_valid = exu_mp_valid & ~dec_tlu_error_wb;

   assign btb_wr_tag[pt.BTB_BTAG_SIZE-1:0] = exu_mp_btag[pt.BTB_BTAG_SIZE-1:0];

   if(!pt.BTB_FULLYA) begin

      if(pt.BTB_BTAG_FOLD) begin : btbfold
         el2_btb_tag_hash_fold #(.pt(pt)) rdtagf  (.hash(fetch_rd_tag_f[pt.BTB_BTAG_SIZE-1:0]),
                                                    .pc({ifc_fetch_addr_f[pt.BTB_ADDR_HI+pt.BTB_BTAG_SIZE+pt.BTB_BTAG_SIZE:pt.BTB_ADDR_HI+1]}));
         el2_btb_tag_hash_fold #(.pt(pt)) rdtagp1f(.hash(fetch_rd_tag_p1_f[pt.BTB_BTAG_SIZE-1:0]),
                                                    .pc({fetch_addr_p1_f[ pt.BTB_ADDR_HI+pt.BTB_BTAG_SIZE+pt.BTB_BTAG_SIZE:pt.BTB_ADDR_HI+1]}));
      end
      else begin
         el2_btb_tag_hash #(.pt(pt)) rdtagf(.hash(fetch_rd_tag_f[pt.BTB_BTAG_SIZE-1:0]),
                                             .pc({ifc_fetch_addr_f[pt.BTB_ADDR_HI+pt.BTB_BTAG_SIZE+pt.BTB_BTAG_SIZE+pt.BTB_BTAG_SIZE:pt.BTB_ADDR_HI+1]}));
         el2_btb_tag_hash #(.pt(pt)) rdtagp1f(.hash(fetch_rd_tag_p1_f[pt.BTB_BTAG_SIZE-1:0]),
                                               .pc({fetch_addr_p1_f[pt.BTB_ADDR_HI+pt.BTB_BTAG_SIZE+pt.BTB_BTAG_SIZE+pt.BTB_BTAG_SIZE:pt.BTB_ADDR_HI+1]}));
      end

      assign btb_wr_en_way0 = ( ({{~exu_mp_way & exu_mp_valid_write & ~dec_tlu_error_wb}}) |
                                ({{~dec_tlu_way_wb & dec_tlu_error_wb}}));

      assign btb_wr_en_way1 = ( ({{exu_mp_way & exu_mp_valid_write & ~dec_tlu_error_wb}}) |
                                ({{dec_tlu_way_wb & dec_tlu_error_wb}}));
      assign btb_wr_addr[pt.BTB_ADDR_HI:pt.BTB_ADDR_LO] = dec_tlu_error_wb ? btb_error_addr_wb[pt.BTB_ADDR_HI:pt.BTB_ADDR_LO] : exu_mp_addr[pt.BTB_ADDR_HI:pt.BTB_ADDR_LO];


      assign vwayhit_f[1:0] = ( ({2{fetch_start_f[0]}} & {wayhit_f[1:0]}) |
                                ({2{fetch_start_f[1]}} & {wayhit_p1_f[0], wayhit_f[1]})) & {eoc_mask, 1'b1};

   end // if (!pt.BTB_FULLYA)

   assign btb_wr_data[BTB_DWIDTH-1:0] = {btb_wr_tag[pt.BTB_BTAG_SIZE-1:0], exu_mp_tgt[pt.BTB_TOFFSET_SIZE-1:0], exu_mp_pc4, exu_mp_boffset,
                                                exu_mp_call | exu_mp_ja, exu_mp_ret | exu_mp_ja, btb_valid} ;

   assign exu_mp_valid_write = exu_mp_valid & exu_mp_ataken & ~exu_mp_pkt.valid;
   logic [1:0] bht_wr_data0, bht_wr_data2;
   logic [1:0] bht_wr_en0, bht_wr_en2;

   assign middle_of_bank = exu_mp_pc4 ^ exu_mp_boffset;
   assign bht_wr_en0[1:0] = {2{exu_mp_valid & ~exu_mp_call & ~exu_mp_ret & ~exu_mp_ja}} & {middle_of_bank, ~middle_of_bank};
   assign bht_wr_en2[1:0] = {2{dec_tlu_br0_v_wb}} & {dec_tlu_br0_middle_wb, ~dec_tlu_br0_middle_wb} ;

   // Experiments show this is the best priority scheme for same bank/index writes at the same time.
   assign bht_wr_data0[1:0] = exu_mp_hist[1:0]; // lowest priority
   assign bht_wr_data2[1:0] = dec_tlu_br0_hist_wb[1:0]; // highest priority



   logic [pt.BHT_ADDR_HI:pt.BHT_ADDR_LO] bht_rd_addr_f, bht_rd_addr_p1_f, bht_wr_addr0, bht_wr_addr2;

   logic [pt.BHT_ADDR_HI:pt.BHT_ADDR_LO] mp_hashed, br0_hashed_wb, bht_rd_addr_hashed_f, bht_rd_addr_hashed_p1_f;
   el2_btb_ghr_hash #(.pt(pt)) mpghrhs  (.hashin(exu_mp_addr[pt.BTB_ADDR_HI:pt.BTB_ADDR_LO]), .ghr(exu_mp_eghr[pt.BHT_GHR_SIZE-1:0]), .hash(mp_hashed[pt.BHT_ADDR_HI:pt.BHT_ADDR_LO]));
   el2_btb_ghr_hash #(.pt(pt)) br0ghrhs (.hashin(dec_tlu_br0_addr_wb[pt.BTB_ADDR_HI:pt.BTB_ADDR_LO]), .ghr(exu_i0_br_fghr_wb[pt.BHT_GHR_SIZE-1:0]), .hash(br0_hashed_wb[pt.BHT_ADDR_HI:pt.BHT_ADDR_LO]));
   el2_btb_ghr_hash #(.pt(pt)) fghrhs (.hashin(btb_rd_addr_f[pt.BTB_ADDR_HI:pt.BTB_ADDR_LO]), .ghr(fghr[pt.BHT_GHR_SIZE-1:0]), .hash(bht_rd_addr_hashed_f[pt.BHT_ADDR_HI:pt.BHT_ADDR_LO]));
   el2_btb_ghr_hash #(.pt(pt)) fghrhs_p1 (.hashin(btb_rd_addr_p1_f[pt.BTB_ADDR_HI:pt.BTB_ADDR_LO]), .ghr(fghr[pt.BHT_GHR_SIZE-1:0]), .hash(bht_rd_addr_hashed_p1_f[pt.BHT_ADDR_HI:pt.BHT_ADDR_LO]));

   assign bht_wr_addr0[pt.BHT_ADDR_HI:pt.BHT_ADDR_LO] = mp_hashed[pt.BHT_ADDR_HI:pt.BHT_ADDR_LO];
   assign bht_wr_addr2[pt.BHT_ADDR_HI:pt.BHT_ADDR_LO] = br0_hashed_wb[pt.BHT_ADDR_HI:pt.BHT_ADDR_LO];
   assign bht_rd_addr_f[pt.BHT_ADDR_HI:pt.BHT_ADDR_LO] = bht_rd_addr_hashed_f[pt.BHT_ADDR_HI:pt.BHT_ADDR_LO];
   assign bht_rd_addr_p1_f[pt.BHT_ADDR_HI:pt.BHT_ADDR_LO] = bht_rd_addr_hashed_p1_f[pt.BHT_ADDR_HI:pt.BHT_ADDR_LO];


   // ----------------------------------------------------------------------
   // Structures. Using FLOPS
   // ----------------------------------------------------------------------
   // BTB
   // Entry -> tag[pt.BTB_BTAG_SIZE-1:0], toffset[11:0], pc4, boffset, call, ret, valid

   if(!pt.BTB_FULLYA) begin

      for (j=0 ; j<LRU_SIZE ; j++) begin : BTB_FLOPS
         // Way 0
         rvdffe #(17+pt.BTB_BTAG_SIZE) btb_bank0_way0 (.*,
                    .en(((btb_wr_addr[pt.BTB_ADDR_HI:pt.BTB_ADDR_LO] == j) & btb_wr_en_way0)),
                    .din        (btb_wr_data[BTB_DWIDTH-1:0]),
                    .dout       (btb_bank0_rd_data_way0_out[j]));

         // Way 1
         rvdffe #(17+pt.BTB_BTAG_SIZE) btb_bank0_way1 (.*,
                    .en(((btb_wr_addr[pt.BTB_ADDR_HI:pt.BTB_ADDR_LO] == j) & btb_wr_en_way1)),
                    .din        (btb_wr_data[BTB_DWIDTH-1:0]),
                    .dout       (btb_bank0_rd_data_way1_out[j]));

      end


    always_comb begin : BTB_rd_mux
        btb_bank0_rd_data_way0_f[BTB_DWIDTH-1:0] = '0 ;
        btb_bank0_rd_data_way1_f[BTB_DWIDTH-1:0] = '0 ;
        btb_bank0_rd_data_way0_p1_f[BTB_DWIDTH-1:0] = '0 ;
        btb_bank0_rd_data_way1_p1_f[BTB_DWIDTH-1:0] = '0 ;

        for (int j=0; j< LRU_SIZE; j++) begin
          if (btb_rd_addr_f[pt.BTB_ADDR_HI:pt.BTB_ADDR_LO] == (pt.BTB_ADDR_HI-pt.BTB_ADDR_LO+1)'(j)) begin

           btb_bank0_rd_data_way0_f[BTB_DWIDTH-1:0] =  btb_bank0_rd_data_way0_out[j];
           btb_bank0_rd_data_way1_f[BTB_DWIDTH-1:0] =  btb_bank0_rd_data_way1_out[j];

          end
        end
        for (int j=0; j< LRU_SIZE; j++) begin
          if (btb_rd_addr_p1_f[pt.BTB_ADDR_HI:pt.BTB_ADDR_LO] == (pt.BTB_ADDR_HI-pt.BTB_ADDR_LO+1)'(j)) begin

           btb_bank0_rd_data_way0_p1_f[BTB_DWIDTH-1:0] =  btb_bank0_rd_data_way0_out[j];
           btb_bank0_rd_data_way1_p1_f[BTB_DWIDTH-1:0] =  btb_bank0_rd_data_way1_out[j];

          end
        end
    end
end // if (!pt.BTB_FULLYA)





      if(pt.BTB_FULLYA) begin : fa

         logic found1, hit0, hit1;
         logic btb_used_reset, write_used;
         logic [$clog2(pt.BTB_SIZE)-1:0] btb_fa_wr_addr0, hit0_index, hit1_index;

         logic [pt.BTB_SIZE-1:0]         btb_tag_hit, btb_offset_0, btb_offset_1, btb_used_ns, btb_used,
                                         wr0_en, btb_upper_hit;
         logic [pt.BTB_SIZE-1:0][BTB_DWIDTH-1:0] btbdata;

         // Fully Associative tag hash uses bits 31:3. Bits 2:1 are the offset bits used for the 4 tag comp banks
         // Full tag used to speed up lookup. There is one 31:3 cmp per entry, and 4 2:1 cmps per entry.

         logic [FA_CMP_LOWER-1:1]  ifc_fetch_addr_p1_f;


         assign ifc_fetch_addr_p1_f[FA_CMP_LOWER-1:1] = ifc_fetch_addr_f[FA_CMP_LOWER-1:1] + 1'b1;

         assign fetch_mp_collision_f = ( (exu_mp_btag[pt.BTB_BTAG_SIZE-1:0] == ifc_fetch_addr_f[31:1]) &
                                      exu_mp_valid & ifc_fetch_req_f & ~exu_mp_pkt.way);
         assign fetch_mp_collision_p1_f = ( (exu_mp_btag[pt.BTB_BTAG_SIZE-1:0] == {ifc_fetch_addr_f[31:FA_CMP_LOWER], ifc_fetch_addr_p1_f[FA_CMP_LOWER-1:1]}) &
                                      exu_mp_valid & ifc_fetch_req_f & ~exu_mp_pkt.way);

      always_comb begin
         btb_vbank0_rd_data_f = '0;
         btb_vbank1_rd_data_f = '0;
         btb_tag_hit = '0;
         btb_upper_hit = '0;
         btb_offset_0 = '0;
         btb_offset_1 = '0;

         found1 = 1'b0;
         hit0 = 1'b0;
         hit1 = 1'b0;
         hit0_index = '0;
         hit1_index = '0;
         btb_fa_wr_addr0 = '0;

         for(int i=0; i<pt.BTB_SIZE; i++) begin
            // Break the cmp into chunks for lower area.
            // Chunk1: FA 31:6 or 31:5 depending on icache line size
            // Chunk2: FA 5:1 or 4:1 depending on icache line size
            btb_upper_hit[i] = (btbdata[i][BTB_DWIDTH_TOP:FA_TAG_END_UPPER] == ifc_fetch_addr_f[31:FA_CMP_LOWER]) & btbdata[i][0] & ~wr0_en[i];
            btb_offset_0[i] = (btbdata[i][FA_TAG_START_LOWER:FA_TAG_END_LOWER] == ifc_fetch_addr_f[FA_CMP_LOWER-1:1]) & btb_upper_hit[i];
            btb_offset_1[i] = (btbdata[i][FA_TAG_START_LOWER:FA_TAG_END_LOWER] == ifc_fetch_addr_p1_f[FA_CMP_LOWER-1:1]) & btb_upper_hit[i];

            if(~hit0) begin
               if(btb_offset_0[i]) begin
                  hit0_index[BTB_FA_INDEX:0] = (BTB_FA_INDEX+1)'(i);
                  // hit unless we are also writing this entry at the same time
                  hit0 = 1'b1;
               end
            end
            if(~hit1) begin
               if(btb_offset_1[i]) begin
                  hit1_index[BTB_FA_INDEX:0] = (BTB_FA_INDEX+1)'(i);
                  hit1 = 1'b1;
               end
            end


            // Mux out the 2 potential branches
            if(btb_offset_0[i] == 1'b1)
              btb_vbank0_rd_data_f[BTB_DWIDTH-1:0] = fetch_mp_collision_f ? btb_wr_data : btbdata[i];
            if(btb_offset_1[i] == 1'b1)
              btb_vbank1_rd_data_f[BTB_DWIDTH-1:0] = fetch_mp_collision_p1_f ? btb_wr_data : btbdata[i];

            // find the first zero from bit zero in the used vector, this is the write address
            if(~found1) begin
               if(~btb_used[i]) begin
                  btb_fa_wr_addr0[BTB_FA_INDEX:0] = i[BTB_FA_INDEX:0];
                  found1 = 1'b1;
               end
            end
         end
      end // always_comb begin

`ifdef RV_ASSERT_ON
   btbhitonehot0: assert #0 ($onehot0(btb_offset_0));
   btbhitonehot1: assert #0 ($onehot0(btb_offset_1));
`endif

   assign vwayhit_f[1:0] = {hit1, hit0} & {eoc_mask, 1'b1};

   // way bit is reused as the predicted bit
   assign way_raw[1:0] =  vwayhit_f[1:0] | {fetch_mp_collision_p1_f, fetch_mp_collision_f};

   for (j=0 ; j<pt.BTB_SIZE ; j++) begin : BTB_FAFLOPS

      assign wr0_en[j] = ((btb_fa_wr_addr0[BTB_FA_INDEX:0] == j) & (exu_mp_valid_write & ~exu_mp_pkt.way)) |
                         ((dec_fa_error_index == j) & dec_tlu_error_wb);

      rvdffe #(BTB_DWIDTH) btb_fa (.*, .clk(clk),
                                   .en  (wr0_en[j]),
                                   .din (btb_wr_data[BTB_DWIDTH-1:0]),
                                   .dout(btbdata[j]));
   end // block: BTB_FAFLOPS

   assign ifu_bp_fa_index_f[1] = hit1 ? hit1_index : '0;
   assign ifu_bp_fa_index_f[0] = hit0 ? hit0_index : '0;

   assign btb_used_reset = &btb_used[pt.BTB_SIZE-1:0];
   assign btb_used_ns[pt.BTB_SIZE-1:0] = ({pt.BTB_SIZE{vwayhit_f[1]}} & (32'b1 << hit1_index[BTB_FA_INDEX:0])) |
                                         ({pt.BTB_SIZE{vwayhit_f[0]}} & (32'b1 << hit0_index[BTB_FA_INDEX:0])) |
                                         ({pt.BTB_SIZE{exu_mp_valid_write & ~exu_mp_pkt.way & ~dec_tlu_error_wb}} & (32'b1 << btb_fa_wr_addr0[BTB_FA_INDEX:0])) |
                                         ({pt.BTB_SIZE{btb_used_reset}} & {pt.BTB_SIZE{1'b0}}) |
                                         ({pt.BTB_SIZE{~btb_used_reset & dec_tlu_error_wb}} & (btb_used[pt.BTB_SIZE-1:0] & ~(32'b1 << dec_fa_error_index[BTB_FA_INDEX:0]))) |
                                         (~{pt.BTB_SIZE{btb_used_reset | dec_tlu_error_wb}} & btb_used[pt.BTB_SIZE-1:0]);

   assign write_used = btb_used_reset | ifu_bp_hit_taken_f | exu_mp_valid_write | dec_tlu_error_wb;


   rvdffe #(pt.BTB_SIZE) btb_usedf (.*, .clk(clk),
                    .en  (write_used),
                    .din (btb_used_ns[pt.BTB_SIZE-1:0]),
                    .dout(btb_used[pt.BTB_SIZE-1:0]));

end // block: fa


   //-----------------------------------------------------------------------------
   // BHT
   // 2 bit Entry -> direction, strength
   //
   //-----------------------------------------------------------------------------

   logic [1:0] [(pt.BHT_ARRAY_DEPTH/NUM_BHT_LOOP)-1:0][NUM_BHT_LOOP-1:0][1:0]      bht_bank_wr_data ;
   logic [1:0] [pt.BHT_ARRAY_DEPTH-1:0] [1:0]                bht_bank_rd_data_out ;
   logic [1:0] [(pt.BHT_ARRAY_DEPTH/NUM_BHT_LOOP)-1:0]                 bht_bank_clken ;
   logic [1:0] [(pt.BHT_ARRAY_DEPTH/NUM_BHT_LOOP)-1:0]                 bht_bank_clk   ;
   logic [1:0] [(pt.BHT_ARRAY_DEPTH/NUM_BHT_LOOP)-1:0][NUM_BHT_LOOP-1:0]           bht_bank_sel   ;

   for ( i=0; i<2; i++) begin : BANKS
     for (genvar k=0 ; k < (pt.BHT_ARRAY_DEPTH)/NUM_BHT_LOOP ; k++) begin : BHT_CLK_GROUP
     assign bht_bank_clken[i][k]  = (bht_wr_en0[i] & ((bht_wr_addr0[pt.BHT_ADDR_HI: NUM_BHT_LOOP_OUTER_LO]==k) |  BHT_NO_ADDR_MATCH)) |
                                    (bht_wr_en2[i] & ((bht_wr_addr2[pt.BHT_ADDR_HI: NUM_BHT_LOOP_OUTER_LO]==k) |  BHT_NO_ADDR_MATCH));
`ifndef RV_FPGA_OPTIMIZE
     rvclkhdr bht_bank_grp_cgc ( .en(bht_bank_clken[i][k]), .l1clk(bht_bank_clk[i][k]), .* ); // ifndef RV_FPGA_OPTIMIZE
`endif

     for (j=0 ; j<NUM_BHT_LOOP ; j++) begin : BHT_FLOPS
       assign   bht_bank_sel[i][k][j]    = (bht_wr_en0[i] & (bht_wr_addr0[NUM_BHT_LOOP_INNER_HI :pt.BHT_ADDR_LO] == j) & ((bht_wr_addr0[pt.BHT_ADDR_HI: NUM_BHT_LOOP_OUTER_LO]==k) | BHT_NO_ADDR_MATCH)) |
                                           (bht_wr_en2[i] & (bht_wr_addr2[NUM_BHT_LOOP_INNER_HI :pt.BHT_ADDR_LO] == j) & ((bht_wr_addr2[pt.BHT_ADDR_HI: NUM_BHT_LOOP_OUTER_LO]==k) | BHT_NO_ADDR_MATCH)) ;

       assign bht_bank_wr_data[i][k][j]  = (bht_wr_en2[i] & (bht_wr_addr2[NUM_BHT_LOOP_INNER_HI:pt.BHT_ADDR_LO] == j) & ((bht_wr_addr2[pt.BHT_ADDR_HI: NUM_BHT_LOOP_OUTER_LO]==k) | BHT_NO_ADDR_MATCH)) ? bht_wr_data2[1:0] :
                                                                                                                      bht_wr_data0[1:0]   ;


          rvdffs_fpga #(2) bht_bank (.*,
                    .clk        (bht_bank_clk[i][k]),
                    .en         (bht_bank_sel[i][k][j]),
                    .rawclk     (clk),
                    .clken      (bht_bank_sel[i][k][j]),
                    .din        (bht_bank_wr_data[i][k][j]),
                    .dout       (bht_bank_rd_data_out[i][(16*k)+j]));

      end // block: BHT_FLOPS
   end // block: BHT_CLK_GROUP
 end // block: BANKS

    always_comb begin : BHT_rd_mux
     bht_bank0_rd_data_f[1:0] = '0 ;
     bht_bank1_rd_data_f[1:0] = '0 ;
     bht_bank0_rd_data_p1_f[1:0] = '0 ;
     for (int j=0; j< pt.BHT_ARRAY_DEPTH; j++) begin
       if (bht_rd_addr_f[pt.BHT_ADDR_HI:pt.BHT_ADDR_LO] == (pt.BHT_ADDR_HI-pt.BHT_ADDR_LO+1)'(j)) begin
         bht_bank0_rd_data_f[1:0] = bht_bank_rd_data_out[0][j];
         bht_bank1_rd_data_f[1:0] = bht_bank_rd_data_out[1][j];
       end
       if (bht_rd_addr_p1_f[pt.BHT_ADDR_HI:pt.BHT_ADDR_LO] == (pt.BHT_ADDR_HI-pt.BHT_ADDR_LO+1)'(j)) begin
         bht_bank0_rd_data_p1_f[1:0] = bht_bank_rd_data_out[0][j];
       end
      end
    end // block: BHT_rd_mux


function [1:0] countones;
      input [1:0] valid;

      begin

countones[1:0] = {2'b0, valid[1]} +
                 {2'b0, valid[0]};
      end
   endfunction
endmodule // el2_ifu_bp_ctl

