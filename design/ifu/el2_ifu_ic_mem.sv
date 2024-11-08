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
////////////////////////////////////////////////////
//   ICACHE DATA & TAG MODULE WRAPPER              //
/////////////////////////////////////////////////////
`include "el2_ifu_ic_macros.svh"
module el2_ifu_ic_mem
import el2_pkg::*;
 #(
`include "el2_param.vh"
 )
  (
      input logic                                   clk,                // Clock only while core active.  Through one clock header.  For flops with    second clock header built in.  Connected to ACTIVE_L2CLK.
      input logic                                   active_clk,         // Clock only while core active.  Through two clock headers. For flops without second clock header built in.
      input logic                                   rst_l,              // reset, active low
      input logic                                   clk_override,       // Override non-functional clock gating
      input logic                                   dec_tlu_core_ecc_disable,  // Disable ECC checking

      input logic [31:1]                            ic_rw_addr,
      input logic [pt.ICACHE_NUM_WAYS-1:0]          ic_wr_en  ,         // Which way to write
      input logic                                   ic_rd_en  ,         // Read enable
      input logic [pt.ICACHE_INDEX_HI:3]            ic_debug_addr,      // Read/Write addresss to the Icache.
      input logic                                   ic_debug_rd_en,     // Icache debug rd
      input logic                                   ic_debug_wr_en,     // Icache debug wr
      input logic                                   ic_debug_tag_array, // Debug tag array
      input logic [pt.ICACHE_NUM_WAYS-1:0]          ic_debug_way,       // Debug way. Rd or Wr.
      input logic [63:0]                            ic_premux_data,     // Premux data to be muxed with each way of the Icache.
      input logic                                   ic_sel_premux_data, // Select the pre_muxed data

      input  logic [pt.ICACHE_BANKS_WAY-1:0][70:0]  ic_wr_data,         // Data to fill to the Icache. With ECC
      output logic [63:0]                           ic_rd_data ,        // Data read from Icache. 2x64bits + parity bits. F2 stage. With ECC
      output logic [70:0]                           ic_debug_rd_data ,  // Data read from Icache. 2x64bits + parity bits. F2 stage. With ECC
      output logic [25:0]                           ictag_debug_rd_data,// Debug icache tag.
      input logic  [70:0]                           ic_debug_wr_data,   // Debug wr cache.

      output logic [pt.ICACHE_BANKS_WAY-1:0]        ic_eccerr,          // ecc error per bank
      output logic [pt.ICACHE_BANKS_WAY-1:0]        ic_parerr,          // ecc error per bank
      input logic [pt.ICACHE_NUM_WAYS-1:0]          ic_tag_valid,       // Valid from the I$ tag valid outside (in flops).

      el2_mem_if.veer_icache_src icache_export,
      input el2_ic_data_ext_in_pkt_t [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0] ic_data_ext_in_pkt,   // this is being driven by the top level for soc testing/etc
      input el2_ic_tag_ext_in_pkt_t  [pt.ICACHE_NUM_WAYS-1:0]                          ic_tag_ext_in_pkt,    // this is being driven by the top level for soc testing/etc

      output logic [pt.ICACHE_NUM_WAYS-1:0]         ic_rd_hit,          // ic_rd_hit[3:0]
      output logic                                  ic_tag_perr,        // Tag Parity error
      // Excluding scan_mode from coverage as its usage is determined by the integrator of the VeeR core.
      /*verilator coverage_off*/
      input  logic                                  scan_mode           // Flop scan mode control
      /*verilator coverage_on*/
      ) ;




   EL2_IC_TAG #(.pt(pt)) ic_tag_inst
          (
           .*,
           .icache_export(icache_export),
           .ic_wr_en     (ic_wr_en[pt.ICACHE_NUM_WAYS-1:0]),
           .ic_debug_addr(ic_debug_addr[pt.ICACHE_INDEX_HI:3]),
           .ic_rw_addr   (ic_rw_addr[31:3])
           ) ;

   EL2_IC_DATA #(.pt(pt)) ic_data_inst
          (
           .*,
           .icache_export(icache_export),
           .ic_wr_en     (ic_wr_en[pt.ICACHE_NUM_WAYS-1:0]),
           .ic_debug_addr(ic_debug_addr[pt.ICACHE_INDEX_HI:3]),
           .ic_rw_addr   (ic_rw_addr[31:1])
           ) ;

 endmodule


/////////////////////////////////////////////////
////// ICACHE DATA MODULE    ////////////////////
/////////////////////////////////////////////////
module EL2_IC_DATA
import el2_pkg::*;
#(
`include "el2_param.vh"
 )
     (
      input logic clk,
      input logic active_clk,
      input logic rst_l,
      input logic clk_override,

      input logic [31:1]                  ic_rw_addr,
      input logic [pt.ICACHE_NUM_WAYS-1:0]ic_wr_en,
      input logic                          ic_rd_en,           // Read enable

      input  logic [pt.ICACHE_BANKS_WAY-1:0][70:0]    ic_wr_data,         // Data to fill to the Icache. With ECC
      output logic [63:0]                             ic_rd_data ,                                 // Data read from Icache. 2x64bits + parity bits. F2 stage. With ECC
      input  logic [70:0]                             ic_debug_wr_data,   // Debug wr cache.
      output logic [70:0]                             ic_debug_rd_data ,  // Data read from Icache. 2x64bits + parity bits. F2 stage. With ECC
      output logic [pt.ICACHE_BANKS_WAY-1:0] ic_parerr,
      output logic [pt.ICACHE_BANKS_WAY-1:0] ic_eccerr,    // ecc error per bank
      input logic [pt.ICACHE_INDEX_HI:3]     ic_debug_addr,     // Read/Write addresss to the Icache.
      input logic                            ic_debug_rd_en,      // Icache debug rd
      input logic                            ic_debug_wr_en,      // Icache debug wr
      input logic                            ic_debug_tag_array,  // Debug tag array
      input logic [pt.ICACHE_NUM_WAYS-1:0]   ic_debug_way,        // Debug way. Rd or Wr.
      input logic [63:0]                     ic_premux_data,      // Premux data to be muxed with each way of the Icache.
      input logic                            ic_sel_premux_data,  // Select the pre_muxed data

      input logic [pt.ICACHE_NUM_WAYS-1:0]ic_rd_hit,
      el2_mem_if.veer_icache_src             icache_export,
      input el2_ic_data_ext_in_pkt_t  [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0] ic_data_ext_in_pkt,   // this is being driven by the top level for soc testing/etc
      // Excluding scan_mode from coverage as its usage is determined by the integrator of the VeeR core.
      /*verilator coverage_off*/
      input  logic                         scan_mode
      /*verilator coverage_on*/

      ) ;

   logic [pt.ICACHE_TAG_INDEX_LO-1:1]                                             ic_rw_addr_ff;
   logic [pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_NUM_WAYS-1:0]                        ic_b_sb_wren;    //bank x ways
   logic [pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_NUM_WAYS-1:0]                        ic_b_sb_rden;    //bank x ways


   logic [pt.ICACHE_BANKS_WAY-1:0]                                                ic_b_rden;       //bank
   logic [pt.ICACHE_BANKS_WAY-1:0]                                                ic_b_rden_ff;    //bank
   logic [pt.ICACHE_BANKS_WAY-1:0]                                                ic_debug_sel_sb;

   logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0][70:0]                  wb_dout ;       //  ways x bank
   logic [pt.ICACHE_BANKS_WAY-1:0][70:0]                                          ic_sb_wr_data, ic_bank_wr_data, wb_dout_ecc_bank;
   logic [pt.ICACHE_NUM_WAYS-1:0] [141:0]                                         wb_dout_way_pre;
   logic [pt.ICACHE_NUM_WAYS-1:0] [63:0]                                          wb_dout_way, wb_dout_way_with_premux;
   logic [141:0]                                                                  wb_dout_ecc;

   logic [pt.ICACHE_BANKS_WAY-1:0]                                                bank_check_en;

   logic [pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_NUM_WAYS-1:0]                        ic_bank_way_clken;
   logic [pt.ICACHE_BANKS_WAY-1:0]                                                ic_bank_way_clken_final;
   logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0]                        ic_bank_way_clken_final_up;

   logic [pt.ICACHE_NUM_WAYS-1:0]                                                 ic_debug_rd_way_en;    // debug wr_way
   logic [pt.ICACHE_NUM_WAYS-1:0]                                                 ic_debug_rd_way_en_ff; // debug wr_way
   logic [pt.ICACHE_NUM_WAYS-1:0]                                                 ic_debug_wr_way_en;    // debug wr_way
   logic [pt.ICACHE_INDEX_HI:1]                                                   ic_rw_addr_q;

   logic [pt.ICACHE_BANKS_WAY-1:0]       [pt.ICACHE_INDEX_HI : pt.ICACHE_DATA_INDEX_LO] ic_rw_addr_bank_q;

   logic [pt.ICACHE_TAG_LO-1 : pt.ICACHE_DATA_INDEX_LO]                           ic_rw_addr_q_inc;
   logic [pt.ICACHE_NUM_WAYS-1:0]                                                 ic_rd_hit_q;



      logic [pt.ICACHE_BANKS_WAY-1:0]                                                ic_b_sram_en;
      logic [pt.ICACHE_BANKS_WAY-1:0]                                                ic_b_read_en;
      logic [pt.ICACHE_BANKS_WAY-1:0]                                                ic_b_write_en;
      logic [pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_NUM_BYPASS-1:0] [31 : pt.ICACHE_DATA_INDEX_LO]  wb_index_hold;
      logic [pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_NUM_BYPASS-1:0]                                 write_bypass_en;     //bank
      logic [pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_NUM_BYPASS-1:0]                                 write_bypass_en_ff;  //bank
      logic [pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_NUM_BYPASS-1:0]                                 index_valid;  //bank
      logic [pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_NUM_BYPASS-1:0]                                 ic_b_clear_en;
      logic [pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_NUM_BYPASS-1:0]                                 ic_b_addr_match;
      logic [pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_NUM_BYPASS-1:0]                                 ic_b_addr_match_index_only;

      logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0]                                                ic_b_sram_en_up;
      logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0]                                                ic_b_read_en_up;
      logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0]                                                ic_b_write_en_up;
      logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_NUM_BYPASS-1:0] [31 : pt.ICACHE_DATA_INDEX_LO]  wb_index_hold_up;
      logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_NUM_BYPASS-1:0]                                 write_bypass_en_up;     //bank
      logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_NUM_BYPASS-1:0]                                 write_bypass_en_ff_up;  //bank
      logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_NUM_BYPASS-1:0]                                 index_valid_up;  //bank
      logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_NUM_BYPASS-1:0]                                 ic_b_clear_en_up;
      logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_NUM_BYPASS-1:0]                                 ic_b_addr_match_up;
      logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_NUM_BYPASS-1:0]                                 ic_b_addr_match_index_only_up;


   logic [pt.ICACHE_BANKS_WAY-1:0]                 [31 : pt.ICACHE_DATA_INDEX_LO] ic_b_rw_addr;
   logic [pt.ICACHE_BANKS_WAY-1:0]                 [31 : pt.ICACHE_DATA_INDEX_LO] ic_b_rw_addr_index_only;

   logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0]                 [31 : pt.ICACHE_DATA_INDEX_LO] ic_b_rw_addr_up;
   logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0]                 [31 : pt.ICACHE_DATA_INDEX_LO] ic_b_rw_addr_index_only_up;



   logic                                                                          ic_rd_en_with_debug;
   logic                                                                          ic_rw_addr_wrap, ic_cacheline_wrap_ff;
   logic                                                                          ic_debug_rd_en_ff;

   // Use exported ICache interface. Some signals are assigned here, some in the blocks below.
   always_comb begin
      icache_export.ic_b_sb_wren = ic_b_sb_wren;
      icache_export.ic_sb_wr_data = ic_sb_wr_data;
      icache_export.ic_rw_addr_bank_q = ic_rw_addr_bank_q;
      icache_export.ic_bank_way_clken_final =ic_bank_way_clken_final_up;
      icache_export.ic_bank_way_clken_final_up =ic_bank_way_clken_final_up;
   end


//-----------------------------------------------------------
// ----------- Logic section starts here --------------------
//-----------------------------------------------------------
   assign  ic_debug_rd_way_en[pt.ICACHE_NUM_WAYS-1:0] =  {pt.ICACHE_NUM_WAYS{ic_debug_rd_en & ~ic_debug_tag_array}} & ic_debug_way[pt.ICACHE_NUM_WAYS-1:0] ;
   assign  ic_debug_wr_way_en[pt.ICACHE_NUM_WAYS-1:0] =  {pt.ICACHE_NUM_WAYS{ic_debug_wr_en & ~ic_debug_tag_array}} & ic_debug_way[pt.ICACHE_NUM_WAYS-1:0] ;

   logic end_of_cache_line;
   assign end_of_cache_line = (pt.ICACHE_LN_SZ==7'h40) ? (&ic_rw_addr_q[5:4]) : ic_rw_addr_q[4];
   always_comb begin : clkens
      ic_bank_way_clken  = '0;

      for ( int i=0; i<pt.ICACHE_BANKS_WAY; i++) begin: wr_ens
       ic_b_sb_wren[i]        =  ic_wr_en[pt.ICACHE_NUM_WAYS-1:0]  |
                                       (ic_debug_wr_way_en[pt.ICACHE_NUM_WAYS-1:0] & {pt.ICACHE_NUM_WAYS{ic_debug_addr[pt.ICACHE_BANK_HI : pt.ICACHE_BANK_LO] == i}}) ;
       ic_debug_sel_sb[i]     = (ic_debug_addr[pt.ICACHE_BANK_HI : pt.ICACHE_BANK_LO] == i );
       ic_sb_wr_data[i]       = (ic_debug_sel_sb[i] & ic_debug_wr_en) ? ic_debug_wr_data : ic_bank_wr_data[i] ;
       ic_b_rden[i]           =  ic_rd_en_with_debug & ( ( ~ic_rw_addr_q[pt.ICACHE_BANK_HI] & (i==0)) |
                                                        (( ic_rw_addr_q[pt.ICACHE_BANK_HI] & ic_rw_addr_q[2:1] == 2'b11) & (i==0) & ~end_of_cache_line) |
                                                         (  ic_rw_addr_q[pt.ICACHE_BANK_HI] & (i==1)) |
                                                         ((~ic_rw_addr_q[pt.ICACHE_BANK_HI] & ic_rw_addr_q[2:1] == 2'b11) & (i==1)) ) ;



       ic_b_sb_rden[i]        =  {pt.ICACHE_NUM_WAYS{ic_b_rden[i]}}   ;

       for ( int j=0; j<pt.ICACHE_NUM_WAYS; j++) begin: way_clkens
         ic_bank_way_clken[i][j] |= ic_b_sb_rden[i][j] | clk_override | ic_b_sb_wren[i][j];
       end
     end // block: wr_ens
   end // block: clkens

// bank read enables
  assign ic_rd_en_with_debug                          = (ic_rd_en   | ic_debug_rd_en ) & ~(|ic_wr_en);
  assign ic_rw_addr_q[pt.ICACHE_INDEX_HI:1] = (ic_debug_rd_en | ic_debug_wr_en) ?
                                              {ic_debug_addr[pt.ICACHE_INDEX_HI:3],2'b0} :
                                              ic_rw_addr[pt.ICACHE_INDEX_HI:1] ;

   assign ic_rw_addr_q_inc[pt.ICACHE_TAG_LO-1:pt.ICACHE_DATA_INDEX_LO] = ic_rw_addr_q[pt.ICACHE_TAG_LO-1 : pt.ICACHE_DATA_INDEX_LO] + 1 ;
   assign ic_rw_addr_wrap                                        = ic_rw_addr_q[pt.ICACHE_BANK_HI] & (ic_rw_addr_q[2:1] == 2'b11) & ic_rd_en_with_debug & ~(|ic_wr_en[pt.ICACHE_NUM_WAYS-1:0]);
   assign ic_cacheline_wrap_ff                                   = ic_rw_addr_ff[pt.ICACHE_TAG_INDEX_LO-1:pt.ICACHE_BANK_LO] == {(pt.ICACHE_TAG_INDEX_LO - pt.ICACHE_BANK_LO){1'b1}};


   assign ic_rw_addr_bank_q[0] = ~ic_rw_addr_wrap ? ic_rw_addr_q[pt.ICACHE_INDEX_HI:pt.ICACHE_DATA_INDEX_LO] : {ic_rw_addr_q[pt.ICACHE_INDEX_HI: pt.ICACHE_TAG_INDEX_LO] , ic_rw_addr_q_inc[pt.ICACHE_TAG_INDEX_LO-1: pt.ICACHE_DATA_INDEX_LO] } ;
   assign ic_rw_addr_bank_q[1] = ic_rw_addr_q[pt.ICACHE_INDEX_HI:pt.ICACHE_DATA_INDEX_LO];


   rvdffie #(.WIDTH(int'(pt.ICACHE_TAG_INDEX_LO+pt.ICACHE_BANKS_WAY+pt.ICACHE_NUM_WAYS)),.OVERRIDE(1)) miscff
            (.*,
             .din({ ic_b_rden[pt.ICACHE_BANKS_WAY-1:0],   ic_rw_addr_q[pt.ICACHE_TAG_INDEX_LO-1:1], ic_debug_rd_way_en[pt.ICACHE_NUM_WAYS-1:0],   ic_debug_rd_en}),
             .dout({ic_b_rden_ff[pt.ICACHE_BANKS_WAY-1:0],ic_rw_addr_ff[pt.ICACHE_TAG_INDEX_LO-1:1],ic_debug_rd_way_en_ff[pt.ICACHE_NUM_WAYS-1:0],ic_debug_rd_en_ff})
             );

 if (pt.ICACHE_WAYPACK == 0 ) begin : PACKED_0


    logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_NUM_BYPASS_WIDTH-1:0] wrptr_up;
    logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_NUM_BYPASS_WIDTH-1:0] wrptr_in_up;
    logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_NUM_BYPASS-1:0]       sel_bypass_up;
    logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_NUM_BYPASS-1:0]       sel_bypass_ff_up;
    logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0][(71*pt.ICACHE_NUM_WAYS)-1:0]    sel_bypass_data_up;
    logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0]                                 any_bypass_up;
    logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0]                                 any_addr_match_up;

   for (genvar i=0; i<pt.ICACHE_NUM_WAYS; i++) begin: WAYS
      for (genvar k=0; k<pt.ICACHE_BANKS_WAY; k++) begin: BANKS_WAY   // 16B subbank
      if (pt.ICACHE_ECC) begin : ECC1
        logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0] [71-1:0]        wb_dout_pre_up;           // data and its bit enables
        logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0] [pt.ICACHE_NUM_BYPASS-1:0] [71-1:0]  wb_dout_hold_up;

        // Use exported ICache interface.
        always_comb begin
           wb_dout_pre_up = icache_export.wb_dout_pre_up;
        end

        if ($clog2(pt.ICACHE_DATA_DEPTH) == 13 )   begin : size_8192
           `EL2_IC_DATA_SRAM_LOGIC(8192,71)
        end
        else if ($clog2(pt.ICACHE_DATA_DEPTH) == 12 )   begin : size_4096
           `EL2_IC_DATA_SRAM_LOGIC(4096,71)
        end
        else if ($clog2(pt.ICACHE_DATA_DEPTH) == 11 ) begin : size_2048
           `EL2_IC_DATA_SRAM_LOGIC(2048,71)
        end
        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 10 ) begin : size_1024
           `EL2_IC_DATA_SRAM_LOGIC(1024,71)
        end
        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 9 ) begin : size_512
           `EL2_IC_DATA_SRAM_LOGIC(512,71)
        end
         else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 8 ) begin : size_256
           `EL2_IC_DATA_SRAM_LOGIC(256,71)
         end
         else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 7 ) begin : size_128
           `EL2_IC_DATA_SRAM_LOGIC(128,71)
         end
         else  begin : size_64
           `EL2_IC_DATA_SRAM_LOGIC(64,71)
         end
      end // if (pt.ICACHE_ECC)

     else  begin  : ECC0
        logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0] [68-1:0]        wb_dout_pre_up;           // data and its bit enables
        logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0] [pt.ICACHE_NUM_BYPASS-1:0] [68-1:0]  wb_dout_hold_up;

        // Use exported ICache interface.
        always_comb begin
           wb_dout_pre_up = icache_export.wb_dout_pre_up;
        end

        if ($clog2(pt.ICACHE_DATA_DEPTH) == 13 )   begin : size_8192
           `EL2_IC_DATA_SRAM_LOGIC(8192,68)
        end
        else if ($clog2(pt.ICACHE_DATA_DEPTH) == 12 )   begin : size_4096
           `EL2_IC_DATA_SRAM_LOGIC(4096,68)
        end
        else if ($clog2(pt.ICACHE_DATA_DEPTH) == 11 ) begin : size_2048
           `EL2_IC_DATA_SRAM_LOGIC(2048,68)
        end
        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 10 ) begin : size_1024
           `EL2_IC_DATA_SRAM_LOGIC(1024,68)
        end
        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 9 ) begin : size_512
           `EL2_IC_DATA_SRAM_LOGIC(512,68)
        end
         else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 8 ) begin : size_256
           `EL2_IC_DATA_SRAM_LOGIC(256,68)
         end
         else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 7 ) begin : size_128
           `EL2_IC_DATA_SRAM_LOGIC(128,68)
         end
         else  begin : size_64
           `EL2_IC_DATA_SRAM_LOGIC(64,68)
         end
      end // else: !if(pt.ICACHE_ECC)
      end // block: BANKS_WAY
   end // block: WAYS

 end // block: PACKED_0

 // WAY PACKED
 else begin : PACKED_1

    logic [pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_NUM_BYPASS_WIDTH-1:0] wrptr;
    logic [pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_NUM_BYPASS_WIDTH-1:0] wrptr_in;
    logic [pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_NUM_BYPASS-1:0]                       sel_bypass;
    logic [pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_NUM_BYPASS-1:0]                       sel_bypass_ff;


    logic [pt.ICACHE_BANKS_WAY-1:0][(71*pt.ICACHE_NUM_WAYS)-1:0]  sel_bypass_data;
    logic [pt.ICACHE_BANKS_WAY-1:0]                               any_bypass;
    logic [pt.ICACHE_BANKS_WAY-1:0]                               any_addr_match;

 // generate IC DATA PACKED SRAMS for 2/4 ways
  for (genvar k=0; k<pt.ICACHE_BANKS_WAY; k++) begin: BANKS_WAY   // 16B subbank
     if (pt.ICACHE_ECC) begin : ECC1
        logic [pt.ICACHE_BANKS_WAY-1:0] [(71*pt.ICACHE_NUM_WAYS)-1:0]        wb_packeddout, ic_b_sb_bit_en_vec, wb_packeddout_pre;           // data and its bit enables

        logic [pt.ICACHE_BANKS_WAY-1:0] [pt.ICACHE_NUM_BYPASS-1:0] [(71*pt.ICACHE_NUM_WAYS)-1:0]  wb_packeddout_hold;

        // Use exported ICache interface.
        always_comb begin
           icache_export.ic_b_sb_bit_en_vec = ic_b_sb_bit_en_vec;
           wb_packeddout_pre = icache_export.wb_packeddout_pre;
        end

        for (genvar i=0; i<pt.ICACHE_NUM_WAYS; i++) begin: BITEN
           assign ic_b_sb_bit_en_vec[k][(71*i)+70:71*i] = {71{ic_b_sb_wren[k][i]}};
        end

        // SRAMS with ECC (single/double detect; no correct)
        if ($clog2(pt.ICACHE_DATA_DEPTH) == 13 )   begin : size_8192
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM_LOGIC(8192,284,71)    // 64b data + 7b ecc
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM_LOGIC(8192,142,71)
           end // block: WAYS
        end // block: size_8192

        else if ($clog2(pt.ICACHE_DATA_DEPTH) == 12 )   begin : size_4096
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM_LOGIC(4096,284,71)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM_LOGIC(4096,142,71)
           end // block: WAYS
        end // block: size_4096

        else if ($clog2(pt.ICACHE_DATA_DEPTH) == 11 ) begin : size_2048
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM_LOGIC(2048,284,71)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM_LOGIC(2048,142,71)
           end // block: WAYS
        end // block: size_2048

        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 10 ) begin : size_1024
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM_LOGIC(1024,284,71)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM_LOGIC(1024,142,71)
           end // block: WAYS
        end // block: size_1024

        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 9 ) begin : size_512
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM_LOGIC(512,284,71)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM_LOGIC(512,142,71)
           end // block: WAYS
        end // block: size_512

        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 8 ) begin : size_256
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM_LOGIC(256,284,71)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM_LOGIC(256,142,71)
           end // block: WAYS
        end // block: size_256

        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 7 ) begin : size_128
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM_LOGIC(128,284,71)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM_LOGIC(128,142,71)
           end // block: WAYS
        end // block: size_128

        else  begin : size_64
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM_LOGIC(64,284,71)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM_LOGIC(64,142,71)
           end // block: WAYS
        end // block: size_64


       for (genvar i=0; i<pt.ICACHE_NUM_WAYS; i++) begin: WAYS
          assign wb_dout[i][k][70:0]  = wb_packeddout[k][(71*i)+70:71*i];
       end : WAYS

       end // if (pt.ICACHE_ECC)


     else  begin  : ECC0
        logic [pt.ICACHE_BANKS_WAY-1:0] [(68*pt.ICACHE_NUM_WAYS)-1:0]        wb_packeddout, ic_b_sb_bit_en_vec, wb_packeddout_pre;           // data and its bit enables

        logic [pt.ICACHE_BANKS_WAY-1:0] [pt.ICACHE_NUM_BYPASS-1:0] [(68*pt.ICACHE_NUM_WAYS)-1:0]  wb_packeddout_hold;

        // Use exported ICache interface.
        always_comb begin
           icache_export.ic_b_sb_bit_en_vec = ic_b_sb_bit_en_vec;
           wb_packeddout_pre = icache_export.wb_packeddout_pre;
        end

        for (genvar i=0; i<pt.ICACHE_NUM_WAYS; i++) begin: BITEN
           assign ic_b_sb_bit_en_vec[k][(68*i)+67:68*i] = {68{ic_b_sb_wren[k][i]}};
        end

        // SRAMs with parity
        if ($clog2(pt.ICACHE_DATA_DEPTH) == 13 )   begin : size_8192
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM_LOGIC(8192,272,68)    // 64b data + 4b parity
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM_LOGIC(8192,136,68)
           end // block: WAYS
        end // block: size_8192

        else if ($clog2(pt.ICACHE_DATA_DEPTH) == 12 )   begin : size_4096
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM_LOGIC(4096,272,68)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM_LOGIC(4096,136,68)
           end // block: WAYS
        end // block: size_4096

        else if ($clog2(pt.ICACHE_DATA_DEPTH) == 11 ) begin : size_2048
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM_LOGIC(2048,272,68)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM_LOGIC(2048,136,68)
           end // block: WAYS
        end // block: size_2048

        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 10 ) begin : size_1024
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM_LOGIC(1024,272,68)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM_LOGIC(1024,136,68)
           end // block: WAYS
        end // block: size_1024

        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 9 ) begin : size_512
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM_LOGIC(512,272,68)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM_LOGIC(512,136,68)
           end // block: WAYS
        end // block: size_512

        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 8 ) begin : size_256
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM_LOGIC(256,272,68)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM_LOGIC(256,136,68)
           end // block: WAYS
        end // block: size_256

        else if ( $clog2(pt.ICACHE_DATA_DEPTH) == 7 ) begin : size_128
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM_LOGIC(128,272,68)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM_LOGIC(128,136,68)
           end // block: WAYS
        end // block: size_128

        else  begin : size_64
           if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM_LOGIC(64,272,68)
           end // block: WAYS
           else   begin : WAYS
              `EL2_PACKED_IC_DATA_SRAM_LOGIC(64,136,68)
           end // block: WAYS
        end // block: size_64

       for (genvar i=0; i<pt.ICACHE_NUM_WAYS; i++) begin: WAYS
          assign wb_dout[i][k][67:0]  = wb_packeddout[k][(68*i)+67:68*i];
       end
     end // block: ECC0
     end // block: BANKS_WAY
 end // block: PACKED_1


   assign ic_rd_hit_q[pt.ICACHE_NUM_WAYS-1:0] = ic_debug_rd_en_ff ? ic_debug_rd_way_en_ff[pt.ICACHE_NUM_WAYS-1:0] : ic_rd_hit[pt.ICACHE_NUM_WAYS-1:0] ;


 if ( pt.ICACHE_ECC ) begin : ECC1_MUX

   assign ic_bank_wr_data[1] = ic_wr_data[1][70:0];
   assign ic_bank_wr_data[0] = ic_wr_data[0][70:0];

    always_comb begin : rd_mux
      wb_dout_way_pre[pt.ICACHE_NUM_WAYS-1:0] = '0;

      for ( int i=0; i<pt.ICACHE_NUM_WAYS; i++) begin : num_ways
        for ( int j=0; j<pt.ICACHE_BANKS_WAY; j++) begin : banks
         wb_dout_way_pre[i][70:0]      |=  ({71{(ic_rw_addr_ff[pt.ICACHE_BANK_HI : pt.ICACHE_BANK_LO] == (pt.ICACHE_BANK_BITS)'(j))}}   &  wb_dout[i][j]);
         wb_dout_way_pre[i][141 : 71]  |=  ({71{(ic_rw_addr_ff[pt.ICACHE_BANK_HI : pt.ICACHE_BANK_LO] == (pt.ICACHE_BANK_BITS)'(j-1))}} &  wb_dout[i][j]);
        end
      end
    end

    for ( genvar i=0; i<pt.ICACHE_NUM_WAYS; i++) begin : num_ways_mux1
      assign wb_dout_way[i][63:0] = (ic_rw_addr_ff[2:1] == 2'b00) ? wb_dout_way_pre[i][63:0]   :
                                    (ic_rw_addr_ff[2:1] == 2'b01) ?{wb_dout_way_pre[i][86:71], wb_dout_way_pre[i][63:16]} :
                                    (ic_rw_addr_ff[2:1] == 2'b10) ?{wb_dout_way_pre[i][102:71],wb_dout_way_pre[i][63:32]} :
                                                                   {wb_dout_way_pre[i][119:71],wb_dout_way_pre[i][63:48]};

      assign wb_dout_way_with_premux[i][63:0]  =  ic_sel_premux_data ? ic_premux_data[63:0] : wb_dout_way[i][63:0] ;
   end

   always_comb begin : rd_out
      ic_debug_rd_data[70:0]     = '0;
      ic_rd_data[63:0]           = '0;
      wb_dout_ecc[141:0]         = '0;
      for ( int i=0; i<pt.ICACHE_NUM_WAYS; i++) begin : num_ways_mux2
         ic_rd_data[63:0]       |= ({64{ic_rd_hit_q[i] | ic_sel_premux_data}}) &  wb_dout_way_with_premux[i][63:0];
         ic_debug_rd_data[70:0] |= ({71{ic_rd_hit_q[i]}}) & wb_dout_way_pre[i][70:0];
         wb_dout_ecc[141:0]     |= {142{ic_rd_hit_q[i]}}  & wb_dout_way_pre[i];
      end
   end


 for (genvar i=0; i < pt.ICACHE_BANKS_WAY ; i++) begin : ic_ecc_error
    assign bank_check_en[i]    = |ic_rd_hit[pt.ICACHE_NUM_WAYS-1:0] & ((i==0) | (~ic_cacheline_wrap_ff & (ic_b_rden_ff[pt.ICACHE_BANKS_WAY-1:0] == {pt.ICACHE_BANKS_WAY{1'b1}})));  // always check the lower address bank, and drop the upper address bank on a CL wrap
    assign wb_dout_ecc_bank[i] = wb_dout_ecc[(71*i)+70:(71*i)];

   rvecc_decode_64  ecc_decode_64 (
                           .en               (bank_check_en[i]),
                           .din              (wb_dout_ecc_bank[i][63 : 0]),                // [134:71],  [63:0]
                           .ecc_in           (wb_dout_ecc_bank[i][70 : 64]),               // [141:135] [70:64]
                           .ecc_error        (ic_eccerr[i]));

   // or the sb and db error detects into 1 signal called aligndataperr[i] where i corresponds to 2B position
  assign  ic_parerr[i]  = '0 ;
  end // block: ic_ecc_error

end // if ( pt.ICACHE_ECC )

else  begin : ECC0_MUX
   assign ic_bank_wr_data[1] = ic_wr_data[1][70:0];
   assign ic_bank_wr_data[0] = ic_wr_data[0][70:0];

   always_comb begin : rd_mux
      wb_dout_way_pre[pt.ICACHE_NUM_WAYS-1:0] = '0;

   for ( int i=0; i<pt.ICACHE_NUM_WAYS; i++) begin : num_ways
     for ( int j=0; j<pt.ICACHE_BANKS_WAY; j++) begin : banks
         wb_dout_way_pre[i][67:0]         |=  ({68{(ic_rw_addr_ff[pt.ICACHE_BANK_HI : pt.ICACHE_BANK_LO] == (pt.ICACHE_BANK_BITS)'(j))}}   &  wb_dout[i][j][67:0]);
         wb_dout_way_pre[i][135 : 68]     |=  ({68{(ic_rw_addr_ff[pt.ICACHE_BANK_HI : pt.ICACHE_BANK_LO] == (pt.ICACHE_BANK_BITS)'(j-1))}} &  wb_dout[i][j][67:0]);
      end
     end
   end
   // When we straddle the banks like this - the ECC we capture is not correct ??
   for ( genvar i=0; i<pt.ICACHE_NUM_WAYS; i++) begin : num_ways_mux1
      assign wb_dout_way[i][63:0] = (ic_rw_addr_ff[2:1] == 2'b00) ? wb_dout_way_pre[i][63:0]   :
                                    (ic_rw_addr_ff[2:1] == 2'b01) ?{wb_dout_way_pre[i][83:68],  wb_dout_way_pre[i][63:16]} :
                                    (ic_rw_addr_ff[2:1] == 2'b10) ?{wb_dout_way_pre[i][99:68],  wb_dout_way_pre[i][63:32]} :
                                                                   {wb_dout_way_pre[i][115:68], wb_dout_way_pre[i][63:48]};

      assign wb_dout_way_with_premux[i][63:0]      =  ic_sel_premux_data ? ic_premux_data[63:0]  : wb_dout_way[i][63:0] ;
   end

   always_comb begin : rd_out
      ic_rd_data[63:0]   = '0;
      ic_debug_rd_data[70:0]   = '0;
      wb_dout_ecc[135:0] = '0;

      for ( int i=0; i<pt.ICACHE_NUM_WAYS; i++) begin : num_ways_mux2
         ic_rd_data[63:0]   |= ({64{ic_rd_hit_q[i] | ic_sel_premux_data}} &  wb_dout_way_with_premux[i][63:0]);
         ic_debug_rd_data[70:0] |= ({71{ic_rd_hit_q[i]}}) & {3'b0,wb_dout_way_pre[i][67:0]};
         wb_dout_ecc[135:0] |= {136{ic_rd_hit_q[i]}}  & wb_dout_way_pre[i][135:0];
      end
   end

   assign wb_dout_ecc_bank[0] =  wb_dout_ecc[67:0];
   assign wb_dout_ecc_bank[1] =  wb_dout_ecc[135:68];

   logic [pt.ICACHE_BANKS_WAY-1:0][3:0] ic_parerr_bank;

  for (genvar i=0; i < pt.ICACHE_BANKS_WAY ; i++) begin : ic_par_error
    assign bank_check_en[i]    = |ic_rd_hit[pt.ICACHE_NUM_WAYS-1:0] & ((i==0) | (~ic_cacheline_wrap_ff & (ic_b_rden_ff[pt.ICACHE_BANKS_WAY-1:0] == {pt.ICACHE_BANKS_WAY{1'b1}})));  // always check the lower address bank, and drop the upper address bank on a CL wrap
     for (genvar j=0; j<4; j++)  begin : parity
      rveven_paritycheck pchk (
                           .data_in   (wb_dout_ecc_bank[i][16*(j+1)-1: 16*j]),
                           .parity_in (wb_dout_ecc_bank[i][64+j]),
                           .parity_err(ic_parerr_bank[i][j] )
                           );
        end
     assign ic_eccerr [i] = '0 ;
  end

     assign ic_parerr[1] = (|ic_parerr_bank[1][3:0]) & bank_check_en[1];
     assign ic_parerr[0] = (|ic_parerr_bank[0][3:0]) & bank_check_en[0];

end // else: !if( pt.ICACHE_ECC )


endmodule // EL2_IC_DATA

//=============================================================================================================================================================
///\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\ END OF IC DATA MODULE \/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/\/
//\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
//=============================================================================================================================================================

/////////////////////////////////////////////////
////// ICACHE TAG MODULE     ////////////////////
/////////////////////////////////////////////////
module EL2_IC_TAG
import el2_pkg::*;
 #(
`include "el2_param.vh"
 )
     (
      input logic                                                   clk,
      input logic                                                   active_clk,
      input logic                                                   rst_l,
      input logic                                                   clk_override,
      input logic                                                   dec_tlu_core_ecc_disable,

      input logic [31:3]                                            ic_rw_addr,

      input logic [pt.ICACHE_NUM_WAYS-1:0]                         ic_wr_en,             // way
      input logic [pt.ICACHE_NUM_WAYS-1:0]                         ic_tag_valid,
      input logic                                                  ic_rd_en,

      input logic [pt.ICACHE_INDEX_HI:3]                           ic_debug_addr,        // Read/Write addresss to the Icache.
      input logic                                                  ic_debug_rd_en,       // Icache debug rd
      input logic                                                  ic_debug_wr_en,       // Icache debug wr
      input logic                                                  ic_debug_tag_array,   // Debug tag array
      input logic [pt.ICACHE_NUM_WAYS-1:0]                         ic_debug_way,         // Debug way. Rd or Wr.

      el2_mem_if.veer_icache_src                                   icache_export,
      input el2_ic_tag_ext_in_pkt_t   [pt.ICACHE_NUM_WAYS-1:0]    ic_tag_ext_in_pkt,

      output logic [25:0]                                          ictag_debug_rd_data,
      input  logic [70:0]                                          ic_debug_wr_data,     // Debug wr cache.

      output logic [pt.ICACHE_NUM_WAYS-1:0]                        ic_rd_hit,
      output logic                                                 ic_tag_perr,
      // Excluding scan_mode from coverage as its usage is determined by the integrator of the VeeR core.
      /*verilator coverage_off*/
      input  logic                                                 scan_mode
      /*verilator coverage_on*/
   ) ;

   logic [pt.ICACHE_NUM_WAYS-1:0] [25:0]                           ic_tag_data_raw;
   logic [pt.ICACHE_NUM_WAYS-1:0] [25:0]                           ic_tag_data_raw_pre;
   logic [pt.ICACHE_NUM_WAYS-1:0] [36:pt.ICACHE_TAG_LO]            w_tout;
   logic [25:0]                                                    ic_tag_wr_data ;
   logic [pt.ICACHE_NUM_WAYS-1:0] [31:0]                           ic_tag_corrected_data_unc;
   logic [pt.ICACHE_NUM_WAYS-1:0] [06:0]                           ic_tag_corrected_ecc_unc;
   logic [pt.ICACHE_NUM_WAYS-1:0]                                  ic_tag_single_ecc_error;
   logic [pt.ICACHE_NUM_WAYS-1:0]                                  ic_tag_double_ecc_error;
   logic [6:0]                                                     ic_tag_ecc;

   logic [pt.ICACHE_NUM_WAYS-1:0]                                  ic_tag_way_perr ;
   logic [pt.ICACHE_NUM_WAYS-1:0]                                  ic_debug_rd_way_en ;
   logic [pt.ICACHE_NUM_WAYS-1:0]                                  ic_debug_rd_way_en_ff ;

   logic [pt.ICACHE_INDEX_HI: pt.ICACHE_TAG_INDEX_LO]              ic_rw_addr_q;
   logic [31:pt.ICACHE_TAG_LO]                                     ic_rw_addr_ff;
   logic [pt.ICACHE_NUM_WAYS-1:0]                                  ic_tag_rden_q;          // way
   logic [pt.ICACHE_NUM_WAYS-1:0]                                  ic_tag_wren;          // way
   logic [pt.ICACHE_NUM_WAYS-1:0]                                  ic_tag_wren_q;        // way
   logic [pt.ICACHE_NUM_WAYS-1:0]                                  ic_tag_clken;
   logic [pt.ICACHE_NUM_WAYS-1:0]                                  ic_debug_wr_way_en;   // debug wr_way
   logic                                                           ic_rd_en_ff;
   logic                                                           ic_tag_parity;

   // Use exported ICache interface. Some signals are assigned here, some in the blocks below.
   always_comb begin
      icache_export.ic_tag_wren_q = ic_tag_wren_q;
      icache_export.ic_tag_wr_data = ic_tag_wr_data;
      icache_export.ic_rw_addr_q = ic_rw_addr_q;
      ic_tag_data_raw_pre = icache_export.ic_tag_data_raw_pre;
   end

   assign  ic_tag_wren [pt.ICACHE_NUM_WAYS-1:0]  = ic_wr_en[pt.ICACHE_NUM_WAYS-1:0] & {pt.ICACHE_NUM_WAYS{(ic_rw_addr[pt.ICACHE_BEAT_ADDR_HI:4] == {pt.ICACHE_BEAT_BITS-1{1'b1}})}} ;
   assign  ic_tag_clken[pt.ICACHE_NUM_WAYS-1:0]  = {pt.ICACHE_NUM_WAYS{ic_rd_en | clk_override}} | ic_wr_en[pt.ICACHE_NUM_WAYS-1:0] | ic_debug_wr_way_en[pt.ICACHE_NUM_WAYS-1:0] | ic_debug_rd_way_en[pt.ICACHE_NUM_WAYS-1:0];

   rvdff #(1) rd_en_ff (.*, .clk(active_clk),
                    .din (ic_rd_en),
                    .dout(ic_rd_en_ff)) ;


   rvdffie #(32-pt.ICACHE_TAG_LO) adr_ff (.*,
                                          .din ({ic_rw_addr[31:pt.ICACHE_TAG_LO]}),
                                          .dout({ic_rw_addr_ff[31:pt.ICACHE_TAG_LO]})
                                          );

   localparam PAD_BITS = 21 - (32 - pt.ICACHE_TAG_LO);  // sizing for a max tag width.

   // tags
   assign  ic_debug_rd_way_en[pt.ICACHE_NUM_WAYS-1:0] =  {pt.ICACHE_NUM_WAYS{ic_debug_rd_en & ic_debug_tag_array}} & ic_debug_way[pt.ICACHE_NUM_WAYS-1:0] ;
   assign  ic_debug_wr_way_en[pt.ICACHE_NUM_WAYS-1:0] =  {pt.ICACHE_NUM_WAYS{ic_debug_wr_en & ic_debug_tag_array}} & ic_debug_way[pt.ICACHE_NUM_WAYS-1:0] ;

   assign  ic_tag_wren_q[pt.ICACHE_NUM_WAYS-1:0]  =  ic_tag_wren[pt.ICACHE_NUM_WAYS-1:0]          |
                                  ic_debug_wr_way_en[pt.ICACHE_NUM_WAYS-1:0]   ;

   assign  ic_tag_rden_q[pt.ICACHE_NUM_WAYS-1:0]  =  ({pt.ICACHE_NUM_WAYS{ic_rd_en }}  | ic_debug_rd_way_en[pt.ICACHE_NUM_WAYS-1:0] ) &  {pt.ICACHE_NUM_WAYS{~(|ic_wr_en)  & ~ic_debug_wr_en}};

if (pt.ICACHE_TAG_LO == 11) begin: SMALLEST
 if (pt.ICACHE_ECC) begin : ECC1_W
           rvecc_encode  tag_ecc_encode (
                                  .din    ({{pt.ICACHE_TAG_LO{1'b0}}, ic_rw_addr[31:pt.ICACHE_TAG_LO]}),
                                  .ecc_out({ ic_tag_ecc[6:0]}));

   assign  ic_tag_wr_data[25:0] = (ic_debug_wr_en & ic_debug_tag_array) ?
                                  {ic_debug_wr_data[68:64], ic_debug_wr_data[31:11]} :
                                  {ic_tag_ecc[4:0], ic_rw_addr[31:pt.ICACHE_TAG_LO]} ;
 end

 else begin : ECC0_W
           rveven_paritygen #(32-pt.ICACHE_TAG_LO) pargen  (.data_in   (ic_rw_addr[31:pt.ICACHE_TAG_LO]),
                                                 .parity_out(ic_tag_parity));

   assign  ic_tag_wr_data[21:0] = (ic_debug_wr_en & ic_debug_tag_array) ?
                                  {ic_debug_wr_data[64], ic_debug_wr_data[31:11]} :
                                  {ic_tag_parity, ic_rw_addr[31:pt.ICACHE_TAG_LO]} ;
 end // else: !if(pt.ICACHE_ECC)

end // block: SMALLEST


else begin: OTHERS
  if(pt.ICACHE_ECC) begin :ECC1_W
           rvecc_encode  tag_ecc_encode (
                                  .din    ({{pt.ICACHE_TAG_LO{1'b0}}, ic_rw_addr[31:pt.ICACHE_TAG_LO]}),
                                  .ecc_out({ ic_tag_ecc[6:0]}));

   assign  ic_tag_wr_data[25:0] = (ic_debug_wr_en & ic_debug_tag_array) ?
                                  {ic_debug_wr_data[68:64],ic_debug_wr_data[31:11]} :
                                  {ic_tag_ecc[4:0], {PAD_BITS{1'b0}},ic_rw_addr[31:pt.ICACHE_TAG_LO]} ;

  end
  else  begin :ECC0_W
   logic   ic_tag_parity ;
           rveven_paritygen #(32-pt.ICACHE_TAG_LO) pargen  (.data_in   (ic_rw_addr[31:pt.ICACHE_TAG_LO]),
                                                 .parity_out(ic_tag_parity));
   assign  ic_tag_wr_data[21:0] = (ic_debug_wr_en & ic_debug_tag_array) ?
                                  {ic_debug_wr_data[64], ic_debug_wr_data[31:11]} :
                                  {ic_tag_parity, {PAD_BITS{1'b0}},ic_rw_addr[31:pt.ICACHE_TAG_LO]} ;
  end // else: !if(pt.ICACHE_ECC)

end // block: OTHERS


    assign ic_rw_addr_q[pt.ICACHE_INDEX_HI: pt.ICACHE_TAG_INDEX_LO] = (ic_debug_rd_en | ic_debug_wr_en) ?
                                                ic_debug_addr[pt.ICACHE_INDEX_HI: pt.ICACHE_TAG_INDEX_LO] :
                                                ic_rw_addr[pt.ICACHE_INDEX_HI: pt.ICACHE_TAG_INDEX_LO] ;

   rvdff #(pt.ICACHE_NUM_WAYS) tag_rd_wy_ff (.*, .clk(active_clk),
                    .din ({ic_debug_rd_way_en[pt.ICACHE_NUM_WAYS-1:0]}),
                    .dout({ic_debug_rd_way_en_ff[pt.ICACHE_NUM_WAYS-1:0]}));

 if (pt.ICACHE_WAYPACK == 0 ) begin : PACKED_0

   logic [pt.ICACHE_NUM_WAYS-1:0] ic_b_sram_en;
   logic [pt.ICACHE_NUM_WAYS-1:0]                                                                               ic_b_read_en;
   logic [pt.ICACHE_NUM_WAYS-1:0]                                                                               ic_b_write_en;
   logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_TAG_NUM_BYPASS-1:0] [pt.ICACHE_INDEX_HI : pt.ICACHE_TAG_INDEX_LO]   wb_index_hold;
   logic [pt.ICACHE_NUM_WAYS-1:0]                               [pt.ICACHE_INDEX_HI : pt.ICACHE_TAG_INDEX_LO]   ic_b_rw_addr;
   logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_TAG_NUM_BYPASS-1:0]                                                 write_bypass_en;     //bank
   logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_TAG_NUM_BYPASS-1:0]                                                 write_bypass_en_ff;  //bank
   logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_TAG_NUM_BYPASS-1:0]                                                 index_valid;  //bank
   logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_TAG_NUM_BYPASS-1:0]                                                 ic_b_clear_en;
   logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_TAG_NUM_BYPASS-1:0]                                                 ic_b_addr_match;




    logic [pt.ICACHE_NUM_WAYS-1:0] [pt.ICACHE_TAG_NUM_BYPASS_WIDTH-1:0] wrptr;
    logic [pt.ICACHE_NUM_WAYS-1:0] [pt.ICACHE_TAG_NUM_BYPASS_WIDTH-1:0] wrptr_in;
    logic [pt.ICACHE_NUM_WAYS-1:0] [pt.ICACHE_TAG_NUM_BYPASS-1:0]       sel_bypass;
    logic [pt.ICACHE_NUM_WAYS-1:0] [pt.ICACHE_TAG_NUM_BYPASS-1:0]       sel_bypass_ff;



    logic [pt.ICACHE_NUM_WAYS-1:0][25:0]  sel_bypass_data;
    logic [pt.ICACHE_NUM_WAYS-1:0]        any_bypass;
    logic [pt.ICACHE_NUM_WAYS-1:0]        any_addr_match;
    logic [pt.ICACHE_NUM_WAYS-1:0]        ic_tag_clken_final;

    // Use exported ICache interface.
    always_comb begin
      icache_export.ic_tag_clken_final = ic_tag_clken_final;
    end
    for (genvar i=0; i<pt.ICACHE_NUM_WAYS; i++) begin: WAYS

      if (pt.ICACHE_ECC) begin  : ECC1
        logic [pt.ICACHE_NUM_WAYS-1:0] [pt.ICACHE_TAG_NUM_BYPASS-1:0][25 :0] wb_dout_hold;

        if (pt.ICACHE_TAG_DEPTH == 32)   begin : size_32
          `EL2_IC_TAG_SRAM_LOGIC(32,26)
        end // if (pt.ICACHE_TAG_DEPTH == 32)
        if (pt.ICACHE_TAG_DEPTH == 64)   begin : size_64
          `EL2_IC_TAG_SRAM_LOGIC(64,26)
        end // if (pt.ICACHE_TAG_DEPTH == 64)
        if (pt.ICACHE_TAG_DEPTH == 128)   begin : size_128
          `EL2_IC_TAG_SRAM_LOGIC(128,26)
        end // if (pt.ICACHE_TAG_DEPTH == 128)
        if (pt.ICACHE_TAG_DEPTH == 256)   begin : size_256
          `EL2_IC_TAG_SRAM_LOGIC(256,26)
        end // if (pt.ICACHE_TAG_DEPTH == 256)
        if (pt.ICACHE_TAG_DEPTH == 512)   begin : size_512
          `EL2_IC_TAG_SRAM_LOGIC(512,26)
        end // if (pt.ICACHE_TAG_DEPTH == 512)
        if (pt.ICACHE_TAG_DEPTH == 1024)   begin : size_1024
          `EL2_IC_TAG_SRAM_LOGIC(1024,26)
        end // if (pt.ICACHE_TAG_DEPTH == 1024)
        if (pt.ICACHE_TAG_DEPTH == 2048)   begin : size_2048
          `EL2_IC_TAG_SRAM_LOGIC(2048,26)
        end // if (pt.ICACHE_TAG_DEPTH == 2048)
        if (pt.ICACHE_TAG_DEPTH == 4096)   begin  : size_4096
          `EL2_IC_TAG_SRAM_LOGIC(4096,26)
        end // if (pt.ICACHE_TAG_DEPTH == 4096)

        assign w_tout[i][31:pt.ICACHE_TAG_LO] = ic_tag_data_raw[i][31-pt.ICACHE_TAG_LO:0] ;
        assign w_tout[i][36:32]              = ic_tag_data_raw[i][25:21] ;

        rvecc_decode  ecc_decode (
                         .en(~dec_tlu_core_ecc_disable & ic_rd_en_ff),
                         .sed_ded ( 1'b1 ),    // 1 : means only detection
                         .din({11'b0,ic_tag_data_raw[i][20:0]}),
                         .ecc_in({2'b0, ic_tag_data_raw[i][25:21]}),
                         .dout(ic_tag_corrected_data_unc[i][31:0]),
                         .ecc_out(ic_tag_corrected_ecc_unc[i][6:0]),
                         .single_ecc_error(ic_tag_single_ecc_error[i]),
                         .double_ecc_error(ic_tag_double_ecc_error[i]));

        assign ic_tag_way_perr[i]= ic_tag_single_ecc_error[i] | ic_tag_double_ecc_error[i]  ;
      end
      else  begin : ECC0
        logic [pt.ICACHE_NUM_WAYS-1:0] [pt.ICACHE_TAG_NUM_BYPASS-1:0][21 :0] wb_dout_hold;
        assign ic_tag_data_raw_pre[i][25:22] = '0 ;

        if (pt.ICACHE_TAG_DEPTH == 32)   begin : size_32
          `EL2_IC_TAG_SRAM_LOGIC(32,22)
        end // if (pt.ICACHE_TAG_DEPTH == 32)
        if (pt.ICACHE_TAG_DEPTH == 64)   begin : size_64
          `EL2_IC_TAG_SRAM_LOGIC(64,22)
        end // if (pt.ICACHE_TAG_DEPTH == 64)
        if (pt.ICACHE_TAG_DEPTH == 128)   begin : size_128
          `EL2_IC_TAG_SRAM_LOGIC(128,22)
        end // if (pt.ICACHE_TAG_DEPTH == 128)
        if (pt.ICACHE_TAG_DEPTH == 256)   begin : size_256
          `EL2_IC_TAG_SRAM_LOGIC(256,22)
        end // if (pt.ICACHE_TAG_DEPTH == 256)
        if (pt.ICACHE_TAG_DEPTH == 512)   begin : size_512
          `EL2_IC_TAG_SRAM_LOGIC(512,22)
        end // if (pt.ICACHE_TAG_DEPTH == 512)
        if (pt.ICACHE_TAG_DEPTH == 1024)   begin : size_1024
          `EL2_IC_TAG_SRAM_LOGIC(1024,22)
        end // if (pt.ICACHE_TAG_DEPTH == 1024)
        if (pt.ICACHE_TAG_DEPTH == 2048)   begin : size_2048
          `EL2_IC_TAG_SRAM_LOGIC(2048,22)
        end // if (pt.ICACHE_TAG_DEPTH == 2048)
        if (pt.ICACHE_TAG_DEPTH == 4096)   begin  : size_4096
          `EL2_IC_TAG_SRAM_LOGIC(4096,22)
        end // if (pt.ICACHE_TAG_DEPTH == 4096)

        assign w_tout[i][31:pt.ICACHE_TAG_LO] = ic_tag_data_raw[i][31-pt.ICACHE_TAG_LO:0] ;
        assign w_tout[i][32]                 = ic_tag_data_raw[i][21] ;

        rveven_paritycheck #(32-pt.ICACHE_TAG_LO) parcheck(.data_in   (w_tout[i][31:pt.ICACHE_TAG_LO]),
                                                 .parity_in (w_tout[i][32]),
                                                 .parity_err(ic_tag_way_perr[i]));
      end // else: !if(pt.ICACHE_ECC)

   end // block: WAYS
 end // block: PACKED_0


 else begin : PACKED_1


   logic                                                                                ic_b_sram_en;
   logic                                                                                ic_b_read_en;
   logic                                                                                ic_b_write_en;
   logic [pt.ICACHE_TAG_NUM_BYPASS-1:0] [pt.ICACHE_INDEX_HI : pt.ICACHE_TAG_INDEX_LO]   wb_index_hold;
   logic                                [pt.ICACHE_INDEX_HI : pt.ICACHE_TAG_INDEX_LO]   ic_b_rw_addr;
   logic [pt.ICACHE_TAG_NUM_BYPASS-1:0]                                                 write_bypass_en;     //bank
   logic [pt.ICACHE_TAG_NUM_BYPASS-1:0]                                                 write_bypass_en_ff;  //bank
   logic [pt.ICACHE_TAG_NUM_BYPASS-1:0]                                                 index_valid;  //bank
   logic [pt.ICACHE_TAG_NUM_BYPASS-1:0]                                                 ic_b_clear_en;
   logic [pt.ICACHE_TAG_NUM_BYPASS-1:0]                                                 ic_b_addr_match;




    logic [pt.ICACHE_TAG_NUM_BYPASS_WIDTH-1:0]  wrptr;
    logic [pt.ICACHE_TAG_NUM_BYPASS_WIDTH-1:0]  wrptr_in;
    logic [pt.ICACHE_TAG_NUM_BYPASS-1:0]        sel_bypass;
    logic [pt.ICACHE_TAG_NUM_BYPASS-1:0]        sel_bypass_ff;



    logic [(26*pt.ICACHE_NUM_WAYS)-1:0]  sel_bypass_data;
    logic                                any_bypass;
    logic                                any_addr_match;
    logic                                ic_tag_clken_final;

    // Use exported ICache interface.
    always_comb begin
      icache_export.ic_tag_clken_final = ic_tag_clken_final;
    end

   if (pt.ICACHE_ECC) begin  : ECC1
    logic [(26*pt.ICACHE_NUM_WAYS)-1 :0]  ic_tag_data_raw_packed, ic_tag_wren_biten_vec, ic_tag_data_raw_packed_pre;           // data and its bit enables
    logic [pt.ICACHE_TAG_NUM_BYPASS-1:0][(26*pt.ICACHE_NUM_WAYS)-1 :0] wb_packeddout_hold;

    // Use exported ICache interface.
    always_comb begin
      icache_export.ic_tag_wren_biten_vec = ic_tag_wren_biten_vec;
      ic_tag_data_raw_packed_pre = icache_export.ic_tag_data_raw_packed_pre;
    end

    for (genvar i=0; i<pt.ICACHE_NUM_WAYS; i++) begin: BITEN
        assign ic_tag_wren_biten_vec[(26*i)+25:26*i] = {26{ic_tag_wren_q[i]}};
     end
      if (pt.ICACHE_TAG_DEPTH == 32)   begin : size_32
        if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
          `EL2_IC_TAG_PACKED_SRAM_LOGIC(32,104)
        end // block: WAYS
      else begin : WAYS
          `EL2_IC_TAG_PACKED_SRAM_LOGIC(32,52)
        end // block: WAYS
      end // if (pt.ICACHE_TAG_DEPTH == 32

      if (pt.ICACHE_TAG_DEPTH == 64)   begin : size_64
        if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
          `EL2_IC_TAG_PACKED_SRAM_LOGIC(64,104)
        end // block: WAYS
      else begin : WAYS
          `EL2_IC_TAG_PACKED_SRAM_LOGIC(64,52)
        end // block: WAYS
      end // block: size_64

      if (pt.ICACHE_TAG_DEPTH == 128)   begin : size_128
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
          `EL2_IC_TAG_PACKED_SRAM_LOGIC(128,104)
      end // block: WAYS
      else begin : WAYS
          `EL2_IC_TAG_PACKED_SRAM_LOGIC(128,52)
      end // block: WAYS

      end // block: size_128

      if (pt.ICACHE_TAG_DEPTH == 256)   begin : size_256
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
          `EL2_IC_TAG_PACKED_SRAM_LOGIC(256,104)
        end // block: WAYS
       else begin : WAYS
          `EL2_IC_TAG_PACKED_SRAM_LOGIC(256,52)
        end // block: WAYS
      end // block: size_256

      if (pt.ICACHE_TAG_DEPTH == 512)   begin : size_512
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
          `EL2_IC_TAG_PACKED_SRAM_LOGIC(512,104)
        end // block: WAYS
       else begin : WAYS
          `EL2_IC_TAG_PACKED_SRAM_LOGIC(512,52)
        end // block: WAYS
      end // block: size_512

      if (pt.ICACHE_TAG_DEPTH == 1024)   begin : size_1024
         if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
          `EL2_IC_TAG_PACKED_SRAM_LOGIC(1024,104)
        end // block: WAYS
       else begin : WAYS
          `EL2_IC_TAG_PACKED_SRAM_LOGIC(1024,52)
        end // block: WAYS
      end // block: size_1024

      if (pt.ICACHE_TAG_DEPTH == 2048)   begin : size_2048
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
          `EL2_IC_TAG_PACKED_SRAM_LOGIC(2048,104)
        end // block: WAYS
       else begin : WAYS
          `EL2_IC_TAG_PACKED_SRAM_LOGIC(2048,52)
        end // block: WAYS
      end // block: size_2048

      if (pt.ICACHE_TAG_DEPTH == 4096)   begin  : size_4096
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
          `EL2_IC_TAG_PACKED_SRAM_LOGIC(4096,104)
        end // block: WAYS
       else begin : WAYS
          `EL2_IC_TAG_PACKED_SRAM_LOGIC(4096,52)
        end // block: WAYS
      end // block: size_4096

        for (genvar i=0; i<pt.ICACHE_NUM_WAYS; i++) begin
          assign ic_tag_data_raw[i]  = ic_tag_data_raw_packed[(26*i)+25:26*i];
          assign w_tout[i][31:pt.ICACHE_TAG_LO] = ic_tag_data_raw[i][31-pt.ICACHE_TAG_LO:0] ;
          assign w_tout[i][36:32]              = ic_tag_data_raw[i][25:21] ;
          rvecc_decode  ecc_decode (
                           .en(~dec_tlu_core_ecc_disable & ic_rd_en_ff),
                           .sed_ded ( 1'b1 ),    // 1 : means only detection
                           .din({11'b0,ic_tag_data_raw[i][20:0]}),
                           .ecc_in({2'b0, ic_tag_data_raw[i][25:21]}),
                           .dout(ic_tag_corrected_data_unc[i][31:0]),
                           .ecc_out(ic_tag_corrected_ecc_unc[i][6:0]),
                           .single_ecc_error(ic_tag_single_ecc_error[i]),
                           .double_ecc_error(ic_tag_double_ecc_error[i]));

          assign ic_tag_way_perr[i]= ic_tag_single_ecc_error[i] | ic_tag_double_ecc_error[i]  ;
     end // for (genvar i=0; i<pt.ICACHE_NUM_WAYS; i++)

   end // block: ECC1


   else  begin : ECC0
    logic [(22*pt.ICACHE_NUM_WAYS)-1 :0]  ic_tag_data_raw_packed, ic_tag_wren_biten_vec, ic_tag_data_raw_packed_pre;           // data and its bit enables
    logic [pt.ICACHE_TAG_NUM_BYPASS-1:0][(22*pt.ICACHE_NUM_WAYS)-1 :0] wb_packeddout_hold;
    for (genvar i=0; i<pt.ICACHE_NUM_WAYS; i++) begin: BITEN
        assign ic_tag_wren_biten_vec[(22*i)+21:22*i] = {22{ic_tag_wren_q[i]}};
     end
      if (pt.ICACHE_TAG_DEPTH == 32)   begin : size_32
        if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM_LOGIC(32,88)
        end // block: WAYS
      else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM_LOGIC(32,44)
        end // block: WAYS
      end // if (pt.ICACHE_TAG_DEPTH == 32

      if (pt.ICACHE_TAG_DEPTH == 64)   begin : size_64
        if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM_LOGIC(64,88)
        end // block: WAYS
      else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM_LOGIC(64,44)
        end // block: WAYS
      end // block: size_64

      if (pt.ICACHE_TAG_DEPTH == 128)   begin : size_128
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM_LOGIC(128,88)
      end // block: WAYS
      else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM_LOGIC(128,44)
      end // block: WAYS

      end // block: size_128

      if (pt.ICACHE_TAG_DEPTH == 256)   begin : size_256
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM_LOGIC(256,88)
        end // block: WAYS
       else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM_LOGIC(256,44)
        end // block: WAYS
      end // block: size_256

      if (pt.ICACHE_TAG_DEPTH == 512)   begin : size_512
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM_LOGIC(512,88)
        end // block: WAYS
       else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM_LOGIC(512,44)
        end // block: WAYS
      end // block: size_512

      if (pt.ICACHE_TAG_DEPTH == 1024)   begin : size_1024
         if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM_LOGIC(1024,88)
        end // block: WAYS
       else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM_LOGIC(1024,44)
        end // block: WAYS
      end // block: size_1024

      if (pt.ICACHE_TAG_DEPTH == 2048)   begin : size_2048
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM_LOGIC(2048,88)
        end // block: WAYS
       else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM_LOGIC(2048,44)
        end // block: WAYS
      end // block: size_2048

      if (pt.ICACHE_TAG_DEPTH == 4096)   begin  : size_4096
       if (pt.ICACHE_NUM_WAYS == 4) begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM_LOGIC(4096,88)
        end // block: WAYS
       else begin : WAYS
                 `EL2_IC_TAG_PACKED_SRAM_LOGIC(4096,44)
        end // block: WAYS
      end // block: size_4096

      for (genvar i=0; i<pt.ICACHE_NUM_WAYS; i++) begin
          assign ic_tag_data_raw[i]  = ic_tag_data_raw_packed[(22*i)+21:22*i];
          assign w_tout[i][31:pt.ICACHE_TAG_LO] = ic_tag_data_raw[i][31-pt.ICACHE_TAG_LO:0] ;
          assign w_tout[i][32]                 = ic_tag_data_raw[i][21] ;
          assign w_tout[i][36:33]              = '0 ;


          rveven_paritycheck #(32-pt.ICACHE_TAG_LO) parcheck(.data_in   (w_tout[i][31:pt.ICACHE_TAG_LO]),
                                                   .parity_in (w_tout[i][32]),
                                                   .parity_err(ic_tag_way_perr[i]));
      end


   end // block: ECC0
 end // block: PACKED_1


   always_comb begin : tag_rd_out
      ictag_debug_rd_data[25:0] = '0;
      for ( int j=0; j<pt.ICACHE_NUM_WAYS; j++) begin: debug_rd_out
         ictag_debug_rd_data[25:0] |=  pt.ICACHE_ECC ? ({26{ic_debug_rd_way_en_ff[j]}} & ic_tag_data_raw[j] ) : {4'b0, ({22{ic_debug_rd_way_en_ff[j]}} & ic_tag_data_raw[j][21:0])};
      end
   end


   for ( genvar i=0; i<pt.ICACHE_NUM_WAYS; i++) begin : ic_rd_hit_loop
      assign ic_rd_hit[i] = (w_tout[i][31:pt.ICACHE_TAG_LO] == ic_rw_addr_ff[31:pt.ICACHE_TAG_LO]) & ic_tag_valid[i];
   end

   assign  ic_tag_perr  = | (ic_tag_way_perr[pt.ICACHE_NUM_WAYS-1:0] & ic_tag_valid[pt.ICACHE_NUM_WAYS-1:0] ) ;
endmodule // EL2_IC_TAG
