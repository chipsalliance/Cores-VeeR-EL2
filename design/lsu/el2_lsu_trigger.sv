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
// Function: LSU Trigger logic
// Comments:
//
//********************************************************************************
module el2_lsu_trigger
import el2_pkg::*;
#(
`include "el2_param.vh"
 )(
   input el2_trigger_pkt_t [3:0] trigger_pkt_any,            // trigger packet from dec
   input el2_lsu_pkt_t           lsu_pkt_m,                  // lsu packet
   input logic [31:0]             lsu_addr_m,                 // address
   input logic [31:0]             store_data_m,               // store data

   output logic [3:0]             lsu_trigger_match_m         // match result
);

   logic               trigger_enable;
   logic [3:0][31:0]  lsu_match_data;
   logic [3:0]        lsu_trigger_data_match;
   logic [31:0]       store_data_trigger_m;
   logic [31:0]       ldst_addr_trigger_m;

   // Generate the trigger enable (This is for power)
   always_comb begin
      trigger_enable = 1'b0;
      for (int i=0; i<4; i++) begin
         trigger_enable |= trigger_pkt_any[i].m;
      end
   end

   assign store_data_trigger_m[31:0] = {({16{lsu_pkt_m.word}} & store_data_m[31:16]),({8{(lsu_pkt_m.half | lsu_pkt_m.word)}} & store_data_m[15:8]), store_data_m[7:0]} & {32{trigger_enable}};
   assign ldst_addr_trigger_m[31:0]  = lsu_addr_m[31:0] & {32{trigger_enable}};


   for (genvar i=0; i<4; i++) begin : genblock
      assign lsu_match_data[i][31:0] = ({32{~trigger_pkt_any[i].select}} & ldst_addr_trigger_m[31:0]) |
                                       ({32{trigger_pkt_any[i].select & trigger_pkt_any[i].store}} & store_data_trigger_m[31:0]);

      rvmaskandmatch trigger_match (.mask(trigger_pkt_any[i].tdata2[31:0]), .data(lsu_match_data[i][31:0]), .masken(trigger_pkt_any[i].match), .match(lsu_trigger_data_match[i]));

      assign lsu_trigger_match_m[i] = lsu_pkt_m.valid & ~lsu_pkt_m.dma & trigger_enable &
                                        ((trigger_pkt_any[i].store & lsu_pkt_m.store) | (trigger_pkt_any[i].load & lsu_pkt_m.load & ~trigger_pkt_any[i].select)) &
                                        lsu_trigger_data_match[i];
   end


endmodule // el2_lsu_trigger
