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
// el2_ifu_ifc_ctl.sv
// Function: Fetch pipe control
//
// Comments:
//********************************************************************************

module el2_ifu_ifc_ctl
import el2_pkg::*;
#(
`include "el2_param.vh"
 )
  (
   input logic clk,                         // Clock only while core active.  Through one clock header.  For flops with    second clock header built in.  Connected to ACTIVE_L2CLK.
   input logic free_l2clk,                  // Clock always.                  Through one clock header.  For flops with    second header built in.

   input logic rst_l, // reset enable, from core pin
   // Excluding scan_mode from coverage as its usage is determined by the integrator of the VeeR core.
   /*pragma coverage off*/
   input logic scan_mode, // scan
   /*pragma coverage on*/

   input logic ic_hit_f,      // Icache hit
   input logic ifu_ic_mb_empty, // Miss buffer empty

   input logic ifu_fb_consume1,  // Aligner consumed 1 fetch buffer
   input logic ifu_fb_consume2,  // Aligner consumed 2 fetch buffers

   input logic dec_tlu_flush_noredir_wb, // Don't fetch on flush
   input logic exu_flush_final, // FLush
   input logic [31:1] exu_flush_path_final, // Flush path

   input logic ifu_bp_hit_taken_f, // btb hit, select the target path
   input logic [31:1] ifu_bp_btb_target_f, //  predicted target PC

   input logic ic_dma_active, // IC DMA active, stop fetching
   input logic ic_write_stall, // IC is writing, stop fetching
   input logic dma_iccm_stall_any, // force a stall in the fetch pipe for DMA ICCM access

   input logic [31:0]  dec_tlu_mrac_ff ,   // side_effect and cacheable for each region

   output logic [31:1] ifc_fetch_addr_f, // fetch addr F
   output logic [31:1] ifc_fetch_addr_bf, // fetch addr BF

   output logic  ifc_fetch_req_f,  // fetch request valid F

   output logic  ifu_pmu_fetch_stall, // pmu event measuring fetch stall

   output logic                       ifc_fetch_uncacheable_bf,      // The fetch request is uncacheable space. BF stage
   output logic                      ifc_fetch_req_bf,              // Fetch request. Comes with the address.  BF stage
   output logic                       ifc_fetch_req_bf_raw,          // Fetch request without some qualifications. Used for clock-gating. BF stage
   output logic                       ifc_iccm_access_bf,            // This request is to the ICCM. Do not generate misses to the bus.
   output logic                       ifc_region_acc_fault_bf,       // Access fault. in ICCM region but offset is outside defined ICCM.

   output logic  ifc_dma_access_ok // fetch is not accessing the ICCM, DMA can proceed


   );

   logic [31:1]  fetch_addr_bf;
   logic [31:1]  fetch_addr_next;
   logic [3:0]   fb_write_f, fb_write_ns;

   logic     fb_full_f_ns, fb_full_f;
   logic     fb_right, fb_right2, fb_left, wfm, idle;
   logic     sel_last_addr_bf, sel_next_addr_bf;
   logic     miss_f, miss_a;
   logic     flush_fb, dma_iccm_stall_any_f;
   logic     mb_empty_mod, goto_idle, leave_idle;
   logic     fetch_bf_en;
   logic         line_wrap;
   logic         fetch_addr_next_1;

   // FSM assignment
    typedef enum logic [1:0] { IDLE  = 2'b00 ,
                               FETCH = 2'b01 ,
                               STALL = 2'b10 ,
                               WFM   = 2'b11   } state_t ;
   state_t state      ;
   state_t next_state ;

   logic     dma_stall;
   assign dma_stall = ic_dma_active | dma_iccm_stall_any_f;



   // Fetch address mux
   // - flush
   // - Miss *or* flush during WFM (icache miss buffer is blocking)
   // - Sequential

if(pt.BTB_ENABLE==1) begin : genblock1
   logic sel_btb_addr_bf;

   assign sel_last_addr_bf = ~exu_flush_final & (~ifc_fetch_req_f | ~ic_hit_f);
   assign sel_btb_addr_bf  = ~exu_flush_final & ifc_fetch_req_f & ifu_bp_hit_taken_f & ic_hit_f;
   assign sel_next_addr_bf = ~exu_flush_final & ifc_fetch_req_f & ~ifu_bp_hit_taken_f & ic_hit_f;


   assign fetch_addr_bf[31:1] = ( ({31{exu_flush_final}} &  exu_flush_path_final[31:1]) | // FLUSH path
                  ({31{sel_last_addr_bf}} & ifc_fetch_addr_f[31:1]) | // MISS path
                  ({31{sel_btb_addr_bf}} & {ifu_bp_btb_target_f[31:1]})| // BTB target
                  ({31{sel_next_addr_bf}} & {fetch_addr_next[31:1]})); // SEQ path


end // if (pt.BTB_ENABLE=1)
   else begin
   assign sel_last_addr_bf = ~exu_flush_final & (~ifc_fetch_req_f | ~ic_hit_f);
   assign sel_next_addr_bf = ~exu_flush_final & ifc_fetch_req_f & ic_hit_f;


   assign fetch_addr_bf[31:1] = ( ({31{exu_flush_final}} &  exu_flush_path_final[31:1]) | // FLUSH path
                  ({31{sel_last_addr_bf}} & ifc_fetch_addr_f[31:1]) | // MISS path
                  ({31{sel_next_addr_bf}} & {fetch_addr_next[31:1]})); // SEQ path

end
   assign fetch_addr_next[31:1] = {({ifc_fetch_addr_f[31:2]} + 30'b1), fetch_addr_next_1 };
   assign line_wrap = (fetch_addr_next[pt.ICACHE_TAG_INDEX_LO] ^ ifc_fetch_addr_f[pt.ICACHE_TAG_INDEX_LO]);

   assign fetch_addr_next_1 = line_wrap ? 1'b0 : ifc_fetch_addr_f[1];

   assign ifc_fetch_req_bf_raw = ~idle;
   assign ifc_fetch_req_bf =  ifc_fetch_req_bf_raw &

                 ~(fb_full_f_ns & ~(ifu_fb_consume2 | ifu_fb_consume1)) &
                 ~dma_stall &
                 ~ic_write_stall &
                 ~dec_tlu_flush_noredir_wb;


   assign fetch_bf_en = exu_flush_final | ifc_fetch_req_f;

   assign miss_f = ifc_fetch_req_f & ~ic_hit_f & ~exu_flush_final;

   assign mb_empty_mod = (ifu_ic_mb_empty | exu_flush_final) & ~dma_stall & ~miss_f & ~miss_a;

   // Halt flushes and takes us to IDLE
   assign goto_idle = exu_flush_final & dec_tlu_flush_noredir_wb;
   // If we're in IDLE, and we get a flush, goto FETCH
   assign leave_idle = exu_flush_final & ~dec_tlu_flush_noredir_wb & idle;

//.i 7
//.o 2
//.ilb state[1] state[0] reset_delayed miss_f mb_empty_mod  goto_idle leave_idle
//.ob next_state[1] next_state[0]
//.type fr
//
//# fetch 01, stall 10, wfm 11, idle 00
//-- 1---- 01
//-- 0--1- 00
//00 0--00 00
//00 0--01 01
//
//01 01-0- 11
//01 00-0- 01
//
//11 0-10- 01
//11 0-00- 11

   assign next_state[1] = (~state[1] & state[0] & miss_f & ~goto_idle) |
              (state[1] & ~mb_empty_mod & ~goto_idle);

   assign next_state[0] = (~goto_idle & leave_idle) | (state[0] & ~goto_idle);

   assign flush_fb = exu_flush_final;

   // model fb write logic to mass balance the fetch buffers
   assign fb_right = ( ifu_fb_consume1 & ~ifu_fb_consume2 & (~ifc_fetch_req_f | miss_f)) | // Consumed and no new fetch
              (ifu_fb_consume2 &  ifc_fetch_req_f); // Consumed 2 and new fetch


   assign fb_right2 = (ifu_fb_consume2 & (~ifc_fetch_req_f | miss_f)); // Consumed 2 and no new fetch

   assign fb_left = ifc_fetch_req_f & ~(ifu_fb_consume1 | ifu_fb_consume2) & ~miss_f;

// CBH
   assign fb_write_ns[3:0] = ( ({4{(flush_fb)}} & 4'b0001) |
                   ({4{~flush_fb & fb_right }} & {1'b0, fb_write_f[3:1]}) |
                   ({4{~flush_fb & fb_right2}} & {2'b0, fb_write_f[3:2]}) |
                   ({4{~flush_fb & fb_left  }} & {fb_write_f[2:0], 1'b0}) |
                   ({4{~flush_fb & ~fb_right & ~fb_right2 & ~fb_left}}  & fb_write_f[3:0]));


   assign fb_full_f_ns = fb_write_ns[3];

   assign idle     = state      == IDLE  ;
   assign wfm      = state      == WFM   ;

   rvdffie #(10) fbwrite_ff (.*, .clk(free_l2clk),
                          .din( {dma_iccm_stall_any, miss_f, ifc_fetch_req_bf, next_state[1:0], fb_full_f_ns, fb_write_ns[3:0]}),
                          .dout({dma_iccm_stall_any_f, miss_a, ifc_fetch_req_f, state[1:0], fb_full_f, fb_write_f[3:0]}));

   assign ifu_pmu_fetch_stall = wfm |
                (ifc_fetch_req_bf_raw &
                ( (fb_full_f & ~(ifu_fb_consume2 | ifu_fb_consume1 | exu_flush_final)) |
                  dma_stall));



   assign ifc_fetch_addr_bf[31:1] = fetch_addr_bf[31:1];

   rvdffpcie #(31) faddrf1_ff  (.*, .en(fetch_bf_en), .din(fetch_addr_bf[31:1]), .dout(ifc_fetch_addr_f[31:1]));


 if (pt.ICCM_ENABLE)  begin : genblock2
   logic iccm_acc_in_region_bf;
   logic iccm_acc_in_range_bf;
   rvrangecheck #( .CCM_SADR    (pt.ICCM_SADR),
                   .CCM_SIZE    (pt.ICCM_SIZE) ) iccm_rangecheck (
                                     .addr     ({ifc_fetch_addr_bf[31:1],1'b0}) ,
                                     .in_range (iccm_acc_in_range_bf) ,
                                     .in_region(iccm_acc_in_region_bf)
                                     );

   assign ifc_iccm_access_bf = iccm_acc_in_range_bf ;

  assign ifc_dma_access_ok = ( (~ifc_iccm_access_bf |
                 (fb_full_f & ~(ifu_fb_consume2 | ifu_fb_consume1)) |
                 (wfm  & ~ifc_fetch_req_bf) |
                 idle ) & ~exu_flush_final) |
                  dma_iccm_stall_any_f;

  assign ifc_region_acc_fault_bf = ~iccm_acc_in_range_bf & iccm_acc_in_region_bf ;
 end
 else  begin
   assign ifc_iccm_access_bf = 1'b0 ;
   assign ifc_dma_access_ok  = 1'b0 ;
   assign ifc_region_acc_fault_bf  = 1'b0 ;
 end

   assign ifc_fetch_uncacheable_bf =  ~dec_tlu_mrac_ff[{ifc_fetch_addr_bf[31:28] , 1'b0 }]  ; // bit 0 of each region description is the cacheable bit

endmodule // el2_ifu_ifc_ctl

