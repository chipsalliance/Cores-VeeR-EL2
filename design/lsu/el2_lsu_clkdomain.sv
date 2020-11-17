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
// Function: Clock Generation Block
// Comments: All the clocks are generate here
//
// //********************************************************************************


module el2_lsu_clkdomain
import el2_pkg::*;
#(
`include "el2_param.vh"
)(
   input logic      clk,                               // Clock only while core active.  Through one clock header.  For flops with    second clock header built in.  Connected to ACTIVE_L2CLK.
   input logic      active_clk,                        // Clock only while core active.  Through two clock headers. For flops without second clock header built in.
   input logic      rst_l,                             // reset, active low
   input logic      dec_tlu_force_halt,                // This will be high till TLU goes to debug halt

   // Inputs
   input logic      clk_override,                      // chciken bit to turn off clock gating
   input logic      dma_dccm_req,                      // dma is active
   input logic      ldst_stbuf_reqvld_r,               // allocating in to the store queue

   input logic      stbuf_reqvld_any,                  // stbuf is draining
   input logic      stbuf_reqvld_flushed_any,          // instruction going to stbuf is flushed
   input logic      lsu_busreq_r,                      // busreq in r
   input logic      lsu_bus_buffer_pend_any,           // bus buffer has a pending bus entry
   input logic      lsu_bus_buffer_empty_any,          // external bus buffer is empty
   input logic      lsu_stbuf_empty_any,               // stbuf is empty

   input logic      lsu_bus_clk_en,                    // bus clock enable

   input el2_lsu_pkt_t  lsu_p,                        // lsu packet in decode
   input el2_lsu_pkt_t  lsu_pkt_d,                    // lsu packet in d
   input el2_lsu_pkt_t  lsu_pkt_m,                    // lsu packet in m
   input el2_lsu_pkt_t  lsu_pkt_r,                    // lsu packet in r

   // Outputs
   output logic     lsu_bus_obuf_c1_clken,             // obuf clock enable
   output logic     lsu_busm_clken,                    // bus clock enable

   output logic     lsu_c1_m_clk,                      // m pipe single pulse clock
   output logic     lsu_c1_r_clk,                      // r pipe single pulse clock

   output logic     lsu_c2_m_clk,                      // m pipe double pulse clock
   output logic     lsu_c2_r_clk,                      // r pipe double pulse clock

   output logic     lsu_store_c1_m_clk,                // store in m
   output logic     lsu_store_c1_r_clk,                // store in r

   output logic     lsu_stbuf_c1_clk,
   output logic     lsu_bus_obuf_c1_clk,               // ibuf clock
   output logic     lsu_bus_ibuf_c1_clk,               // ibuf clock
   output logic     lsu_bus_buf_c1_clk,                // ibuf clock
   output logic     lsu_busm_clk,                      // bus clock

   output logic     lsu_free_c2_clk,                   // free double pulse clock

   input  logic     scan_mode                          // Scan mode
);

   logic lsu_c1_m_clken, lsu_c1_r_clken;
   logic lsu_c2_m_clken, lsu_c2_r_clken;
   logic lsu_c1_m_clken_q, lsu_c1_r_clken_q;
   logic lsu_store_c1_m_clken, lsu_store_c1_r_clken;


   logic lsu_stbuf_c1_clken;
   logic lsu_bus_ibuf_c1_clken, lsu_bus_buf_c1_clken;

   logic lsu_free_c1_clken, lsu_free_c1_clken_q, lsu_free_c2_clken;

   //-------------------------------------------------------------------------------------------
   // Clock Enable logic
   //-------------------------------------------------------------------------------------------

   assign lsu_c1_m_clken = lsu_p.valid | dma_dccm_req | clk_override;
   assign lsu_c1_r_clken = lsu_pkt_m.valid | lsu_c1_m_clken_q | clk_override;

   assign lsu_c2_m_clken = lsu_c1_m_clken | lsu_c1_m_clken_q | clk_override;
   assign lsu_c2_r_clken = lsu_c1_r_clken | lsu_c1_r_clken_q | clk_override;

   assign lsu_store_c1_m_clken = ((lsu_c1_m_clken & lsu_pkt_d.store) | clk_override) ;
   assign lsu_store_c1_r_clken = ((lsu_c1_r_clken & lsu_pkt_m.store) | clk_override) ;

   assign lsu_stbuf_c1_clken = ldst_stbuf_reqvld_r | stbuf_reqvld_any | stbuf_reqvld_flushed_any | clk_override;
   assign lsu_bus_ibuf_c1_clken = lsu_busreq_r | clk_override;
   assign lsu_bus_obuf_c1_clken = (lsu_bus_buffer_pend_any | lsu_busreq_r | clk_override) & lsu_bus_clk_en;
   assign lsu_bus_buf_c1_clken  = ~lsu_bus_buffer_empty_any | lsu_busreq_r | dec_tlu_force_halt | clk_override;

   assign lsu_free_c1_clken = (lsu_p.valid | lsu_pkt_d.valid | lsu_pkt_m.valid | lsu_pkt_r.valid) |
                              ~lsu_bus_buffer_empty_any | ~lsu_stbuf_empty_any | clk_override;
   assign lsu_free_c2_clken = lsu_free_c1_clken | lsu_free_c1_clken_q | clk_override;

    // Flops
   rvdff #(1) lsu_free_c1_clkenff (.din(lsu_free_c1_clken), .dout(lsu_free_c1_clken_q), .clk(active_clk), .*);

   rvdff #(1) lsu_c1_m_clkenff (.din(lsu_c1_m_clken), .dout(lsu_c1_m_clken_q), .clk(lsu_free_c2_clk), .*);
   rvdff #(1) lsu_c1_r_clkenff (.din(lsu_c1_r_clken), .dout(lsu_c1_r_clken_q), .clk(lsu_free_c2_clk), .*);

   // Clock Headers
   rvoclkhdr lsu_c1m_cgc ( .en(lsu_c1_m_clken), .l1clk(lsu_c1_m_clk), .* );
   rvoclkhdr lsu_c1r_cgc ( .en(lsu_c1_r_clken), .l1clk(lsu_c1_r_clk), .* );

   rvoclkhdr lsu_c2m_cgc ( .en(lsu_c2_m_clken), .l1clk(lsu_c2_m_clk), .* );
   rvoclkhdr lsu_c2r_cgc ( .en(lsu_c2_r_clken), .l1clk(lsu_c2_r_clk), .* );

   rvoclkhdr lsu_store_c1m_cgc (.en(lsu_store_c1_m_clken), .l1clk(lsu_store_c1_m_clk), .*);
   rvoclkhdr lsu_store_c1r_cgc (.en(lsu_store_c1_r_clken), .l1clk(lsu_store_c1_r_clk), .*);

   rvoclkhdr lsu_stbuf_c1_cgc ( .en(lsu_stbuf_c1_clken), .l1clk(lsu_stbuf_c1_clk), .* );
   rvoclkhdr lsu_bus_ibuf_c1_cgc ( .en(lsu_bus_ibuf_c1_clken), .l1clk(lsu_bus_ibuf_c1_clk), .* );
   rvoclkhdr lsu_bus_buf_c1_cgc  ( .en(lsu_bus_buf_c1_clken),  .l1clk(lsu_bus_buf_c1_clk), .* );

   assign lsu_busm_clken = (~lsu_bus_buffer_empty_any | lsu_busreq_r | clk_override) & lsu_bus_clk_en;

`ifdef RV_FPGA_OPTIMIZE
   assign lsu_busm_clk = 1'b0;
   assign lsu_bus_obuf_c1_clk = 1'b0;
`else
   rvclkhdr  lsu_bus_obuf_c1_cgc ( .en(lsu_bus_obuf_c1_clken), .l1clk(lsu_bus_obuf_c1_clk), .* );
   rvclkhdr  lsu_busm_cgc (.en(lsu_busm_clken), .l1clk(lsu_busm_clk), .*);
`endif

   rvoclkhdr lsu_free_cgc (.en(lsu_free_c2_clken), .l1clk(lsu_free_c2_clk), .*);

endmodule

