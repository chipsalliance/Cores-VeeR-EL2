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
module el2_lsu_bus_intf
import el2_pkg::*;
#(
`include "el2_param.vh"
 )(
   input logic                          clk,                                // Clock only while core active.  Through one clock header.  For flops with    second clock header built in.  Connected to ACTIVE_L2CLK.
   input logic                          clk_override,                       // Override non-functional clock gating
   input logic                          rst_l,                              // reset, active low
   input logic                          scan_mode,                          // scan mode
   input logic                          dec_tlu_external_ldfwd_disable,     // disable load to load forwarding for externals
   input logic                          dec_tlu_wb_coalescing_disable,      // disable write buffer coalescing
   input logic                          dec_tlu_sideeffect_posted_disable,  // disable the posted sideeffect load store to the bus

   // various clocks needed for the bus reads and writes
   input logic                          lsu_bus_obuf_c1_clken,              // obuf clock enable
   input logic                          lsu_busm_clken,                     // bus clock enable

   input logic                          lsu_c1_r_clk,                       // r pipe single pulse clock
   input logic                          lsu_c2_r_clk,                       // r pipe double pulse clock
   input logic                          lsu_bus_ibuf_c1_clk,                // ibuf single pulse clock
   input logic                          lsu_bus_obuf_c1_clk,                // obuf single pulse clock
   input logic                          lsu_bus_buf_c1_clk,                 // buf  single pulse clock
   input logic                          lsu_free_c2_clk,                    // free clock double pulse clock
   input logic                          active_clk,                         // Clock only while core active.  Through two clock headers. For flops without second clock header built in.
   input logic                          lsu_busm_clk,                       // bus clock

   input logic                          dec_lsu_valid_raw_d,               // Raw valid for address computation
   input logic                          lsu_busreq_m,                      // bus request is in m

   input                                el2_lsu_pkt_t lsu_pkt_m,          // lsu packet flowing down the pipe
   input                                el2_lsu_pkt_t lsu_pkt_r,          // lsu packet flowing down the pipe

   input logic [31:0]                   lsu_addr_m,                        // lsu address flowing down the pipe
   input logic [31:0]                   lsu_addr_r,                        // lsu address flowing down the pipe

   input logic [31:0]                   end_addr_m,                        // lsu address flowing down the pipe
   input logic [31:0]                   end_addr_r,                        // lsu address flowing down the pipe

   input logic [31:0]                   store_data_r,                      // store data flowing down the pipe
   input logic                          dec_tlu_force_halt,

   input logic                          lsu_commit_r,                      // lsu instruction in r commits
   input logic                          is_sideeffects_m,                  // lsu attribute is side_effects
   input logic                          flush_m_up,                        // flush
   input logic                          flush_r,                           // flush
   input logic                          ldst_dual_d, ldst_dual_m, ldst_dual_r,

   output logic                         lsu_busreq_r,                      // bus request is in r
   output logic                         lsu_bus_buffer_pend_any,           // bus buffer has a pending bus entry
   output logic                         lsu_bus_buffer_full_any,           // write buffer is full
   output logic                         lsu_bus_buffer_empty_any,          // write buffer is empty
   output logic [31:0]                  bus_read_data_m,                   // the bus return data


   output logic                         lsu_imprecise_error_load_any,      // imprecise load bus error
   output logic                         lsu_imprecise_error_store_any,     // imprecise store bus error
   output logic [31:0]                  lsu_imprecise_error_addr_any,      // address of the imprecise error

   // Non-blocking loads
   output logic                               lsu_nonblock_load_valid_m,   // there is an external load -> put in the cam
   output logic [pt.LSU_NUM_NBLOAD_WIDTH-1:0] lsu_nonblock_load_tag_m,     // the tag of the external non block load
   output logic                               lsu_nonblock_load_inv_r,     // invalidate signal for the cam entry for non block loads
   output logic [pt.LSU_NUM_NBLOAD_WIDTH-1:0] lsu_nonblock_load_inv_tag_r, // tag of the enrty which needs to be invalidated
   output logic                               lsu_nonblock_load_data_valid,// the non block is valid - sending information back to the cam
   output logic                               lsu_nonblock_load_data_error,// non block load has an error
   output logic [pt.LSU_NUM_NBLOAD_WIDTH-1:0] lsu_nonblock_load_data_tag,  // the tag of the non block load sending the data/error
   output logic [31:0]                        lsu_nonblock_load_data,      // Data of the non block load

   // PMU events
   output logic                         lsu_pmu_bus_trxn,
   output logic                         lsu_pmu_bus_misaligned,
   output logic                         lsu_pmu_bus_error,
   output logic                         lsu_pmu_bus_busy,

   // AXI Write Channels
   output logic                        lsu_axi_awvalid,
   input  logic                        lsu_axi_awready,
   output logic [pt.LSU_BUS_TAG-1:0]   lsu_axi_awid,
   output logic [31:0]                 lsu_axi_awaddr,
   output logic [3:0]                  lsu_axi_awregion,
   output logic [7:0]                  lsu_axi_awlen,
   output logic [2:0]                  lsu_axi_awsize,
   output logic [1:0]                  lsu_axi_awburst,
   output logic                        lsu_axi_awlock,
   output logic [3:0]                  lsu_axi_awcache,
   output logic [2:0]                  lsu_axi_awprot,
   output logic [3:0]                  lsu_axi_awqos,

   output logic                        lsu_axi_wvalid,
   input  logic                        lsu_axi_wready,
   output logic [63:0]                 lsu_axi_wdata,
   output logic [7:0]                  lsu_axi_wstrb,
   output logic                        lsu_axi_wlast,

   input  logic                        lsu_axi_bvalid,
   output logic                        lsu_axi_bready,
   input  logic [1:0]                  lsu_axi_bresp,
   input  logic [pt.LSU_BUS_TAG-1:0]   lsu_axi_bid,

   // AXI Read Channels
   output logic                        lsu_axi_arvalid,
   input  logic                        lsu_axi_arready,
   output logic [pt.LSU_BUS_TAG-1:0]   lsu_axi_arid,
   output logic [31:0]                 lsu_axi_araddr,
   output logic [3:0]                  lsu_axi_arregion,
   output logic [7:0]                  lsu_axi_arlen,
   output logic [2:0]                  lsu_axi_arsize,
   output logic [1:0]                  lsu_axi_arburst,
   output logic                        lsu_axi_arlock,
   output logic [3:0]                  lsu_axi_arcache,
   output logic [2:0]                  lsu_axi_arprot,
   output logic [3:0]                  lsu_axi_arqos,

   input  logic                        lsu_axi_rvalid,
   output logic                        lsu_axi_rready,
   input  logic [pt.LSU_BUS_TAG-1:0]   lsu_axi_rid,
   input  logic [63:0]                 lsu_axi_rdata,
   input  logic [1:0]                  lsu_axi_rresp,

   input logic                         lsu_bus_clk_en

);



   logic              lsu_bus_clk_en_q;

   logic [3:0]        ldst_byteen_m, ldst_byteen_r;
   logic [7:0]        ldst_byteen_ext_m, ldst_byteen_ext_r;
   logic [3:0]        ldst_byteen_hi_m, ldst_byteen_hi_r;
   logic [3:0]        ldst_byteen_lo_m, ldst_byteen_lo_r;
   logic              is_sideeffects_r;

   logic [63:0]       store_data_ext_r;
   logic [31:0]       store_data_hi_r;
   logic [31:0]       store_data_lo_r;

   logic              addr_match_dw_lo_r_m;
   logic              addr_match_word_lo_r_m;
   logic              no_word_merge_r, no_dword_merge_r;

   logic              ld_addr_rhit_lo_lo, ld_addr_rhit_hi_lo, ld_addr_rhit_lo_hi, ld_addr_rhit_hi_hi;
   logic [3:0]        ld_byte_rhit_lo_lo, ld_byte_rhit_hi_lo, ld_byte_rhit_lo_hi, ld_byte_rhit_hi_hi;

   logic [3:0]        ld_byte_hit_lo, ld_byte_rhit_lo;
   logic [3:0]        ld_byte_hit_hi, ld_byte_rhit_hi;

   logic [31:0]       ld_fwddata_rpipe_lo;
   logic [31:0]       ld_fwddata_rpipe_hi;

   logic [3:0]        ld_byte_hit_buf_lo, ld_byte_hit_buf_hi;
   logic [31:0]       ld_fwddata_buf_lo, ld_fwddata_buf_hi;

   logic [63:0]       ld_fwddata_lo, ld_fwddata_hi;
   logic [63:0]       ld_fwddata_m;

   logic              ld_full_hit_hi_m, ld_full_hit_lo_m;
   logic              ld_full_hit_m;

   assign ldst_byteen_m[3:0] = ({4{lsu_pkt_m.by}}   & 4'b0001) |
                                 ({4{lsu_pkt_m.half}} & 4'b0011) |
                                 ({4{lsu_pkt_m.word}} & 4'b1111);

   // Read/Write Buffer
   el2_lsu_bus_buffer #(.pt(pt)) bus_buffer (
      .*
   );

   // Logic to determine if dc5 store can be coalesced or not with younger stores. Bypass ibuf if cannot colaesced
   assign addr_match_dw_lo_r_m = (lsu_addr_r[31:3] == lsu_addr_m[31:3]);
   assign addr_match_word_lo_r_m = addr_match_dw_lo_r_m & ~(lsu_addr_r[2]^lsu_addr_m[2]);

   assign no_word_merge_r  = lsu_busreq_r & ~ldst_dual_r & lsu_busreq_m & (lsu_pkt_m.load | ~addr_match_word_lo_r_m);
   assign no_dword_merge_r = lsu_busreq_r & ~ldst_dual_r & lsu_busreq_m & (lsu_pkt_m.load | ~addr_match_dw_lo_r_m);

   // Create Hi/Lo signals
   assign ldst_byteen_ext_m[7:0] = {4'b0,ldst_byteen_m[3:0]} << lsu_addr_m[1:0];
   assign ldst_byteen_ext_r[7:0] = {4'b0,ldst_byteen_r[3:0]} << lsu_addr_r[1:0];

   assign store_data_ext_r[63:0] = {32'b0,store_data_r[31:0]} << {lsu_addr_r[1:0],3'b0};

   assign ldst_byteen_hi_m[3:0]   = ldst_byteen_ext_m[7:4];
   assign ldst_byteen_lo_m[3:0]   = ldst_byteen_ext_m[3:0];
   assign ldst_byteen_hi_r[3:0]   = ldst_byteen_ext_r[7:4];
   assign ldst_byteen_lo_r[3:0]   = ldst_byteen_ext_r[3:0];

   assign store_data_hi_r[31:0]   = store_data_ext_r[63:32];
   assign store_data_lo_r[31:0]   = store_data_ext_r[31:0];

   assign ld_addr_rhit_lo_lo = (lsu_addr_m[31:2] == lsu_addr_r[31:2]) & lsu_pkt_r.valid & lsu_pkt_r.store & lsu_busreq_m & lsu_busreq_r;
   assign ld_addr_rhit_lo_hi = (end_addr_m[31:2] == lsu_addr_r[31:2]) & lsu_pkt_r.valid & lsu_pkt_r.store & lsu_busreq_m & lsu_busreq_r;
   assign ld_addr_rhit_hi_lo = (lsu_addr_m[31:2] == end_addr_r[31:2]) & lsu_pkt_r.valid & lsu_pkt_r.store & lsu_busreq_m & lsu_busreq_r;
   assign ld_addr_rhit_hi_hi = (end_addr_m[31:2] == end_addr_r[31:2]) & lsu_pkt_r.valid & lsu_pkt_r.store & lsu_busreq_m & lsu_busreq_r;

   for (genvar i=0; i<4; i++) begin: GenBusBufFwd
      assign ld_byte_rhit_lo_lo[i] = ld_addr_rhit_lo_lo & ldst_byteen_lo_r[i] & ldst_byteen_lo_m[i];
      assign ld_byte_rhit_lo_hi[i] = ld_addr_rhit_lo_hi & ldst_byteen_lo_r[i] & ldst_byteen_hi_m[i];
      assign ld_byte_rhit_hi_lo[i] = ld_addr_rhit_hi_lo & ldst_byteen_hi_r[i] & ldst_byteen_lo_m[i];
      assign ld_byte_rhit_hi_hi[i] = ld_addr_rhit_hi_hi & ldst_byteen_hi_r[i] & ldst_byteen_hi_m[i];

      assign ld_byte_hit_lo[i] = ld_byte_rhit_lo_lo[i] | ld_byte_rhit_hi_lo[i] |
                                 ld_byte_hit_buf_lo[i];

      assign ld_byte_hit_hi[i] = ld_byte_rhit_lo_hi[i] | ld_byte_rhit_hi_hi[i] |
                                 ld_byte_hit_buf_hi[i];

      assign ld_byte_rhit_lo[i] = ld_byte_rhit_lo_lo[i] | ld_byte_rhit_hi_lo[i];
      assign ld_byte_rhit_hi[i] = ld_byte_rhit_lo_hi[i] | ld_byte_rhit_hi_hi[i];

      assign ld_fwddata_rpipe_lo[(8*i)+7:(8*i)] = ({8{ld_byte_rhit_lo_lo[i]}} & store_data_lo_r[(8*i)+7:(8*i)]) |
                                                    ({8{ld_byte_rhit_hi_lo[i]}} & store_data_hi_r[(8*i)+7:(8*i)]);

      assign ld_fwddata_rpipe_hi[(8*i)+7:(8*i)] = ({8{ld_byte_rhit_lo_hi[i]}} & store_data_lo_r[(8*i)+7:(8*i)]) |
                                                    ({8{ld_byte_rhit_hi_hi[i]}} & store_data_hi_r[(8*i)+7:(8*i)]);

      // Final muxing between m/r
      assign ld_fwddata_lo[(8*i)+7:(8*i)] = ld_byte_rhit_lo[i]    ? ld_fwddata_rpipe_lo[(8*i)+7:(8*i)] : ld_fwddata_buf_lo[(8*i)+7:(8*i)];

      assign ld_fwddata_hi[(8*i)+7:(8*i)] = ld_byte_rhit_hi[i]    ? ld_fwddata_rpipe_hi[(8*i)+7:(8*i)] : ld_fwddata_buf_hi[(8*i)+7:(8*i)];

   end

   always_comb begin
      ld_full_hit_lo_m = 1'b1;
      ld_full_hit_hi_m = 1'b1;
      for (int i=0; i<4; i++) begin
         ld_full_hit_lo_m &= (ld_byte_hit_lo[i] | ~ldst_byteen_lo_m[i]);
         ld_full_hit_hi_m &= (ld_byte_hit_hi[i] | ~ldst_byteen_hi_m[i]);
      end
   end

   // This will be high if all the bytes of load hit the stores in pipe/write buffer (m/r/wrbuf)
   assign ld_full_hit_m = ld_full_hit_lo_m & ld_full_hit_hi_m & lsu_busreq_m & lsu_pkt_m.load & ~is_sideeffects_m;

   assign ld_fwddata_m[63:0] = 64'({ld_fwddata_hi[31:0], ld_fwddata_lo[31:0]} >> (8*lsu_addr_m[1:0]));
   assign bus_read_data_m[31:0]                        = ld_fwddata_m[31:0];

   // Fifo flops

   rvdff #(.WIDTH(1)) clken_ff (.din(lsu_bus_clk_en), .dout(lsu_bus_clk_en_q), .clk(active_clk), .*);

   rvdff #(.WIDTH(1)) is_sideeffects_rff (.din(is_sideeffects_m), .dout(is_sideeffects_r), .clk(lsu_c1_r_clk), .*);

   rvdff #(4) lsu_byten_rff (.*, .din(ldst_byteen_m[3:0]), .dout(ldst_byteen_r[3:0]), .clk(lsu_c1_r_clk));

`ifdef RV_ASSERT_ON

  // Assertion to check AXI write address is aligned to size
  property lsu_axi_awaddr_aligned;
    @(posedge lsu_busm_clk) disable iff(~rst_l) lsu_axi_awvalid |-> ((lsu_axi_awsize[2:0] == 3'h0)                                   |
                                                                     ((lsu_axi_awsize[2:0] == 3'h1) & (lsu_axi_awaddr[0] == 1'b0))   |
                                                                     ((lsu_axi_awsize[2:0] == 3'h2) & (lsu_axi_awaddr[1:0] == 2'b0)) |
                                                                     ((lsu_axi_awsize[2:0] == 3'h3) & (lsu_axi_awaddr[2:0] == 3'b0)));
  endproperty
  assert_lsu_axi_awaddr_aligned: assert property (lsu_axi_awaddr_aligned) else
    $display("Assertion lsu_axi_awaddr_aligned failed: lsu_axi_awvalid=1'b%b, lsu_axi_awsize=3'h%h, lsu_axi_awaddr=32'h%h",lsu_axi_awvalid, lsu_axi_awsize[2:0], lsu_axi_awaddr[31:0]);
  // Assertion to check awvalid stays stable during entire bus clock

  // Assertion to check AXI read address is aligned to size
  property lsu_axi_araddr_aligned;
    @(posedge lsu_busm_clk) disable iff(~rst_l) lsu_axi_arvalid |-> ((lsu_axi_arsize[2:0] == 3'h0)                                   |
                                                                     ((lsu_axi_arsize[2:0] == 3'h1) & (lsu_axi_araddr[0] == 1'b0))   |
                                                                     ((lsu_axi_arsize[2:0] == 3'h2) & (lsu_axi_araddr[1:0] == 2'b0)) |
                                                                     ((lsu_axi_arsize[2:0] == 3'h3) & (lsu_axi_araddr[2:0] == 3'b0)));
  endproperty
  assert_lsu_axi_araddr_aligned: assert property (lsu_axi_araddr_aligned) else
    $display("Assertion lsu_axi_araddr_aligned failed: lsu_axi_awvalid=1'b%b, lsu_axi_awsize=3'h%h, lsu_axi_araddr=32'h%h",lsu_axi_awvalid, lsu_axi_awsize[2:0], lsu_axi_araddr[31:0]);

  // Assertion to check awvalid stays stable during entire bus clock
 property lsu_axi_awvalid_stable;
     @(posedge clk) disable iff(~rst_l)  (lsu_axi_awvalid != $past(lsu_axi_awvalid)) |-> ($past(lsu_bus_clk_en) | dec_tlu_force_halt);
  endproperty
  assert_lsu_axi_awvalid_stable: assert property (lsu_axi_awvalid_stable) else
     $display("LSU AXI awvalid changed in middle of bus clock");

  // Assertion to check awid stays stable during entire bus clock
  property lsu_axi_awid_stable;
     @(posedge clk) disable iff(~rst_l)  (lsu_axi_awvalid & (lsu_axi_awid[pt.LSU_BUS_TAG-1:0] != $past(lsu_axi_awid[pt.LSU_BUS_TAG-1:0]))) |-> $past(lsu_bus_clk_en);
  endproperty
  assert_lsu_axi_awid_stable: assert property (lsu_axi_awid_stable) else
     $display("LSU AXI awid changed in middle of bus clock");

  // Assertion to check awaddr stays stable during entire bus clock
  property lsu_axi_awaddr_stable;
     @(posedge clk) disable iff(~rst_l)  (lsu_axi_awvalid & (lsu_axi_awaddr[31:0] != $past(lsu_axi_awaddr[31:0]))) |-> $past(lsu_bus_clk_en);
  endproperty
  assert_lsu_axi_awaddr_stable: assert property (lsu_axi_awaddr_stable) else
     $display("LSU AXI awaddr changed in middle of bus clock");

  // Assertion to check awsize stays stable during entire bus clock
  property lsu_axi_awsize_stable;
     @(posedge clk) disable iff(~rst_l)  (lsu_axi_awvalid & (lsu_axi_awsize[2:0] != $past(lsu_axi_awsize[2:0]))) |-> $past(lsu_bus_clk_en);
  endproperty
  assert_lsu_axi_awsize_stable: assert property (lsu_axi_awsize_stable) else
     $display("LSU AXI awsize changed in middle of bus clock");

  // Assertion to check wstrb stays stable during entire bus clock
  property lsu_axi_wstrb_stable;
     @(posedge clk) disable iff(~rst_l)  (lsu_axi_wvalid & (lsu_axi_wstrb[7:0] != $past(lsu_axi_wstrb[7:0]))) |-> $past(lsu_bus_clk_en);
  endproperty
  assert_lsu_axi_wstrb_stable: assert property (lsu_axi_wstrb_stable) else
     $display("LSU AXI wstrb changed in middle of bus clock");

  // Assertion to check wdata stays stable during entire bus clock
  property lsu_axi_wdata_stable;
     @(posedge clk) disable iff(~rst_l)  (lsu_axi_wvalid & (lsu_axi_wdata[63:0] != $past(lsu_axi_wdata[63:0]))) |-> $past(lsu_bus_clk_en);
  endproperty
  assert_lsu_axi_wdata_stable: assert property (lsu_axi_wdata_stable) else
     $display("LSU AXI wdata changed in middle of bus clock");

  // Assertion to check awvalid stays stable during entire bus clock
  property lsu_axi_arvalid_stable;
     @(posedge clk) disable iff(~rst_l)  (lsu_axi_arvalid != $past(lsu_axi_arvalid)) |-> ($past(lsu_bus_clk_en) | dec_tlu_force_halt);
  endproperty
  assert_lsu_axi_arvalid_stable: assert property (lsu_axi_arvalid_stable) else
     $display("LSU AXI awvalid changed in middle of bus clock");

  // Assertion to check awid stays stable during entire bus clock
  property lsu_axi_arid_stable;
     @(posedge clk) disable iff(~rst_l)  (lsu_axi_arvalid & (lsu_axi_arid[pt.LSU_BUS_TAG-1:0] != $past(lsu_axi_arid[pt.LSU_BUS_TAG-1:0]))) |-> $past(lsu_bus_clk_en);
  endproperty
  assert_lsu_axi_arid_stable: assert property (lsu_axi_arid_stable) else
     $display("LSU AXI awid changed in middle of bus clock");

  // Assertion to check awaddr stays stable during entire bus clock
  property lsu_axi_araddr_stable;
     @(posedge clk) disable iff(~rst_l)  (lsu_axi_arvalid & (lsu_axi_araddr[31:0] != $past(lsu_axi_araddr[31:0]))) |-> $past(lsu_bus_clk_en);
  endproperty
  assert_lsu_axi_araddr_stable: assert property (lsu_axi_araddr_stable) else
     $display("LSU AXI awaddr changed in middle of bus clock");

  // Assertion to check awsize stays stable during entire bus clock
  property lsu_axi_arsize_stable;
     @(posedge clk) disable iff(~rst_l)  (lsu_axi_awvalid & (lsu_axi_arsize[2:0] != $past(lsu_axi_arsize[2:0]))) |-> $past(lsu_bus_clk_en);
  endproperty
  assert_lsu_axi_arsize_stable: assert property (lsu_axi_arsize_stable) else
     $display("LSU AXI awsize changed in middle of bus clock");

`endif

endmodule // el2_lsu_bus_intf
