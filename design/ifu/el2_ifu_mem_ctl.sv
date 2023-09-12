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
// Function: Icache , iccm  control
// BFF -> F1 -> F2 -> A
//********************************************************************************

module el2_ifu_mem_ctl
import el2_pkg::*;
#(
`include "el2_param.vh"
 )
  (
   input logic clk,                                                 // Clock only while core active.  Through one clock header.  For flops with    second clock header built in.  Connected to ACTIVE_L2CLK.
   input logic active_clk,                                          // Clock only while core active.  Through two clock headers. For flops without second clock header built in.
   input logic free_l2clk,                                          // Clock always.                  Through one clock header.  For flops with    second header built in.
   input logic rst_l,                                               // reset, active low

   input logic                       exu_flush_final,               // Flush from the pipeline., includes flush lower
   input logic                       dec_tlu_flush_lower_wb,        // Flush lower from the pipeline.
   input logic                       dec_tlu_flush_err_wb,          // Flush from the pipeline due to perr.
   input logic                       dec_tlu_i0_commit_cmt,         // committed i0 instruction
   input logic                       dec_tlu_force_halt,            // force halt.

   input logic [31:1]                ifc_fetch_addr_bf,             // Fetch Address byte aligned always.      F1 stage.
   input logic                       ifc_fetch_uncacheable_bf,      // The fetch request is uncacheable space. F1 stage
   input logic                       ifc_fetch_req_bf,              // Fetch request. Comes with the address.  F1 stage
   input logic                       ifc_fetch_req_bf_raw,          // Fetch request without some qualifications. Used for clock-gating. F1 stage
   input logic                       ifc_iccm_access_bf,            // This request is to the ICCM. Do not generate misses to the bus.
   input logic                       ifc_region_acc_fault_bf,       // Access fault. in ICCM region but offset is outside defined ICCM.
   input logic                       ifc_dma_access_ok,             // It is OK to give dma access to the ICCM. (ICCM is not busy this cycle).
   input logic                       dec_tlu_fence_i_wb,            // Fence.i instruction is committing. Clear all Icache valids.
   input logic                       ifu_bp_hit_taken_f,            // Branch is predicted taken. Kill the fetch next cycle.

   input logic                       ifu_bp_inst_mask_f,            // tell ic which valids to kill because of a taken branch, right justified

   output logic                      ifu_miss_state_idle,           // No icache misses are outstanding.
   output logic                      ifu_ic_mb_empty,               // Continue with normal fetching. This does not mean that miss is finished.
   output logic                      ic_dma_active  ,               // In the middle of servicing dma request to ICCM. Do not make any new requests.
   output logic                      ic_write_stall,                // Stall fetch the cycle we are writing the cache.

/// PMU signals
   output logic                      ifu_pmu_ic_miss,               // IC miss event
   output logic                      ifu_pmu_ic_hit,                // IC hit event
   output logic                      ifu_pmu_bus_error,             // Bus error event
   output logic                      ifu_pmu_bus_busy,              // Bus busy event
   output logic                      ifu_pmu_bus_trxn,              // Bus transaction

  //-------------------------- IFU AXI signals--------------------------
   // AXI Write Channels
   output logic                            ifu_axi_awvalid,
   output logic [pt.IFU_BUS_TAG-1:0]       ifu_axi_awid,
   output logic [31:0]                     ifu_axi_awaddr,
   output logic [3:0]                      ifu_axi_awregion,
   output logic [7:0]                      ifu_axi_awlen,
   output logic [2:0]                      ifu_axi_awsize,
   output logic [1:0]                      ifu_axi_awburst,
   output logic                            ifu_axi_awlock,
   output logic [3:0]                      ifu_axi_awcache,
   output logic [2:0]                      ifu_axi_awprot,
   output logic [3:0]                      ifu_axi_awqos,

   output logic                            ifu_axi_wvalid,
   output logic [63:0]                     ifu_axi_wdata,
   output logic [7:0]                      ifu_axi_wstrb,
   output logic                            ifu_axi_wlast,

   output logic                            ifu_axi_bready,

   // AXI Read Channels
   output logic                            ifu_axi_arvalid,
   input  logic                            ifu_axi_arready,
   output logic [pt.IFU_BUS_TAG-1:0]       ifu_axi_arid,
   output logic [31:0]                     ifu_axi_araddr,
   output logic [3:0]                      ifu_axi_arregion,
   output logic [7:0]                      ifu_axi_arlen,
   output logic [2:0]                      ifu_axi_arsize,
   output logic [1:0]                      ifu_axi_arburst,
   output logic                            ifu_axi_arlock,
   output logic [3:0]                      ifu_axi_arcache,
   output logic [2:0]                      ifu_axi_arprot,
   output logic [3:0]                      ifu_axi_arqos,

   input  logic                            ifu_axi_rvalid,
   output logic                            ifu_axi_rready,
   input  logic [pt.IFU_BUS_TAG-1:0]       ifu_axi_rid,
   input  logic [63:0]                     ifu_axi_rdata,
   input  logic [1:0]                      ifu_axi_rresp,

    input  logic                     ifu_bus_clk_en,


   input  logic                      dma_iccm_req,      //  dma iccm command (read or write)
   input  logic [31:0]               dma_mem_addr,      //  dma address
   input  logic [2:0]                dma_mem_sz,        //  size
   input  logic                      dma_mem_write,     //  write
   input  logic [63:0]               dma_mem_wdata,     //  write data
   input  logic [2:0]                dma_mem_tag,       //  DMA Buffer entry number

   output logic                      iccm_dma_ecc_error,//   Data read from iccm has an ecc error
   output logic                      iccm_dma_rvalid,   //   Data read from iccm is valid
   output logic [63:0]               iccm_dma_rdata,    //   dma data read from iccm
   output logic [2:0]                iccm_dma_rtag,     //   Tag of the DMA req
   output logic                      iccm_ready,        //   iccm ready to accept new command.


//   I$ & ITAG Ports
   output logic [31:1]               ic_rw_addr,         // Read/Write addresss to the Icache.
   output logic [pt.ICACHE_NUM_WAYS-1:0]                ic_wr_en,           // Icache write enable, when filling the Icache.
   output logic                      ic_rd_en,           // Icache read  enable.

   output logic [pt.ICACHE_BANKS_WAY-1:0] [70:0]               ic_wr_data,           // Data to fill to the Icache. With ECC
   input  logic [63:0]               ic_rd_data ,          // Data read from Icache. 2x64bits + parity bits. F2 stage. With ECC
   input  logic [70:0]               ic_debug_rd_data ,          // Data read from Icache. 2x64bits + parity bits. F2 stage. With ECC
   input  logic [25:0]               ictag_debug_rd_data,  // Debug icache tag.
   output logic [70:0]               ic_debug_wr_data,     // Debug wr cache.
   output logic [70:0]               ifu_ic_debug_rd_data, // debug data read


   input  logic [pt.ICACHE_BANKS_WAY-1:0] ic_eccerr,    //
   input  logic [pt.ICACHE_BANKS_WAY-1:0] ic_parerr,

   output logic [pt.ICACHE_INDEX_HI:3]               ic_debug_addr,      // Read/Write addresss to the Icache.
   output logic                      ic_debug_rd_en,     // Icache debug rd
   output logic                      ic_debug_wr_en,     // Icache debug wr
   output logic                      ic_debug_tag_array, // Debug tag array
   output logic [pt.ICACHE_NUM_WAYS-1:0]                ic_debug_way,       // Debug way. Rd or Wr.


   output logic [pt.ICACHE_NUM_WAYS-1:0]                ic_tag_valid,       // Valid bits when accessing the Icache. One valid bit per way. F2 stage

   input  logic [pt.ICACHE_NUM_WAYS-1:0]                ic_rd_hit,          // Compare hits from Icache tags. Per way.  F2 stage
   input  logic                      ic_tag_perr,        // Icache Tag parity error

   // ICCM ports
   output logic [pt.ICCM_BITS-1:1]  iccm_rw_addr,       // ICCM read/write address.
   output logic                      iccm_wren,          // ICCM write enable (through the DMA)
   output logic                      iccm_rden,          // ICCM read enable.
   output logic [77:0]               iccm_wr_data,       // ICCM write data.
   output logic [2:0]                iccm_wr_size,       // ICCM write location within DW.

   input  logic [63:0]               iccm_rd_data,       // Data read from ICCM.
   input  logic [77:0]               iccm_rd_data_ecc,   // Data + ECC read from ICCM.
   input  logic [1:0]                ifu_fetch_val,
   // IFU control signals
   output logic                      ic_hit_f,               // Hit in Icache(if Icache access) or ICCM access( ICCM always has ic_hit_f)
   output logic [1:0]                ic_access_fault_f,      // Access fault (bus error or ICCM access in region but out of offset range).
   output logic [1:0]                ic_access_fault_type_f, // Access fault types
   output logic                      iccm_rd_ecc_single_err, // This fetch has a single ICCM ecc  error.
   output logic [1:0]                iccm_rd_ecc_double_err, // This fetch has a double ICCM ecc  error.
   output logic                      ic_error_start,         // This has any I$ errors ( data/tag/ecc/parity )

   output logic                      ifu_async_error_start,  // Or of the sb iccm, and all the icache errors sent to aligner to stop
   output logic                      iccm_dma_sb_error,      // Single Bit ECC error from a DMA access
   output logic [1:0]                ic_fetch_val_f,         // valid bytes for fetch. To the Aligner.
   output logic [31:0]               ic_data_f,              // Data read from Icache or ICCM. To the Aligner.
   output logic [63:0]               ic_premux_data,         // Premuxed data to be muxed with Icache data
   output logic                      ic_sel_premux_data,     // Select premux data.

/////  Debug
   input  el2_cache_debug_pkt_t     dec_tlu_ic_diag_pkt ,       // Icache/tag debug read/write packet
   input  logic                      dec_tlu_core_ecc_disable,   // disable the ecc checking and flagging
   output logic                      ifu_ic_debug_rd_data_valid, // debug data valid.
   output logic                      iccm_buf_correct_ecc,
   output logic                      iccm_correction_state,

   input  logic                      ifu_pmp_error,


   input  logic         scan_mode
   );

//  Create different defines for ICACHE and ICCM enable combinations

 localparam   NUM_OF_BEATS = 8 ;



   logic [31:3]    ifu_ic_req_addr_f;
   logic           uncacheable_miss_in ;
   logic           uncacheable_miss_ff;



   logic           bus_ifu_wr_en     ;
   logic           bus_ifu_wr_en_ff  ;
   logic           bus_ifu_wr_en_ff_q  ;
   logic           bus_ifu_wr_en_ff_wo_err  ;
   logic [pt.ICACHE_NUM_WAYS-1:0]     bus_ic_wr_en ;

   logic           reset_tag_valid_for_miss  ;


   logic [pt.ICACHE_STATUS_BITS-1:0]     way_status;
   logic [pt.ICACHE_STATUS_BITS-1:0]     way_status_mb_in;
   logic [pt.ICACHE_STATUS_BITS-1:0]     way_status_rep_new;
   logic [pt.ICACHE_STATUS_BITS-1:0]     way_status_mb_ff;
   logic [pt.ICACHE_STATUS_BITS-1:0]     way_status_new;
   logic [pt.ICACHE_STATUS_BITS-1:0]     way_status_hit_new;
   logic [pt.ICACHE_STATUS_BITS-1:0]     way_status_new_w_debug;
   logic [pt.ICACHE_NUM_WAYS-1:0]     tagv_mb_in;
   logic [pt.ICACHE_NUM_WAYS-1:0]     tagv_mb_ff;


   logic           ifu_wr_data_comb_err ;
   logic           ifu_byp_data_err_new;
   logic  [1:0]    ifu_byp_data_err_f;
   logic           ifu_wr_cumulative_err_data;
   logic           ifu_wr_cumulative_err;
   logic           ifu_wr_data_comb_err_ff;
   logic           scnd_miss_index_match ;


   logic           ifc_dma_access_q_ok;
   logic           ifc_iccm_access_f ;
   logic           ifc_region_acc_fault_f;
   logic           ifc_region_acc_fault_final_f;
   logic  [1:0]    ifc_bus_acc_fault_f;
   logic           ic_act_miss_f;
   logic           ic_miss_under_miss_f;
   logic           ic_ignore_2nd_miss_f;
   logic           ic_act_hit_f;
   logic           miss_pending;
   logic [31:1]    imb_in , imb_ff  ;
   logic [31:pt.ICACHE_BEAT_ADDR_HI+1]    miss_addr_in , miss_addr  ;
   logic           miss_wrap_f ;
   logic           flush_final_f;
   logic           ifc_fetch_req_f;
   logic           ifc_fetch_req_f_raw;
   logic           fetch_req_f_qual   ;
   logic           ifc_fetch_req_qual_bf ;
   logic [pt.ICACHE_NUM_WAYS-1:0]     replace_way_mb_any;
   logic           last_beat;
   logic           reset_beat_cnt  ;
   logic [pt.ICACHE_BEAT_ADDR_HI:3]     ic_req_addr_bits_hi_3 ;
   logic [pt.ICACHE_BEAT_ADDR_HI:3]     ic_wr_addr_bits_hi_3 ;
   logic [31:1]    ifu_fetch_addr_int_f ;
   logic [31:1]    ifu_ic_rw_int_addr ;
   logic           crit_wd_byp_ok_ff ;
   logic           ic_crit_wd_rdy_new_ff;
   logic   [79:0]  ic_byp_data_only_pre_new;
   logic   [79:0]  ic_byp_data_only_new;
   logic           ic_byp_hit_f ;
   logic           ic_valid ;
   logic           ic_valid_ff;
   logic           reset_all_tags;
   logic           ic_valid_w_debug;

   logic [pt.ICACHE_NUM_WAYS-1:0]     ifu_tag_wren,ifu_tag_wren_ff;
   logic [pt.ICACHE_NUM_WAYS-1:0]     ic_debug_tag_wr_en;
   logic [pt.ICACHE_NUM_WAYS-1:0]     ifu_tag_wren_w_debug;
   logic [pt.ICACHE_NUM_WAYS-1:0]     ic_debug_way_ff;
   logic           ic_debug_rd_en_ff   ;
   logic           fetch_bf_f_c1_clken ;
   logic           fetch_bf_f_c1_clk;
   logic           debug_c1_clken;
   logic           debug_c1_clk;

   logic           reset_ic_in ;
   logic           reset_ic_ff ;
   logic [pt.ICACHE_BEAT_ADDR_HI:1]     vaddr_f ;
   logic [31:1]    ifu_status_wr_addr;
   logic           sel_mb_addr ;
   logic           sel_mb_addr_ff ;
   logic           sel_mb_status_addr ;
   logic [63:0]    ic_final_data;

   logic [pt.ICACHE_INDEX_HI:pt.ICACHE_TAG_INDEX_LO] ifu_ic_rw_int_addr_ff ;
   logic [pt.ICACHE_INDEX_HI:pt.ICACHE_TAG_INDEX_LO] ifu_status_wr_addr_ff ;
   logic [pt.ICACHE_INDEX_HI:pt.ICACHE_TAG_INDEX_LO] ifu_ic_rw_int_addr_w_debug ;
   logic [pt.ICACHE_INDEX_HI:pt.ICACHE_TAG_INDEX_LO] ifu_status_wr_addr_w_debug ;

   logic [pt.ICACHE_STATUS_BITS-1:0]                              way_status_new_ff ;
   logic                                    way_status_wr_en_ff ;
   logic [pt.ICACHE_TAG_DEPTH-1:0][pt.ICACHE_STATUS_BITS-1:0]        way_status_out ;
   logic [1:0]                              ic_debug_way_enc;

   logic [pt.IFU_BUS_TAG-1:0]             ifu_bus_rid_ff;

   logic         fetch_req_icache_f;
   logic         fetch_req_iccm_f;
   logic         ic_iccm_hit_f;
   logic         fetch_uncacheable_ff;
   logic         way_status_wr_en;
   logic         sel_byp_data;
   logic         sel_ic_data;
   logic         sel_iccm_data;
   logic         ic_rd_parity_final_err;
   logic         ic_act_miss_f_delayed;
   logic         bus_ifu_wr_data_error;
   logic         bus_ifu_wr_data_error_ff;
   logic         way_status_wr_en_w_debug;
   logic         ic_debug_tag_val_rd_out;
   logic         ifu_pmu_ic_miss_in;
   logic         ifu_pmu_ic_hit_in;
   logic         ifu_pmu_bus_error_in;
   logic         ifu_pmu_bus_trxn_in;
   logic         ifu_pmu_bus_busy_in;
   logic         ic_debug_ict_array_sel_in;
   logic         ic_debug_ict_array_sel_ff;
   logic         debug_data_clken;
   logic         last_data_recieved_in ;
   logic         last_data_recieved_ff ;

   logic                          ifu_bus_rvalid           ;
   logic                          ifu_bus_rvalid_ff        ;
   logic                          ifu_bus_rvalid_unq_ff    ;
   logic                          ifu_bus_arready_unq       ;
   logic                          ifu_bus_arready_unq_ff    ;
   logic                          ifu_bus_arvalid           ;
   logic                          ifu_bus_arvalid_ff        ;
   logic                          ifu_bus_arready           ;
   logic                          ifu_bus_arready_ff        ;
   logic [63:0]                   ifu_bus_rdata_ff        ;
   logic [1:0]                    ifu_bus_rresp_ff          ;
   logic                          ifu_bus_rsp_valid ;
   logic                          ifu_bus_rsp_ready ;
   logic [pt.IFU_BUS_TAG-1:0]     ifu_bus_rsp_tag;
   logic [63:0]                   ifu_bus_rsp_rdata;
   logic [1:0]                    ifu_bus_rsp_opc;

   logic [pt.ICACHE_NUM_BEATS-1:0]    write_fill_data;
   logic [pt.ICACHE_NUM_BEATS-1:0]    wr_data_c1_clk;
   logic [pt.ICACHE_NUM_BEATS-1:0]    ic_miss_buff_data_valid_in;
   logic [pt.ICACHE_NUM_BEATS-1:0]    ic_miss_buff_data_valid;
   logic [pt.ICACHE_NUM_BEATS-1:0]    ic_miss_buff_data_error_in;
   logic [pt.ICACHE_NUM_BEATS-1:0]    ic_miss_buff_data_error;
   logic [pt.ICACHE_BEAT_ADDR_HI:1]    byp_fetch_index;
   logic [pt.ICACHE_BEAT_ADDR_HI:2]    byp_fetch_index_0;
   logic [pt.ICACHE_BEAT_ADDR_HI:2]    byp_fetch_index_1;
   logic [pt.ICACHE_BEAT_ADDR_HI:3]    byp_fetch_index_inc;
   logic [pt.ICACHE_BEAT_ADDR_HI:2]    byp_fetch_index_inc_0;
   logic [pt.ICACHE_BEAT_ADDR_HI:2]    byp_fetch_index_inc_1;
   logic          miss_buff_hit_unq_f ;
   logic          stream_hit_f ;
   logic          stream_miss_f ;
   logic          stream_eol_f ;
   logic          crit_byp_hit_f ;
   logic [pt.IFU_BUS_TAG-1:0] other_tag ;
   logic [(2*pt.ICACHE_NUM_BEATS)-1:0] [31:0] ic_miss_buff_data;
   logic [63:0] ic_miss_buff_half;
   logic        scnd_miss_req, scnd_miss_req_q;
   logic        scnd_miss_req_in;


   logic [pt.ICCM_BITS-1:2]                iccm_ecc_corr_index_ff;
   logic [pt.ICCM_BITS-1:2]                iccm_ecc_corr_index_in;
   logic [38:0]                         iccm_ecc_corr_data_ff;
   logic                                iccm_ecc_write_status     ;
   logic                                iccm_rd_ecc_single_err_ff   ;
   logic                                iccm_error_start;     // start the error fsm
   logic                                perr_state_en;
   logic                                miss_state_en;

   logic        busclk;
   logic        busclk_force;
   logic        busclk_reset;
   logic        bus_ifu_bus_clk_en_ff;
   logic        bus_ifu_bus_clk_en ;

   logic        ifc_bus_ic_req_ff_in;
   logic        ifu_bus_cmd_valid ;
   logic        ifu_bus_cmd_ready ;

   logic        bus_inc_data_beat_cnt     ;
   logic        bus_reset_data_beat_cnt   ;
   logic        bus_hold_data_beat_cnt    ;

   logic        bus_inc_cmd_beat_cnt     ;
   logic        bus_reset_cmd_beat_cnt_0   ;
   logic        bus_reset_cmd_beat_cnt_secondlast   ;
   logic        bus_hold_cmd_beat_cnt    ;

   logic [pt.ICACHE_BEAT_BITS-1:0]  bus_new_data_beat_count  ;
   logic [pt.ICACHE_BEAT_BITS-1:0]  bus_data_beat_count      ;

   logic [pt.ICACHE_BEAT_BITS-1:0]  bus_new_cmd_beat_count  ;
   logic [pt.ICACHE_BEAT_BITS-1:0]  bus_cmd_beat_count      ;


   logic [pt.ICACHE_BEAT_BITS-1:0]  bus_new_rd_addr_count;
   logic [pt.ICACHE_BEAT_BITS-1:0]  bus_rd_addr_count;


   logic        bus_cmd_sent           ;
   logic        bus_last_data_beat     ;


   logic [pt.ICACHE_NUM_WAYS-1:0]       bus_wren            ;

   logic [pt.ICACHE_NUM_WAYS-1:0]       bus_wren_last       ;
   logic [pt.ICACHE_NUM_WAYS-1:0]       wren_reset_miss      ;
   logic        ifc_dma_access_ok_d;
   logic        ifc_dma_access_ok_prev;

   logic   bus_cmd_req_in ;
   logic   bus_cmd_req_hold ;

   logic   second_half_available ;
   logic   write_ic_16_bytes ;

   logic   ifc_region_acc_fault_final_bf;
   logic   ifc_region_acc_fault_memory_bf;
   logic   ifc_region_acc_fault_memory_f;
   logic   ifc_region_acc_okay;

   logic   iccm_correct_ecc;
   logic   dma_sb_err_state, dma_sb_err_state_ff;
   logic   two_byte_instr;

   typedef enum logic [2:0] {IDLE=3'b000, CRIT_BYP_OK=3'b001, HIT_U_MISS=3'b010, MISS_WAIT=3'b011,CRIT_WRD_RDY=3'b100,SCND_MISS=3'b101,STREAM=3'b110 , STALL_SCND_MISS=3'b111} miss_state_t;
   miss_state_t miss_state, miss_nxtstate;

   typedef enum logic [1:0] {ERR_STOP_IDLE=2'b00, ERR_FETCH1=2'b01 , ERR_FETCH2=2'b10 , ERR_STOP_FETCH=2'b11} err_stop_state_t;
   err_stop_state_t err_stop_state, err_stop_nxtstate;
   logic   err_stop_state_en ;
   logic   err_stop_fetch ;

   logic   ic_crit_wd_rdy;         // Critical fetch is ready to be bypassed.

   logic   ifu_bp_hit_taken_q_f;
   logic   ifu_bus_rvalid_unq;
   logic   bus_cmd_beat_en;


// ---- Clock gating section -----
// c1 clock enables


   assign fetch_bf_f_c1_clken  = ifc_fetch_req_bf_raw | ifc_fetch_req_f | miss_pending | exu_flush_final | scnd_miss_req;
   assign debug_c1_clken       = ic_debug_rd_en | ic_debug_wr_en ;
   // C1 - 1 clock pulse for data
`ifdef RV_FPGA_OPTIMIZE
   assign fetch_bf_f_c1_clk = 1'b0;
   assign debug_c1_clk      = 1'b0;
`else
   rvclkhdr fetch_bf_f_c1_cgc    ( .en(fetch_bf_f_c1_clken),     .l1clk(fetch_bf_f_c1_clk), .* );
   rvclkhdr debug_c1_cgc         ( .en(debug_c1_clken),          .l1clk(debug_c1_clk), .* );
`endif


// ------ end clock gating section ------------------------

   logic [1:0]    iccm_single_ecc_error;
   logic          dma_iccm_req_f ;
   assign iccm_dma_sb_error     = (|iccm_single_ecc_error[1:0] )  & dma_iccm_req_f ;
   assign ifu_async_error_start = iccm_rd_ecc_single_err | ic_error_start;


   typedef enum logic [2:0] {ERR_IDLE=3'b000, IC_WFF=3'b001 , ECC_WFF=3'b010 , ECC_CORR=3'b011, DMA_SB_ERR=3'b100} perr_state_t;
   perr_state_t perr_state, perr_nxtstate;


   assign ic_dma_active = iccm_correct_ecc | (perr_state == DMA_SB_ERR) | (err_stop_state == ERR_STOP_FETCH) | err_stop_fetch |
                          dec_tlu_flush_err_wb; // The last term is to give a error-correction a chance to finish before refetch starts

   assign scnd_miss_req_in     = ifu_bus_rsp_valid & bus_ifu_bus_clk_en & ifu_bus_rsp_ready &
                                 (&bus_new_data_beat_count[pt.ICACHE_BEAT_BITS-1:0]) &
                                 ~uncacheable_miss_ff &  ((miss_state == SCND_MISS) | (miss_nxtstate == SCND_MISS)) & ~exu_flush_final;

   assign ifu_bp_hit_taken_q_f = ifu_bp_hit_taken_f & ic_hit_f ;

   //////////////////////////////////// Create Miss State Machine ///////////////////////
   //                                   Create Miss State Machine                      //
   //                                   Create Miss State Machine                      //
   //                                   Create Miss State Machine                      //
   //////////////////////////////////// Create Miss State Machine ///////////////////////
   // FIFO state machine
   always_comb begin : MISS_SM
      miss_nxtstate   = IDLE;
      miss_state_en   = 1'b0;
      case (miss_state)
         IDLE: begin : idle
                  miss_nxtstate = (ic_act_miss_f & ~exu_flush_final) ? CRIT_BYP_OK : HIT_U_MISS ;
                  miss_state_en = ic_act_miss_f & ~dec_tlu_force_halt ;
         end
         CRIT_BYP_OK: begin : crit_byp_ok
                  miss_nxtstate =  (dec_tlu_force_halt ) ?                                                                             IDLE :
                                  ( ic_byp_hit_f &  (last_data_recieved_ff | (bus_ifu_wr_en_ff & last_beat)) &  uncacheable_miss_ff) ? IDLE :
                                  ( ic_byp_hit_f &  ~last_data_recieved_ff                                &  uncacheable_miss_ff) ? MISS_WAIT :
                                  (~ic_byp_hit_f &  ~exu_flush_final &  (bus_ifu_wr_en_ff & last_beat)       &  uncacheable_miss_ff) ? CRIT_WRD_RDY :
                                  (                                      (bus_ifu_wr_en_ff & last_beat)       & ~uncacheable_miss_ff) ? IDLE :
                                  ( ic_byp_hit_f  &  ~exu_flush_final & ~(bus_ifu_wr_en_ff & last_beat)       & ~ifu_bp_hit_taken_q_f   & ~uncacheable_miss_ff) ? STREAM :
                                  ( bus_ifu_wr_en_ff &  ~exu_flush_final & ~(bus_ifu_wr_en_ff & last_beat)       & ~ifu_bp_hit_taken_q_f   & ~uncacheable_miss_ff) ? STREAM :
                                  (~ic_byp_hit_f  &  ~exu_flush_final &  (bus_ifu_wr_en_ff & last_beat)       & ~uncacheable_miss_ff) ? IDLE :
                                  ( (exu_flush_final | ifu_bp_hit_taken_q_f)  & ~(bus_ifu_wr_en_ff & last_beat)                      ) ? HIT_U_MISS : IDLE;
                  miss_state_en =  dec_tlu_force_halt | exu_flush_final | ic_byp_hit_f | ifu_bp_hit_taken_q_f | (bus_ifu_wr_en_ff & last_beat) | (bus_ifu_wr_en_ff & ~uncacheable_miss_ff)  ;
         end
         CRIT_WRD_RDY: begin : crit_wrd_rdy
                  miss_nxtstate =  IDLE ;
                  miss_state_en =  exu_flush_final | flush_final_f | ic_byp_hit_f | dec_tlu_force_halt  ;
         end
         STREAM: begin : stream
                  miss_nxtstate =  ((exu_flush_final | ifu_bp_hit_taken_q_f  | stream_eol_f ) & ~(bus_ifu_wr_en_ff & last_beat) & ~dec_tlu_force_halt) ? HIT_U_MISS  : IDLE ;
                  miss_state_en =    exu_flush_final | ifu_bp_hit_taken_q_f  | stream_eol_f   |  (bus_ifu_wr_en_ff & last_beat) | dec_tlu_force_halt ;
         end
         MISS_WAIT: begin : miss_wait
                  miss_nxtstate =  (exu_flush_final & ~(bus_ifu_wr_en_ff & last_beat) & ~dec_tlu_force_halt) ? HIT_U_MISS  : IDLE ;
                  miss_state_en =   exu_flush_final | (bus_ifu_wr_en_ff & last_beat) | dec_tlu_force_halt ;
         end
         HIT_U_MISS: begin : hit_u_miss
                  miss_nxtstate =  ic_miss_under_miss_f & ~(bus_ifu_wr_en_ff & last_beat) & ~dec_tlu_force_halt ? SCND_MISS :
                                   ic_ignore_2nd_miss_f & ~(bus_ifu_wr_en_ff & last_beat) & ~dec_tlu_force_halt ? STALL_SCND_MISS : IDLE  ;
                  miss_state_en = (bus_ifu_wr_en_ff & last_beat) | ic_miss_under_miss_f | ic_ignore_2nd_miss_f | dec_tlu_force_halt;
         end
         SCND_MISS: begin : scnd_miss
                  miss_nxtstate   = dec_tlu_force_halt ? IDLE  :
                                    exu_flush_final ?  ((bus_ifu_wr_en_ff & last_beat) ? IDLE : HIT_U_MISS) : CRIT_BYP_OK;
                  miss_state_en   = (bus_ifu_wr_en_ff & last_beat) | exu_flush_final | dec_tlu_force_halt;
         end
         STALL_SCND_MISS: begin : stall_scnd_miss
                  miss_nxtstate   =  dec_tlu_force_halt ? IDLE  :
                                     exu_flush_final ?  ((bus_ifu_wr_en_ff & last_beat) ? IDLE : HIT_U_MISS) : IDLE;
                  miss_state_en   = (bus_ifu_wr_en_ff & last_beat) | exu_flush_final | dec_tlu_force_halt;
         end
         default: begin : def_case
                  miss_nxtstate   = IDLE;
                  miss_state_en   = 1'b0;
         end
      endcase
   end
   rvdffs #(($bits(miss_state_t))) miss_state_ff (.clk(active_clk), .din(miss_nxtstate), .dout({miss_state}), .en(miss_state_en),   .*);

  logic    sel_hold_imb     ;

   assign miss_pending       =  (miss_state != IDLE) ;
   assign crit_wd_byp_ok_ff  =  (miss_state == CRIT_BYP_OK) | ((miss_state == CRIT_WRD_RDY) & ~flush_final_f);
   assign sel_hold_imb       =  (miss_pending & ~(bus_ifu_wr_en_ff & last_beat) & ~((miss_state == CRIT_WRD_RDY) & exu_flush_final) &
                              ~((miss_state == CRIT_WRD_RDY) & crit_byp_hit_f) ) | ic_act_miss_f |
                                (miss_pending & (miss_nxtstate == CRIT_WRD_RDY)) ;


   logic         sel_hold_imb_scnd;
   logic  [31:1] imb_scnd_in;
   logic  [31:1] imb_scnd_ff;
   logic         uncacheable_miss_scnd_in ;
   logic         uncacheable_miss_scnd_ff ;

   logic  [pt.ICACHE_NUM_WAYS-1:0] tagv_mb_scnd_in;
   logic  [pt.ICACHE_NUM_WAYS-1:0] tagv_mb_scnd_ff;

   logic  [pt.ICACHE_STATUS_BITS-1:0] way_status_mb_scnd_in;
   logic  [pt.ICACHE_STATUS_BITS-1:0] way_status_mb_scnd_ff;

   assign sel_hold_imb_scnd                                =((miss_state == SCND_MISS) | ic_miss_under_miss_f) & ~flush_final_f ;
   assign way_status_mb_scnd_in[pt.ICACHE_STATUS_BITS-1:0] = (miss_state == SCND_MISS) ? way_status_mb_scnd_ff[pt.ICACHE_STATUS_BITS-1:0] : {way_status[pt.ICACHE_STATUS_BITS-1:0]} ;
   assign tagv_mb_scnd_in[pt.ICACHE_NUM_WAYS-1:0]          = (miss_state == SCND_MISS) ? tagv_mb_scnd_ff[pt.ICACHE_NUM_WAYS-1:0]          : ({ic_tag_valid[pt.ICACHE_NUM_WAYS-1:0]} & {pt.ICACHE_NUM_WAYS{~reset_all_tags & ~exu_flush_final}});
   assign uncacheable_miss_scnd_in   = sel_hold_imb_scnd ? uncacheable_miss_scnd_ff : ifc_fetch_uncacheable_bf ;


   rvdff_fpga #(1)  unc_miss_scnd_ff    (.*, .clk(fetch_bf_f_c1_clk), .clken(fetch_bf_f_c1_clken), .rawclk(clk), .din (uncacheable_miss_scnd_in), .dout(uncacheable_miss_scnd_ff));
   rvdffpcie #(31) imb_f_scnd_ff       (.*, .en(fetch_bf_f_c1_clken),  .din ({imb_scnd_in[31:1]}), .dout({imb_scnd_ff[31:1]}));
   rvdff_fpga #(pt.ICACHE_STATUS_BITS)  mb_rep_wayf2_scnd_ff (.*, .clk(fetch_bf_f_c1_clk), .clken(fetch_bf_f_c1_clken), .rawclk(clk), .din ({way_status_mb_scnd_in[pt.ICACHE_STATUS_BITS-1:0]}), .dout({way_status_mb_scnd_ff[pt.ICACHE_STATUS_BITS-1:0]}));
   rvdff_fpga #(pt.ICACHE_NUM_WAYS)     mb_tagv_scnd_ff      (.*, .clk(fetch_bf_f_c1_clk), .clken(fetch_bf_f_c1_clken), .rawclk(clk), .din ({tagv_mb_scnd_in[pt.ICACHE_NUM_WAYS-1:0]}), .dout({tagv_mb_scnd_ff[pt.ICACHE_NUM_WAYS-1:0]}));




   assign ic_req_addr_bits_hi_3[pt.ICACHE_BEAT_ADDR_HI:3] = bus_rd_addr_count[pt.ICACHE_BEAT_BITS-1:0] ;
   assign ic_wr_addr_bits_hi_3[pt.ICACHE_BEAT_ADDR_HI:3]  = ifu_bus_rid_ff[pt.ICACHE_BEAT_BITS-1:0] & {pt.ICACHE_BEAT_BITS{bus_ifu_wr_en_ff}};
   // NOTE: Cacheline size is 16 bytes in this example.
   // Tag     Index  Bank Offset
   // [31:16] [15:5] [4]  [3:0]


   assign fetch_req_icache_f   = ifc_fetch_req_f & ~ifc_iccm_access_f & ~ifc_region_acc_fault_final_f;
   assign fetch_req_iccm_f     = ifc_fetch_req_f &  ifc_iccm_access_f;

   assign ic_iccm_hit_f        = fetch_req_iccm_f  &  (~miss_pending | (miss_state==HIT_U_MISS) | (miss_state==STREAM));
   assign ic_byp_hit_f         = (crit_byp_hit_f | stream_hit_f)  & fetch_req_icache_f &  miss_pending ;
   assign ic_act_hit_f         = (|ic_rd_hit[pt.ICACHE_NUM_WAYS-1:0]) & fetch_req_icache_f & ~reset_all_tags & (~miss_pending | (miss_state==HIT_U_MISS)) & ~sel_mb_addr_ff;
   assign ic_act_miss_f        = (((~(|ic_rd_hit[pt.ICACHE_NUM_WAYS-1:0]) | reset_all_tags) & fetch_req_icache_f & ~miss_pending) | scnd_miss_req) & ~ifc_region_acc_fault_final_f;
   assign ic_miss_under_miss_f = (~(|ic_rd_hit[pt.ICACHE_NUM_WAYS-1:0]) | reset_all_tags) & fetch_req_icache_f & (miss_state == HIT_U_MISS) &
                                   (imb_ff[31:pt.ICACHE_TAG_INDEX_LO] != ifu_fetch_addr_int_f[31:pt.ICACHE_TAG_INDEX_LO]) & ~uncacheable_miss_ff & ~sel_mb_addr_ff & ~ifc_region_acc_fault_final_f;
   assign ic_ignore_2nd_miss_f = (~(|ic_rd_hit[pt.ICACHE_NUM_WAYS-1:0]) | reset_all_tags) & fetch_req_icache_f & (miss_state == HIT_U_MISS) &
                                   ((imb_ff[31:pt.ICACHE_TAG_INDEX_LO] == ifu_fetch_addr_int_f[31:pt.ICACHE_TAG_INDEX_LO])  |   uncacheable_miss_ff) ;
   assign ic_hit_f             =  ic_act_hit_f | ic_byp_hit_f | ic_iccm_hit_f | (ifc_region_acc_fault_final_f & ifc_fetch_req_f);

   assign uncacheable_miss_in   = scnd_miss_req ? uncacheable_miss_scnd_ff : sel_hold_imb ? uncacheable_miss_ff : ifc_fetch_uncacheable_bf ;
   assign imb_in[31:1]          = scnd_miss_req ? imb_scnd_ff[31:1]        : sel_hold_imb ? imb_ff[31:1] : {ifc_fetch_addr_bf[31:1]} ;

   assign imb_scnd_in[31:1]     = sel_hold_imb_scnd ? imb_scnd_ff[31:1] : {ifc_fetch_addr_bf[31:1]} ;

   assign scnd_miss_index_match  =  (imb_ff[pt.ICACHE_INDEX_HI:pt.ICACHE_TAG_INDEX_LO] == imb_scnd_ff[pt.ICACHE_INDEX_HI:pt.ICACHE_TAG_INDEX_LO]) & scnd_miss_req & ~ifu_wr_cumulative_err_data;
   assign way_status_mb_in[pt.ICACHE_STATUS_BITS-1:0] = (scnd_miss_req & ~scnd_miss_index_match) ? way_status_mb_scnd_ff[pt.ICACHE_STATUS_BITS-1:0] :
                                                        (scnd_miss_req &  scnd_miss_index_match) ? way_status_rep_new[pt.ICACHE_STATUS_BITS-1:0] :
                                                         miss_pending                            ? way_status_mb_ff[pt.ICACHE_STATUS_BITS-1:0] :
                                                                                                  {way_status[pt.ICACHE_STATUS_BITS-1:0]} ;
   assign tagv_mb_in[pt.ICACHE_NUM_WAYS-1:0]          = scnd_miss_req ? (tagv_mb_scnd_ff[pt.ICACHE_NUM_WAYS-1:0] | ({pt.ICACHE_NUM_WAYS {scnd_miss_index_match}} & replace_way_mb_any[pt.ICACHE_NUM_WAYS-1:0])) :
                                                         miss_pending ? tagv_mb_ff[pt.ICACHE_NUM_WAYS-1:0]  : ({ic_tag_valid[pt.ICACHE_NUM_WAYS-1:0]} & {pt.ICACHE_NUM_WAYS{~reset_all_tags & ~exu_flush_final}}) ;

   assign reset_ic_in           = miss_pending & ~scnd_miss_req_q &  (reset_all_tags |  reset_ic_ff) ;



   rvdffpcie #(31) ifu_fetch_addr_f_ff (.*, .en(fetch_bf_f_c1_clken), .din ({ifc_fetch_addr_bf[31:1]}), .dout({ifu_fetch_addr_int_f[31:1]}));

   assign vaddr_f[pt.ICACHE_BEAT_ADDR_HI:1] = ifu_fetch_addr_int_f[pt.ICACHE_BEAT_ADDR_HI:1] ;

   rvdffpcie #(31) imb_f_ff        (.*, .en(fetch_bf_f_c1_clken), .din (imb_in[31:1]), .dout(imb_ff[31:1]));
   rvdff_fpga #(1) unc_miss_ff     (.*, .clk(fetch_bf_f_c1_clk), .clken(fetch_bf_f_c1_clken), .rawclk(clk),  .din ( uncacheable_miss_in),               .dout( uncacheable_miss_ff));


   assign miss_addr_in[31:pt.ICACHE_BEAT_ADDR_HI+1]      = (~miss_pending                    ) ? imb_ff[31:pt.ICACHE_BEAT_ADDR_HI+1] :
                                                           (                scnd_miss_req_q  ) ? imb_scnd_ff[31:pt.ICACHE_BEAT_ADDR_HI+1] : miss_addr[31:pt.ICACHE_BEAT_ADDR_HI+1] ;


   rvdfflie #(.WIDTH(31-pt.ICACHE_BEAT_ADDR_HI),.LEFT(31-pt.ICACHE_BEAT_ADDR_HI-8)) miss_f_ff       (.*, .en(bus_ifu_bus_clk_en | ic_act_miss_f | dec_tlu_force_halt), .din ({miss_addr_in[31:pt.ICACHE_BEAT_ADDR_HI+1]}), .dout({miss_addr[31:pt.ICACHE_BEAT_ADDR_HI+1]}));





   rvdff_fpga #(pt.ICACHE_STATUS_BITS)  mb_rep_wayf2_ff (.*, .clk(fetch_bf_f_c1_clk),  .clken(fetch_bf_f_c1_clken), .rawclk(clk),  .din ({way_status_mb_in[pt.ICACHE_STATUS_BITS-1:0]}), .dout({way_status_mb_ff[pt.ICACHE_STATUS_BITS-1:0]}));
   rvdff_fpga #(pt.ICACHE_NUM_WAYS)     mb_tagv_ff      (.*, .clk(fetch_bf_f_c1_clk),  .clken(fetch_bf_f_c1_clken), .rawclk(clk),  .din ({tagv_mb_in[pt.ICACHE_NUM_WAYS-1:0]}), .dout({tagv_mb_ff[pt.ICACHE_NUM_WAYS-1:0]}));

   assign ifc_fetch_req_qual_bf  = ifc_fetch_req_bf  & ~((miss_state == CRIT_WRD_RDY) & flush_final_f) & ~stream_miss_f ;// & ~exu_flush_final ;

   assign ifc_fetch_req_f       = ifc_fetch_req_f_raw & ~exu_flush_final ;

   rvdff_fpga #(1) ifu_iccm_acc_ff     (.*, .clk(fetch_bf_f_c1_clk), .clken(fetch_bf_f_c1_clken), .rawclk(clk),   .din(ifc_iccm_access_bf),      .dout(ifc_iccm_access_f));
   rvdff_fpga #(1) ifu_iccm_reg_acc_ff (.*, .clk(fetch_bf_f_c1_clk), .clken(fetch_bf_f_c1_clken), .rawclk(clk),   .din(ifc_region_acc_fault_final_bf), .dout(ifc_region_acc_fault_final_f));
   rvdff_fpga #(1) rgn_acc_ff          (.*, .clk(fetch_bf_f_c1_clk), .clken(fetch_bf_f_c1_clken), .rawclk(clk),   .din(ifc_region_acc_fault_bf),       .dout(ifc_region_acc_fault_f));


   assign ifu_ic_req_addr_f[31:3]  = {miss_addr[31:pt.ICACHE_BEAT_ADDR_HI+1] , ic_req_addr_bits_hi_3[pt.ICACHE_BEAT_ADDR_HI:3] };
   assign ifu_ic_mb_empty          = (((miss_state == HIT_U_MISS) | (miss_state == STREAM)) & ~(bus_ifu_wr_en_ff & last_beat)) |  ~miss_pending ;
   assign ifu_miss_state_idle      = (miss_state == IDLE) ;


   assign sel_mb_addr  = ((miss_pending & write_ic_16_bytes & ~uncacheable_miss_ff) | reset_tag_valid_for_miss) ;
   assign ifu_ic_rw_int_addr[31:1] = ({31{ sel_mb_addr}}  &  {imb_ff[31:pt.ICACHE_BEAT_ADDR_HI+1] , ic_wr_addr_bits_hi_3[pt.ICACHE_BEAT_ADDR_HI:3] , imb_ff[2:1]})  |
                                     ({31{~sel_mb_addr}}  &  ifc_fetch_addr_bf[31:1] )   ;

   assign sel_mb_status_addr  = ((miss_pending & write_ic_16_bytes & ~uncacheable_miss_ff & last_beat & bus_ifu_wr_en_ff_q) | reset_tag_valid_for_miss) ;
   assign ifu_status_wr_addr[31:1] = ({31{ sel_mb_status_addr}}  &  {imb_ff[31:pt.ICACHE_BEAT_ADDR_HI+1] , ic_wr_addr_bits_hi_3[pt.ICACHE_BEAT_ADDR_HI:3] , imb_ff[2:1]})  |
                                     ({31{~sel_mb_status_addr}}  &  ifu_fetch_addr_int_f[31:1] )   ;


  assign ic_rw_addr[31:1]      = ifu_ic_rw_int_addr[31:1] ;


if (pt.ICACHE_ECC == 1) begin: icache_ecc_1
   logic [6:0]       ic_wr_ecc;
   logic [6:0]       ic_miss_buff_ecc;
   logic [141:0]     ic_wr_16bytes_data ;
   logic [70:0]      ifu_ic_debug_rd_data_in   ;

                rvecc_encode_64  ic_ecc_encode_64_bus (
                           .din    (ifu_bus_rdata_ff[63:0]),
                           .ecc_out(ic_wr_ecc[6:0]));
                rvecc_encode_64  ic_ecc_encode_64_buff (
                           .din    (ic_miss_buff_half[63:0]),
                           .ecc_out(ic_miss_buff_ecc[6:0]));

   for (genvar i=0; i < pt.ICACHE_BANKS_WAY ; i++) begin : ic_wr_data_loop
      assign ic_wr_data[i][70:0]  =  ic_wr_16bytes_data[((71*i)+70): (71*i)];
   end


   assign ic_debug_wr_data[70:0]   = {dec_tlu_ic_diag_pkt.icache_wrdata[70:0]} ;
   assign ic_error_start           = ((|ic_eccerr[pt.ICACHE_BANKS_WAY-1:0]) & ic_act_hit_f)  | ic_rd_parity_final_err;



  assign ifu_ic_debug_rd_data_in[70:0] = ic_debug_ict_array_sel_ff ? {2'b0,ictag_debug_rd_data[25:21],32'b0,ictag_debug_rd_data[20:0],{7-pt.ICACHE_STATUS_BITS{1'b0}}, way_status[pt.ICACHE_STATUS_BITS-1:0],3'b0,ic_debug_tag_val_rd_out} :
                                                                     ic_debug_rd_data[70:0];

  rvdffe #(71) ifu_debug_data_ff (.*,
                                  .en (debug_data_clken),
                                  .din ({
                                         ifu_ic_debug_rd_data_in[70:0]
                                         }),
                                  .dout({
                                         ifu_ic_debug_rd_data[70:0]
                                         })
                                  );

  assign ic_wr_16bytes_data[141:0] =  ifu_bus_rid_ff[0] ? {ic_wr_ecc[6:0] , ifu_bus_rdata_ff[63:0] ,  ic_miss_buff_ecc[6:0] , ic_miss_buff_half[63:0] } :
                                                        {ic_miss_buff_ecc[6:0] ,  ic_miss_buff_half[63:0] , ic_wr_ecc[6:0] , ifu_bus_rdata_ff[63:0] } ;


end
else begin : icache_parity_1
   logic [3:0]   ic_wr_parity;
   logic [3:0]   ic_miss_buff_parity;
   logic [135:0] ic_wr_16bytes_data ;
   logic [70:0]  ifu_ic_debug_rd_data_in   ;
    for (genvar i=0 ; i < 4 ; i++) begin : DATA_PGEN
       rveven_paritygen #(16) par_bus  (.data_in   (ifu_bus_rdata_ff[((16*i)+15):(16*i)]),
                                      .parity_out(ic_wr_parity[i]));
       rveven_paritygen #(16) par_buff  (.data_in   (ic_miss_buff_half[((16*i)+15):(16*i)]),
                                      .parity_out(ic_miss_buff_parity[i]));
    end


   for (genvar i=0; i < pt.ICACHE_BANKS_WAY ; i++) begin : ic_wr_data_loop
      assign ic_wr_data[i][70:0]  =  {3'b0, ic_wr_16bytes_data[((68*i)+67): (68*i)]};
   end





   assign ic_debug_wr_data[70:0]   = {dec_tlu_ic_diag_pkt.icache_wrdata[70:0]} ;
   assign ic_error_start           = ((|ic_parerr[pt.ICACHE_BANKS_WAY-1:0]) & ic_act_hit_f) | ic_rd_parity_final_err;

   assign ifu_ic_debug_rd_data_in[70:0] = ic_debug_ict_array_sel_ff ? {6'b0,ictag_debug_rd_data[21],32'b0,ictag_debug_rd_data[20:0],{7-pt.ICACHE_STATUS_BITS{1'b0}},way_status[pt.ICACHE_STATUS_BITS-1:0],3'b0,ic_debug_tag_val_rd_out} :
                                                                      ic_debug_rd_data[70:0] ;

   rvdffe #(71) ifu_debug_data_ff (.*,
                                   .en (debug_data_clken),
                                   .din ({
                                          ifu_ic_debug_rd_data_in[70:0]
                                          }),
                                   .dout({
                                          ifu_ic_debug_rd_data[70:0]
                                          })
                                   );

   assign ic_wr_16bytes_data[135:0] =  ifu_bus_rid_ff[0] ? {ic_wr_parity[3:0] , ifu_bus_rdata_ff[63:0] ,  ic_miss_buff_parity[3:0] , ic_miss_buff_half[63:0] } :
                                                        {ic_miss_buff_parity[3:0] ,  ic_miss_buff_half[63:0] , ic_wr_parity[3:0] , ifu_bus_rdata_ff[63:0] } ;

end


  assign ifu_wr_data_comb_err       =  bus_ifu_wr_data_error_ff ;
  assign ifu_wr_cumulative_err      = (ifu_wr_data_comb_err | ifu_wr_data_comb_err_ff) & ~reset_beat_cnt;
  assign ifu_wr_cumulative_err_data =  ifu_wr_data_comb_err | ifu_wr_data_comb_err_ff ;


  assign sel_byp_data     =  (ic_crit_wd_rdy | (miss_state == STREAM) | (miss_state == CRIT_BYP_OK));
  assign sel_ic_data      = ~(ic_crit_wd_rdy | (miss_state == STREAM) | (miss_state == CRIT_BYP_OK) | (miss_state == MISS_WAIT)) & ~fetch_req_iccm_f & ~ifc_region_acc_fault_final_f;

 if (pt.ICCM_ICACHE==1) begin: iccm_icache
  assign sel_iccm_data    =  fetch_req_iccm_f  ;

  assign ic_final_data[63:0]  = ({64{sel_byp_data | sel_iccm_data | sel_ic_data}} & {ic_rd_data[63:0]} ) ;

  assign ic_premux_data[63:0] = ({64{sel_byp_data }} & {ic_byp_data_only_new[63:0]} ) |
                          ({64{sel_iccm_data}} & {iccm_rd_data[63:0]});

  assign ic_sel_premux_data = sel_iccm_data | sel_byp_data ;
 end

if (pt.ICCM_ONLY == 1 ) begin: iccm_only
  assign sel_iccm_data    =  fetch_req_iccm_f  ;
  assign ic_final_data[63:0]  = ({64{sel_byp_data }} & {ic_byp_data_only_new[63:0]} ) |
                          ({64{sel_iccm_data}} & {iccm_rd_data[63:0]});
  assign ic_premux_data = '0 ;
  assign ic_sel_premux_data = '0 ;
end

if (pt.ICACHE_ONLY == 1 ) begin: icache_only
  assign ic_final_data[63:0]  = ({64{sel_byp_data | sel_ic_data}} & {ic_rd_data[63:0]} ) ;
  assign ic_premux_data[63:0] = ({64{sel_byp_data }} & {ic_byp_data_only_new[63:0]} ) ;
  assign ic_sel_premux_data =  sel_byp_data ;
end


if (pt.NO_ICCM_NO_ICACHE == 1 ) begin: no_iccm_no_icache
  assign ic_final_data[63:0]  = ({64{sel_byp_data }} & {ic_byp_data_only_new[63:0]} ) ;
  assign ic_premux_data = 0 ;
  assign ic_sel_premux_data = '0 ;
end


  assign ifc_bus_acc_fault_f[1:0]   =  {2{ic_byp_hit_f}} & ifu_byp_data_err_f[1:0] ;
  assign ic_data_f[31:0]      = ic_final_data[31:0];



assign fetch_req_f_qual       = ic_hit_f & ~exu_flush_final;
assign ic_access_fault_f[1:0]  = ({2{ifc_region_acc_fault_final_f}} | ifc_bus_acc_fault_f[1:0])  & {2{~exu_flush_final}};
assign ic_access_fault_type_f[1:0] = |iccm_rd_ecc_double_err       ? 2'b01 :
                                     ifc_region_acc_fault_f        ? 2'b10 :
                                     ifc_region_acc_fault_memory_f ? 2'b11 :  2'b00 ;

  // right justified

assign ic_fetch_val_f[1] = fetch_req_f_qual & ifu_bp_inst_mask_f & ~(vaddr_f[pt.ICACHE_BEAT_ADDR_HI:1] == {pt.ICACHE_BEAT_ADDR_HI{1'b1}}) & (err_stop_state != ERR_FETCH2);
assign ic_fetch_val_f[0] = fetch_req_f_qual ;
assign two_byte_instr    =  (ic_data_f[1:0] != 2'b11 )  ;

/////////////////////////////////////////////////////////////////////////////////////
//  Create full buffer...                                                          //
/////////////////////////////////////////////////////////////////////////////////////
     logic [63:0]       ic_miss_buff_data_in;
     assign ic_miss_buff_data_in[63:0] = ifu_bus_rsp_rdata[63:0];

     for (genvar i=0; i<pt.ICACHE_NUM_BEATS; i++) begin :  wr_flop

        assign write_fill_data[i]        =   bus_ifu_wr_en & (  (pt.IFU_BUS_TAG)'(i)  == ifu_bus_rsp_tag[pt.IFU_BUS_TAG-1:0]);

        rvdffe #(32) byp_data_0_ff (.*,
                                    .en (write_fill_data[i]),
                                    .din (ic_miss_buff_data_in[31:0]),
                                    .dout(ic_miss_buff_data[i*2][31:0])
                                    );

        rvdffe #(32) byp_data_1_ff (.*,
                                    .en (write_fill_data[i]),
                                    .din (ic_miss_buff_data_in[63:32]),
                                    .dout(ic_miss_buff_data[i*2+1][31:0])
                                    );

        assign ic_miss_buff_data_valid_in[i]  = write_fill_data[i] ? 1'b1  : (ic_miss_buff_data_valid[i]  & ~ic_act_miss_f) ;

        rvdff #(1) byp_data_valid_ff (.*,
                  .clk (active_clk),
                  .din (ic_miss_buff_data_valid_in[i]),
                  .dout(ic_miss_buff_data_valid[i]));

        assign ic_miss_buff_data_error_in[i]  = write_fill_data[i] ? bus_ifu_wr_data_error  : (ic_miss_buff_data_error[i]  & ~ic_act_miss_f) ;

        rvdff #(1) byp_data_error_ff (.*,
                  .clk (active_clk),
                  .din (ic_miss_buff_data_error_in[i] ),
                  .dout(ic_miss_buff_data_error[i]));
     end

/////////////////////////////////////////////////////////////////////////////////////
// New bypass ready                                                                //
/////////////////////////////////////////////////////////////////////////////////////
   logic   [pt.ICACHE_BEAT_ADDR_HI:1]  bypass_index;
   logic   [pt.ICACHE_BEAT_ADDR_HI:3]  bypass_index_5_3_inc;
   logic   bypass_data_ready_in;
   logic   ic_crit_wd_rdy_new_in;

   assign bypass_index[pt.ICACHE_BEAT_ADDR_HI:1] = imb_ff[pt.ICACHE_BEAT_ADDR_HI:1] ;
   assign bypass_index_5_3_inc[pt.ICACHE_BEAT_ADDR_HI:3] = bypass_index[pt.ICACHE_BEAT_ADDR_HI:3] + 1 ;


   assign bypass_data_ready_in = ((ic_miss_buff_data_valid_in[bypass_index[pt.ICACHE_BEAT_ADDR_HI:3]]                                                      & ~bypass_index[2] & ~bypass_index[1])) |
                                 ((ic_miss_buff_data_valid_in[bypass_index[pt.ICACHE_BEAT_ADDR_HI:3]]                                                      & ~bypass_index[2] &  bypass_index[1])) |
                                 ((ic_miss_buff_data_valid_in[bypass_index[pt.ICACHE_BEAT_ADDR_HI:3]]                                                      &  bypass_index[2] & ~bypass_index[1])) |
                                 ((ic_miss_buff_data_valid_in[bypass_index[pt.ICACHE_BEAT_ADDR_HI:3]] & ic_miss_buff_data_valid_in[bypass_index_5_3_inc[pt.ICACHE_BEAT_ADDR_HI:3]] &  bypass_index[2] & bypass_index[1])) |
                                 ((ic_miss_buff_data_valid_in[bypass_index[pt.ICACHE_BEAT_ADDR_HI:3]] & (bypass_index[pt.ICACHE_BEAT_ADDR_HI:3] == {pt.ICACHE_BEAT_ADDR_HI{1'b1}})))   ;



   assign    ic_crit_wd_rdy_new_in = ( bypass_data_ready_in & crit_wd_byp_ok_ff   &  uncacheable_miss_ff &  ~exu_flush_final & ~ifu_bp_hit_taken_q_f) |
                                     (                        crit_wd_byp_ok_ff   & ~uncacheable_miss_ff &  ~exu_flush_final & ~ifu_bp_hit_taken_q_f) |
                                     (ic_crit_wd_rdy_new_ff & ~fetch_req_icache_f & crit_wd_byp_ok_ff    &  ~exu_flush_final) ;


  assign byp_fetch_index[pt.ICACHE_BEAT_ADDR_HI:1]          =    ifu_fetch_addr_int_f[pt.ICACHE_BEAT_ADDR_HI:1]       ;
  assign byp_fetch_index_0[pt.ICACHE_BEAT_ADDR_HI:2]        =   {ifu_fetch_addr_int_f[pt.ICACHE_BEAT_ADDR_HI:3],1'b0} ;
  assign byp_fetch_index_1[pt.ICACHE_BEAT_ADDR_HI:2]        =   {ifu_fetch_addr_int_f[pt.ICACHE_BEAT_ADDR_HI:3],1'b1} ;
  assign byp_fetch_index_inc[pt.ICACHE_BEAT_ADDR_HI:3]      =    ifu_fetch_addr_int_f[pt.ICACHE_BEAT_ADDR_HI:3]+1'b1 ;
  assign byp_fetch_index_inc_0[pt.ICACHE_BEAT_ADDR_HI:2]    =   {byp_fetch_index_inc[pt.ICACHE_BEAT_ADDR_HI:3], 1'b0} ;
  assign byp_fetch_index_inc_1[pt.ICACHE_BEAT_ADDR_HI:2]    =   {byp_fetch_index_inc[pt.ICACHE_BEAT_ADDR_HI:3], 1'b1} ;

  assign  ifu_byp_data_err_new = (~ifu_fetch_addr_int_f[2] &  ~ifu_fetch_addr_int_f[1] &                                                                           ic_miss_buff_data_error[byp_fetch_index[pt.ICACHE_BEAT_ADDR_HI:3]] )  |
                                 (~ifu_fetch_addr_int_f[2] &   ifu_fetch_addr_int_f[1] &                                                                           ic_miss_buff_data_error[byp_fetch_index[pt.ICACHE_BEAT_ADDR_HI:3]] )  |
                                 ( ifu_fetch_addr_int_f[2] &  ~ifu_fetch_addr_int_f[1] &                                                                           ic_miss_buff_data_error[byp_fetch_index[pt.ICACHE_BEAT_ADDR_HI:3]] )  |
                                 ( ifu_fetch_addr_int_f[2] &   ifu_fetch_addr_int_f[1] & (ic_miss_buff_data_error[byp_fetch_index_inc[pt.ICACHE_BEAT_ADDR_HI:3]] | ic_miss_buff_data_error[byp_fetch_index[pt.ICACHE_BEAT_ADDR_HI:3]] )) ;

  assign  ifu_byp_data_err_f[1:0]  =   (ic_miss_buff_data_error[byp_fetch_index[pt.ICACHE_BEAT_ADDR_HI:3]] )  ? 2'b11 :
                                      ( ifu_fetch_addr_int_f[2] &  ifu_fetch_addr_int_f[1] &   ~(ic_miss_buff_data_error[byp_fetch_index[pt.ICACHE_BEAT_ADDR_HI:3]] ) & (~miss_wrap_f & ic_miss_buff_data_error[byp_fetch_index_inc[pt.ICACHE_BEAT_ADDR_HI:3]])) ? 2'b10 : 2'b00;





  assign ic_byp_data_only_pre_new[79:0] =  ({80{~ifu_fetch_addr_int_f[2]}} &   {ic_miss_buff_data[byp_fetch_index_inc_0][15:0],ic_miss_buff_data[byp_fetch_index_1][31:0]     , ic_miss_buff_data[byp_fetch_index_0][31:0]}) |
                                           ({80{ ifu_fetch_addr_int_f[2]}} &   {ic_miss_buff_data[byp_fetch_index_inc_1][15:0],ic_miss_buff_data[byp_fetch_index_inc_0][31:0] , ic_miss_buff_data[byp_fetch_index_1][31:0]}) ;

  assign ic_byp_data_only_new[79:0]      = ~ifu_fetch_addr_int_f[1] ? {ic_byp_data_only_pre_new[79:0]} :
                                                                      {16'b0,ic_byp_data_only_pre_new[79:16]} ;

  assign miss_wrap_f      =  (imb_ff[pt.ICACHE_TAG_INDEX_LO] != ifu_fetch_addr_int_f[pt.ICACHE_TAG_INDEX_LO] ) ;

  assign miss_buff_hit_unq_f  = ((ic_miss_buff_data_valid[byp_fetch_index[pt.ICACHE_BEAT_ADDR_HI:3]]                                                     & ~byp_fetch_index[2] & ~byp_fetch_index[1])) |
                             ((ic_miss_buff_data_valid[byp_fetch_index[pt.ICACHE_BEAT_ADDR_HI:3]]                                                     & ~byp_fetch_index[2] &  byp_fetch_index[1])) |
                             ((ic_miss_buff_data_valid[byp_fetch_index[pt.ICACHE_BEAT_ADDR_HI:3]]                                                     &  byp_fetch_index[2] & ~byp_fetch_index[1])) |
                             ((ic_miss_buff_data_valid[byp_fetch_index[pt.ICACHE_BEAT_ADDR_HI:3]] & ic_miss_buff_data_valid[byp_fetch_index_inc[pt.ICACHE_BEAT_ADDR_HI:3]] &  byp_fetch_index[2] &  byp_fetch_index[1])) |
                             ((ic_miss_buff_data_valid[byp_fetch_index[pt.ICACHE_BEAT_ADDR_HI:3]] &  (byp_fetch_index[pt.ICACHE_BEAT_ADDR_HI:3] == {pt.ICACHE_BEAT_BITS{1'b1}})))   ;

  assign stream_hit_f     =  (miss_buff_hit_unq_f & ~miss_wrap_f ) & (miss_state==STREAM) ;
  assign stream_miss_f    = ~(miss_buff_hit_unq_f & ~miss_wrap_f ) & (miss_state==STREAM) & ifc_fetch_req_f;
  assign stream_eol_f     =  (byp_fetch_index[pt.ICACHE_BEAT_ADDR_HI:2] == {pt.ICACHE_BEAT_BITS+1{1'b1}}) & ifc_fetch_req_f & stream_hit_f;

  assign crit_byp_hit_f   =  (miss_buff_hit_unq_f ) & ((miss_state == CRIT_WRD_RDY) | (miss_state==CRIT_BYP_OK)) ;

/////////////////////////////////////////////////////////////////////////////////////
// Figure out if you have the data to write.                                       //
/////////////////////////////////////////////////////////////////////////////////////

assign other_tag[pt.IFU_BUS_TAG-1:0] = {ifu_bus_rid_ff[pt.IFU_BUS_TAG-1:1] , ~ifu_bus_rid_ff[0] } ;
assign second_half_available      = ic_miss_buff_data_valid[other_tag] ;
assign write_ic_16_bytes          = second_half_available & bus_ifu_wr_en_ff ;
assign ic_miss_buff_half[63:0]    = {ic_miss_buff_data[{other_tag,1'b1}],ic_miss_buff_data[{other_tag,1'b0}] } ;


/////////////////////////////////////////////////////////////////////////////////////
// Parity checking logic for Icache logic.                                         //
/////////////////////////////////////////////////////////////////////////////////////


assign ic_rd_parity_final_err = ic_tag_perr & ~exu_flush_final & sel_ic_data & ~(ifc_region_acc_fault_final_f | (|ifc_bus_acc_fault_f)) &
                                      (fetch_req_icache_f & ~reset_all_tags & (~miss_pending | (miss_state==HIT_U_MISS)) & ~sel_mb_addr_ff);

logic [pt.ICACHE_NUM_WAYS-1:0]                   perr_err_inv_way;
logic [pt.ICACHE_INDEX_HI:pt.ICACHE_TAG_INDEX_LO]   perr_ic_index_ff;
logic                                         perr_sel_invalidate;
logic                                         perr_sb_write_status   ;



   rvdffe #(.WIDTH(pt.ICACHE_INDEX_HI-pt.ICACHE_TAG_INDEX_LO+1),.OVERRIDE(1)) perr_dat_ff    (.din(ifu_ic_rw_int_addr_ff[pt.ICACHE_INDEX_HI:pt.ICACHE_TAG_INDEX_LO]), .dout(perr_ic_index_ff[pt.ICACHE_INDEX_HI : pt.ICACHE_TAG_INDEX_LO]), .en(perr_sb_write_status),  .*);

   assign perr_err_inv_way[pt.ICACHE_NUM_WAYS-1:0]   =  {pt.ICACHE_NUM_WAYS{perr_sel_invalidate}} ;
   assign iccm_correct_ecc     = (perr_state == ECC_CORR);
   assign dma_sb_err_state     = (perr_state == DMA_SB_ERR);
   assign iccm_buf_correct_ecc = iccm_correct_ecc & ~dma_sb_err_state_ff;



   //////////////////////////////////// Create Parity Error State Machine ///////////////////////
   //                                   Create Parity Error State Machine                      //
   //                                   Create Parity Error State Machine                      //
   //                                   Create Parity Error State Machine                      //
   //////////////////////////////////// Create Parity Error State Machine ///////////////////////


   // FIFO state machine
   always_comb begin  : ERROR_SM
      perr_nxtstate            = ERR_IDLE;
      perr_state_en            = 1'b0;
      perr_sb_write_status     = 1'b0;
      perr_sel_invalidate      = 1'b0;

      case (perr_state)
         ERR_IDLE: begin : err_idle
                  perr_nxtstate         =  iccm_dma_sb_error ? DMA_SB_ERR : (ic_error_start & ~exu_flush_final) ? IC_WFF : ECC_WFF;
                  perr_state_en         =  (((iccm_error_start | ic_error_start) & ~dec_tlu_flush_lower_wb) | iccm_dma_sb_error) & ~dec_tlu_force_halt;
                  perr_sb_write_status  =  perr_state_en;
         end
         IC_WFF: begin : icache_wff    // All the I$ data and/or Tag errors ( parity/ECC ) will come to this state
                  perr_nxtstate       =  ERR_IDLE ;
                  perr_state_en       =   dec_tlu_flush_lower_wb | dec_tlu_force_halt ;
                  perr_sel_invalidate =  (dec_tlu_flush_err_wb &  dec_tlu_flush_lower_wb);
         end
         ECC_WFF: begin : ecc_wff
                  perr_nxtstate       =  ((~dec_tlu_flush_err_wb &  dec_tlu_flush_lower_wb ) | dec_tlu_force_halt) ? ERR_IDLE : ECC_CORR ;
                  perr_state_en       =   dec_tlu_flush_lower_wb | dec_tlu_force_halt  ;
         end
         DMA_SB_ERR : begin : dma_sb_ecc
                 perr_nxtstate       = dec_tlu_force_halt ? ERR_IDLE : ECC_CORR;
                 perr_state_en       = 1'b1;
         end
         ECC_CORR: begin : ecc_corr
                  perr_nxtstate       =  ERR_IDLE  ;
                  perr_state_en       =   1'b1   ;
         end
         default: begin : def_case
                  perr_nxtstate            = ERR_IDLE;
                  perr_state_en            = 1'b0;
                  perr_sb_write_status     = 1'b0;
                  perr_sel_invalidate      = 1'b0;
         end
      endcase
   end

   rvdffs #(($bits(perr_state_t))) perr_state_ff (.clk(active_clk), .din(perr_nxtstate), .dout({perr_state}), .en(perr_state_en),   .*);

   //////////////////////////////////// Create stop fetch State Machine /////////////////////////
   //////////////////////////////////// Create stop fetch State Machine /////////////////////////
   //////////////////////////////////// Create stop fetch State Machine /////////////////////////
   //////////////////////////////////// Create stop fetch State Machine /////////////////////////
   //////////////////////////////////// Create stop fetch State Machine /////////////////////////
   always_comb begin  : ERROR_STOP_FETCH
      err_stop_nxtstate            = ERR_STOP_IDLE;
      err_stop_state_en            = 1'b0;
      err_stop_fetch               = 1'b0;
      iccm_correction_state        = 1'b0;

      case (err_stop_state)
         ERR_STOP_IDLE: begin : err_stop_idle
                  err_stop_nxtstate         =  ERR_FETCH1;
                  err_stop_state_en         =  dec_tlu_flush_err_wb & (perr_state  == ECC_WFF) & ~dec_tlu_force_halt;
         end
         ERR_FETCH1: begin : err_fetch1    // All the I$ data and/or Tag errors ( parity/ECC ) will come to this state
                  err_stop_nxtstate       =  (dec_tlu_flush_lower_wb | dec_tlu_i0_commit_cmt | dec_tlu_force_halt) ? ERR_STOP_IDLE : ((ifu_fetch_val[1:0] == 2'b11) | (ifu_fetch_val[0] & two_byte_instr))   ?  ERR_STOP_FETCH : ifu_fetch_val[0] ? ERR_FETCH2 :  ERR_FETCH1;
                  err_stop_state_en       =   dec_tlu_flush_lower_wb | dec_tlu_i0_commit_cmt | ifu_fetch_val[0] | ifu_bp_hit_taken_q_f | dec_tlu_force_halt;
                  err_stop_fetch          =   ((ifu_fetch_val[1:0] == 2'b11) | (ifu_fetch_val[0] & two_byte_instr))  & ~(exu_flush_final | dec_tlu_i0_commit_cmt);
                  iccm_correction_state   = 1'b1;

        end
         ERR_FETCH2: begin : err_fetch2    // All the I$ data and/or Tag errors ( parity/ECC ) will come to this state
                  err_stop_nxtstate       =  (dec_tlu_flush_lower_wb | dec_tlu_i0_commit_cmt | dec_tlu_force_halt) ? ERR_STOP_IDLE : ifu_fetch_val[0] ?  ERR_STOP_FETCH : ERR_FETCH2;
                  err_stop_state_en       =   dec_tlu_flush_lower_wb | dec_tlu_i0_commit_cmt | ifu_fetch_val[0] | dec_tlu_force_halt ;
                  err_stop_fetch          =   ifu_fetch_val[0] & ~exu_flush_final & ~dec_tlu_i0_commit_cmt ;
                  iccm_correction_state   = 1'b1;

         end
         ERR_STOP_FETCH: begin : ecc_wff
                  err_stop_nxtstate       =  ( (dec_tlu_flush_lower_wb & ~dec_tlu_flush_err_wb) | dec_tlu_i0_commit_cmt | dec_tlu_force_halt) ? ERR_STOP_IDLE : dec_tlu_flush_err_wb ? ERR_FETCH1 : ERR_STOP_FETCH ;
                  err_stop_state_en       =   dec_tlu_flush_lower_wb |  dec_tlu_i0_commit_cmt | dec_tlu_force_halt   ;
                  err_stop_fetch          =  1'b1;
                  iccm_correction_state   = 1'b1;

         end
         default: begin : def_case
                  err_stop_nxtstate            = ERR_STOP_IDLE;
                  err_stop_state_en            = 1'b0;
                  err_stop_fetch               = 1'b0 ;
                  iccm_correction_state   = 1'b1;

         end
      endcase
   end
   rvdffs #(($bits(err_stop_state_t))) err_stop_state_ff (.clk(active_clk), .din(err_stop_nxtstate), .dout({err_stop_state}), .en(err_stop_state_en),   .*);



   assign bus_ifu_bus_clk_en =  ifu_bus_clk_en ;

`ifdef RV_FPGA_OPTIMIZE
   assign busclk = 1'b0;
   assign busclk_force = 1'b0;
`else
   rvclkhdr bus_clk_f(.en(bus_ifu_bus_clk_en), .l1clk(busclk), .*);
   rvclkhdr bus_clk(.en(bus_ifu_bus_clk_en | dec_tlu_force_halt), .l1clk(busclk_force), .*);
`endif



   assign  scnd_miss_req = scnd_miss_req_q & ~exu_flush_final;

   assign  ifc_bus_ic_req_ff_in  = (ic_act_miss_f | bus_cmd_req_hold | ifu_bus_cmd_valid) & ~dec_tlu_force_halt & ~((bus_cmd_beat_count== {pt.ICACHE_BEAT_BITS{1'b1}}) & ifu_bus_cmd_valid & ifu_bus_cmd_ready & miss_pending);

   rvdff_fpga #(1) bus_ic_req_ff2(.*, .clk(busclk_force), .clken(bus_ifu_bus_clk_en | dec_tlu_force_halt), .rawclk(clk), .din(ifc_bus_ic_req_ff_in), .dout(ifu_bus_cmd_valid));

   assign    bus_cmd_req_in  = (ic_act_miss_f | bus_cmd_req_hold) & ~bus_cmd_sent & ~dec_tlu_force_halt ; // hold until first command sent



    // AXI command signals
    //  Read Channel
    assign ifu_axi_arvalid               =  ifu_bus_cmd_valid ;
    assign ifu_axi_arid[pt.IFU_BUS_TAG-1:0] = ((pt.IFU_BUS_TAG)'(bus_rd_addr_count[pt.ICACHE_BEAT_BITS-1:0])) & {pt.IFU_BUS_TAG{ifu_bus_cmd_valid}};
    assign ifu_axi_araddr[31:0]          =   {ifu_ic_req_addr_f[31:3],3'b0}  & {32{ifu_bus_cmd_valid}};
    assign ifu_axi_arsize[2:0]           =  3'b011;
    assign ifu_axi_arprot[2:0]           = 3'b101;
    assign ifu_axi_arcache[3:0]          = 4'b1111;
    assign ifu_axi_arregion[3:0]         = ifu_ic_req_addr_f[31:28];
    assign ifu_axi_arlen[7:0]            = '0;
    assign ifu_axi_arburst[1:0]          = 2'b01;
    assign ifu_axi_arqos[3:0]            = '0;
    assign ifu_axi_arlock                = '0;
    assign ifu_axi_rready                = 1'b1;

    //  Write Channel
    assign ifu_axi_awvalid                  = '0 ;
    assign ifu_axi_awid[pt.IFU_BUS_TAG-1:0] = '0 ;
    assign ifu_axi_awaddr[31:0]             = '0 ;
    assign ifu_axi_awsize[2:0]              = '0 ;
    assign ifu_axi_awprot[2:0]              = '0;
    assign ifu_axi_awcache[3:0]             = '0 ;
    assign ifu_axi_awregion[3:0]            = '0 ;
    assign ifu_axi_awlen[7:0]               = '0;
    assign ifu_axi_awburst[1:0]             = '0 ;
    assign ifu_axi_awqos[3:0]               = '0;
    assign ifu_axi_awlock                   = '0;

    assign ifu_axi_wvalid                =  '0;
    assign ifu_axi_wstrb[7:0]            =  '0;
    assign ifu_axi_wdata[63:0]           =  '0;
    assign ifu_axi_wlast                 =  '0;
    assign ifu_axi_bready                =  '0;


   assign ifu_bus_arready_unq     =  ifu_axi_arready ;
   assign ifu_bus_rvalid_unq      =  ifu_axi_rvalid ;
   assign ifu_bus_arvalid         =  ifu_axi_arvalid ;

   rvdff_fpga #(1)               bus_rdy_ff      (.*, .clk(busclk),  .clken(bus_ifu_bus_clk_en), .rawclk(clk), .din(ifu_bus_arready_unq),            .dout(ifu_bus_arready_unq_ff));
   rvdff_fpga #(1)               bus_rsp_vld_ff  (.*, .clk(busclk),  .clken(bus_ifu_bus_clk_en), .rawclk(clk), .din(ifu_bus_rvalid_unq),             .dout(ifu_bus_rvalid_unq_ff));
   rvdff_fpga #(1)               bus_cmd_ff      (.*, .clk(busclk),  .clken(bus_ifu_bus_clk_en), .rawclk(clk), .din(ifu_bus_arvalid),                .dout(ifu_bus_arvalid_ff));
   rvdff_fpga #(2)               bus_rsp_cmd_ff  (.*, .clk(busclk),  .clken(bus_ifu_bus_clk_en), .rawclk(clk), .din(ifu_axi_rresp[1:0]),             .dout(ifu_bus_rresp_ff[1:0]));
   rvdff_fpga #(pt.IFU_BUS_TAG)  bus_rsp_tag_ff  (.*, .clk(busclk),  .clken(bus_ifu_bus_clk_en), .rawclk(clk), .din(ifu_axi_rid[pt.IFU_BUS_TAG-1:0]),.dout(ifu_bus_rid_ff[pt.IFU_BUS_TAG-1:0]));
   rvdffe #(64)                  bus_data_ff     (.*, .clk(clk),     .din(ifu_axi_rdata[63:0]),            .dout(ifu_bus_rdata_ff[63:0]), .en(ifu_bus_clk_en & ifu_axi_rvalid));

   assign ifu_bus_cmd_ready = ifu_axi_arready ;
   assign ifu_bus_rsp_valid = ifu_axi_rvalid ;
   assign ifu_bus_rsp_ready = ifu_axi_rready ;
   assign ifu_bus_rsp_tag[pt.IFU_BUS_TAG-1:0] = ifu_axi_rid[pt.IFU_BUS_TAG-1:0] ;
   assign ifu_bus_rsp_rdata[63:0] = ifu_axi_rdata[63:0] ;
   assign ifu_bus_rsp_opc[1:0] = {ifu_axi_rresp[1:0]} ;









   // Create write signals so we can write to the miss-buffer directly from the bus.

   assign ifu_bus_rvalid            =  ifu_bus_rsp_valid & bus_ifu_bus_clk_en ;



   assign ifu_bus_arready            =  ifu_bus_arready_unq    & bus_ifu_bus_clk_en    ;
   assign ifu_bus_arready_ff         =  ifu_bus_arready_unq_ff & bus_ifu_bus_clk_en_ff ;

   assign ifu_bus_rvalid_ff          =  ifu_bus_rvalid_unq_ff & bus_ifu_bus_clk_en_ff ;
   assign bus_cmd_sent               =  ifu_bus_arvalid & ifu_bus_arready & miss_pending & ~dec_tlu_force_halt;
   assign bus_inc_data_beat_cnt      = (bus_ifu_wr_en_ff & ~bus_last_data_beat & ~dec_tlu_force_halt) ;
   assign bus_reset_data_beat_cnt    =  ic_act_miss_f | (bus_ifu_wr_en_ff &  bus_last_data_beat) | dec_tlu_force_halt;
   assign bus_hold_data_beat_cnt     = ~bus_inc_data_beat_cnt & ~bus_reset_data_beat_cnt ;

   assign bus_new_data_beat_count[pt.ICACHE_BEAT_BITS-1:0] = ({pt.ICACHE_BEAT_BITS{bus_reset_data_beat_cnt}} & (pt.ICACHE_BEAT_BITS)'(0)) |
                                                          ({pt.ICACHE_BEAT_BITS{bus_inc_data_beat_cnt}}   & (bus_data_beat_count[pt.ICACHE_BEAT_BITS-1:0] + {{pt.ICACHE_BEAT_BITS-1{1'b0}},1'b1})) |
                                                          ({pt.ICACHE_BEAT_BITS{bus_hold_data_beat_cnt}}  &  bus_data_beat_count[pt.ICACHE_BEAT_BITS-1:0]);


   assign last_data_recieved_in =  (bus_ifu_wr_en_ff &  bus_last_data_beat & ~scnd_miss_req) | (last_data_recieved_ff & ~ic_act_miss_f) ;



// Request Address Count
   assign bus_new_rd_addr_count[pt.ICACHE_BEAT_BITS-1:0] = (~miss_pending                    ) ? imb_ff[pt.ICACHE_BEAT_ADDR_HI:3] :
                                                           (                scnd_miss_req_q  ) ? imb_scnd_ff[pt.ICACHE_BEAT_ADDR_HI:3] :
                                                           ( bus_cmd_sent                    ) ? (bus_rd_addr_count[pt.ICACHE_BEAT_BITS-1:0] + 3'b001) :
                                                                                                  bus_rd_addr_count[pt.ICACHE_BEAT_BITS-1:0];

   rvdff_fpga #(pt.ICACHE_BEAT_BITS)  bus_rd_addr_ff (.*,  .clk(busclk_reset),  .clken (bus_ifu_bus_clk_en | ic_act_miss_f | dec_tlu_force_halt), .rawclk(clk), .din ({bus_new_rd_addr_count[pt.ICACHE_BEAT_BITS-1:0]}), .dout({bus_rd_addr_count[pt.ICACHE_BEAT_BITS-1:0]}));



// command beat Count
   assign bus_inc_cmd_beat_cnt              =  ifu_bus_cmd_valid    &  ifu_bus_cmd_ready & miss_pending & ~dec_tlu_force_halt;
   assign bus_reset_cmd_beat_cnt_0          =  (ic_act_miss_f        & ~uncacheable_miss_in) | dec_tlu_force_halt ;
   assign bus_reset_cmd_beat_cnt_secondlast =  ic_act_miss_f        &  uncacheable_miss_in ;
   assign bus_hold_cmd_beat_cnt             = ~bus_inc_cmd_beat_cnt & ~(ic_act_miss_f | scnd_miss_req | dec_tlu_force_halt) ;
   assign bus_cmd_beat_en                   =  bus_inc_cmd_beat_cnt | ic_act_miss_f | dec_tlu_force_halt;

   assign bus_new_cmd_beat_count[pt.ICACHE_BEAT_BITS-1:0] =  ({pt.ICACHE_BEAT_BITS{bus_reset_cmd_beat_cnt_0}}       & (pt.ICACHE_BEAT_BITS)'(0) ) |
                                                          ({pt.ICACHE_BEAT_BITS{bus_reset_cmd_beat_cnt_secondlast}} & (pt.ICACHE_BEAT_BITS)'(pt.ICACHE_SCND_LAST)) |
                                                          ({pt.ICACHE_BEAT_BITS{bus_inc_cmd_beat_cnt}}              & (bus_cmd_beat_count[pt.ICACHE_BEAT_BITS-1:0] + {{pt.ICACHE_BEAT_BITS-1{1'b0}}, 1'b1})) |
                                                          ({pt.ICACHE_BEAT_BITS{bus_hold_cmd_beat_cnt}}             &  bus_cmd_beat_count[pt.ICACHE_BEAT_BITS-1:0]) ;

`ifdef RV_FPGA_OPTIMIZE
   assign busclk_reset = 1'b0;
`else
   rvclkhdr bus_clk_reset(.en(bus_ifu_bus_clk_en | ic_act_miss_f | dec_tlu_force_halt), .l1clk(busclk_reset), .*);
`endif



   rvdffs_fpga #(pt.ICACHE_BEAT_BITS)  bus_cmd_beat_ff (.*, .clk(busclk_reset), .clken (bus_ifu_bus_clk_en | ic_act_miss_f | dec_tlu_force_halt), .rawclk(clk), .en (bus_cmd_beat_en), .din ({bus_new_cmd_beat_count[pt.ICACHE_BEAT_BITS-1:0]}),
                    .dout({bus_cmd_beat_count[pt.ICACHE_BEAT_BITS-1:0]}));


    assign bus_last_data_beat     =  uncacheable_miss_ff ? (bus_data_beat_count[pt.ICACHE_BEAT_BITS-1:0] == {{pt.ICACHE_BEAT_BITS-1{1'b0}},1'b1}) : (&bus_data_beat_count[pt.ICACHE_BEAT_BITS-1:0]);

   assign  bus_ifu_wr_en            =  ifu_bus_rvalid     & miss_pending ;
   assign  bus_ifu_wr_en_ff         =  ifu_bus_rvalid_ff  & miss_pending ;
   assign  bus_ifu_wr_en_ff_q       =  ifu_bus_rvalid_ff  & miss_pending & ~uncacheable_miss_ff & ~(|ifu_bus_rresp_ff[1:0]) & write_ic_16_bytes; // qualify with no-error conditions ;
   assign  bus_ifu_wr_en_ff_wo_err  =  ifu_bus_rvalid_ff & miss_pending &  ~uncacheable_miss_ff;


   rvdffie #(10) misc_ff
       ( .*,
         .clk(free_l2clk),
         .din( {ic_act_miss_f,        ifu_wr_cumulative_err,exu_flush_final,  ic_crit_wd_rdy_new_in,bus_ifu_bus_clk_en,   scnd_miss_req_in,bus_cmd_req_in,  last_data_recieved_in,
ifc_dma_access_ok_d,   dma_iccm_req}),
         .dout({ic_act_miss_f_delayed,ifu_wr_data_comb_err_ff,  flush_final_f,ic_crit_wd_rdy_new_ff,bus_ifu_bus_clk_en_ff,scnd_miss_req_q, bus_cmd_req_hold,last_data_recieved_ff,
ifc_dma_access_ok_prev,dma_iccm_req_f})
         );

   rvdffie #(.WIDTH(pt.ICACHE_BEAT_BITS+5),.OVERRIDE(1)) misc1_ff
       ( .*,
         .clk(free_l2clk),
         .din( {reset_ic_in,sel_mb_addr,   bus_new_data_beat_count[pt.ICACHE_BEAT_BITS-1:0],ifc_region_acc_fault_memory_bf,ic_debug_rd_en,       ic_debug_rd_en_ff}),
         .dout({reset_ic_ff,sel_mb_addr_ff,bus_data_beat_count[pt.ICACHE_BEAT_BITS-1:0],    ifc_region_acc_fault_memory_f, ic_debug_rd_en_ff,ifu_ic_debug_rd_data_valid})
         );

   assign    reset_tag_valid_for_miss = ic_act_miss_f_delayed & (miss_state == CRIT_BYP_OK) & ~uncacheable_miss_ff;
   assign    bus_ifu_wr_data_error    = |ifu_bus_rsp_opc[1:0] &  ifu_bus_rvalid  & miss_pending;
   assign    bus_ifu_wr_data_error_ff = |ifu_bus_rresp_ff[1:0] &  ifu_bus_rvalid_ff  & miss_pending;


   assign ic_crit_wd_rdy   =  ic_crit_wd_rdy_new_in | ic_crit_wd_rdy_new_ff ;
   assign last_beat        =  bus_last_data_beat & bus_ifu_wr_en_ff;
   assign reset_beat_cnt    = bus_reset_data_beat_cnt ;

// DMA
   // Making sure that the dma_access is allowed when we have 2 back to back dma_access_ok. Also gating with current state == idle
   assign ifc_dma_access_ok_d  = ifc_dma_access_ok &  ~iccm_correct_ecc & ~iccm_dma_sb_error;
   assign ifc_dma_access_q_ok  = ifc_dma_access_ok &  ~iccm_correct_ecc & ifc_dma_access_ok_prev &  (perr_state == ERR_IDLE)  & ~iccm_dma_sb_error;
   assign iccm_ready           = ifc_dma_access_q_ok ;

   logic [1:0]        iccm_ecc_word_enable;

    if (pt.ICCM_ENABLE == 1 ) begin: iccm_enabled
         logic  [3:2] dma_mem_addr_ff  ;
         logic  iccm_dma_rden    ;

         logic  iccm_dma_ecc_error_in;
         logic  [13:0] dma_mem_ecc;
         logic  [63:0] iccm_dma_rdata_in;
         logic  [31:0] iccm_dma_rdata_1_muxed;
         logic [1:0] [31:0] iccm_corrected_data;
         logic [1:0] [06:0] iccm_corrected_ecc;


         logic [1:0]        iccm_double_ecc_error;


         logic [pt.ICCM_BITS-1:2]       iccm_rw_addr_f;

         logic [31:0]       iccm_corrected_data_f_mux;
         logic [06:0]       iccm_corrected_ecc_f_mux;
         logic              iccm_dma_rvalid_in;
         logic [77:0]       iccm_rdmux_data;
         logic              iccm_rd_ecc_single_err_hold_in ;
         logic [2:0]        dma_mem_tag_ff;




         assign iccm_wren          =  (ifc_dma_access_q_ok & dma_iccm_req &  dma_mem_write) | iccm_correct_ecc;
         assign iccm_rden          =  (ifc_dma_access_q_ok & dma_iccm_req & ~dma_mem_write) | (ifc_iccm_access_bf & ifc_fetch_req_bf);
         assign iccm_dma_rden      =  (ifc_dma_access_q_ok & dma_iccm_req & ~dma_mem_write)                     ;
         assign iccm_wr_size[2:0]  =  {3{dma_iccm_req}}    & dma_mem_sz[2:0] ;

         rvecc_encode  iccm_ecc_encode0 (
                           .din(dma_mem_wdata[31:0]),
                           .ecc_out(dma_mem_ecc[6:0]));

         rvecc_encode  iccm_ecc_encode1 (
                           .din(dma_mem_wdata[63:32]),
                           .ecc_out(dma_mem_ecc[13:7]));

        assign iccm_wr_data[77:0]   =  (iccm_correct_ecc & ~(ifc_dma_access_q_ok & dma_iccm_req)) ?  {iccm_ecc_corr_data_ff[38:0], iccm_ecc_corr_data_ff[38:0]} :
                                       {dma_mem_ecc[13:7],dma_mem_wdata[63:32], dma_mem_ecc[6:0],dma_mem_wdata[31:0]};

         assign iccm_dma_rdata_1_muxed[31:0] = dma_mem_addr_ff[2] ?  iccm_corrected_data[0][31:0] : iccm_corrected_data[1][31:0] ;
         assign iccm_dma_rdata_in[63:0]      = iccm_dma_ecc_error_in ? {2{dma_mem_addr[31:0]}} : {iccm_dma_rdata_1_muxed[31:0], iccm_corrected_data[0]};
         assign iccm_dma_ecc_error_in   =   |(iccm_double_ecc_error[1:0]);

         rvdffe    #(64) dma_data_ff      (.*, .clk(clk), .en(iccm_dma_rvalid_in),  .din(iccm_dma_rdata_in[63:0]), .dout(iccm_dma_rdata[63:0]));
         rvdffie   #(11) dma_misc_bits    (.*, .clk(free_l2clk), .din({dma_mem_tag[2:0],
                                                                       dma_mem_tag_ff[2:0],
                                                                       dma_mem_addr[3:2],
                                                                       iccm_dma_rden,
                                                                       iccm_dma_rvalid_in,
                                                                       iccm_dma_ecc_error_in }),
                                                                .dout({dma_mem_tag_ff[2:0],
                                                                       iccm_dma_rtag[2:0],
                                                                       dma_mem_addr_ff[3:2],
                                                                       iccm_dma_rvalid_in,
                                                                       iccm_dma_rvalid,
                                                                       iccm_dma_ecc_error }));

         assign iccm_rw_addr[pt.ICCM_BITS-1:1]    = (  ifc_dma_access_q_ok & dma_iccm_req  & ~iccm_correct_ecc) ? dma_mem_addr[pt.ICCM_BITS-1:1] :
                                                 (~(ifc_dma_access_q_ok & dma_iccm_req) &  iccm_correct_ecc) ? {iccm_ecc_corr_index_ff[pt.ICCM_BITS-1:2],1'b0} : ifc_fetch_addr_bf[pt.ICCM_BITS-1:1] ;




/////////////////////////////////////////////////////////////////////////////////////
// ECC checking logic for ICCM data.                                               //
/////////////////////////////////////////////////////////////////////////////////////

  logic [3:0] ic_fetch_val_int_f;
  logic [3:0] ic_fetch_val_shift_right;
  assign ic_fetch_val_int_f[3:0] = {2'b00 , ic_fetch_val_f[1:0] } ;
  assign ic_fetch_val_shift_right[3:0] = {ic_fetch_val_int_f << ifu_fetch_addr_int_f[1] } ;

   assign iccm_rdmux_data[77:0] = iccm_rd_data_ecc[77:0];
   for (genvar i=0; i < 2 ; i++) begin : ICCM_ECC_CHECK
      assign iccm_ecc_word_enable[i] = ((|ic_fetch_val_shift_right[(2*i+1):(2*i)] & ~exu_flush_final & sel_iccm_data) | iccm_dma_rvalid_in) & ~dec_tlu_core_ecc_disable;
   rvecc_decode  ecc_decode (
                           .en(iccm_ecc_word_enable[i]),
                           .sed_ded ( 1'b0 ),    // 1 : means only detection
                           .din(iccm_rdmux_data[(39*i+31):(39*i)]),
                           .ecc_in(iccm_rdmux_data[(39*i+38):(39*i+32)]),
                           .dout(iccm_corrected_data[i][31:0]),
                           .ecc_out(iccm_corrected_ecc[i][6:0]),
                           .single_ecc_error(iccm_single_ecc_error[i]),
                           .double_ecc_error(iccm_double_ecc_error[i]));
end

  assign iccm_rd_ecc_single_err  = (|iccm_single_ecc_error[1:0] ) & ifc_iccm_access_f & ifc_fetch_req_f;
  assign iccm_rd_ecc_double_err[1:0]  = ~ifu_fetch_addr_int_f[1] ? ({iccm_double_ecc_error[0], iccm_double_ecc_error[0]} ) & {2{ifc_iccm_access_f}} :
                                                                   ({iccm_double_ecc_error[1], iccm_double_ecc_error[0]} ) & {2{ifc_iccm_access_f}} ;

  assign iccm_corrected_data_f_mux[31:0] = iccm_single_ecc_error[0] ? iccm_corrected_data[0] : iccm_corrected_data[1];
  assign iccm_corrected_ecc_f_mux[6:0]   = iccm_single_ecc_error[0] ? iccm_corrected_ecc[0]  : iccm_corrected_ecc[1];

  assign iccm_ecc_write_status           = ((iccm_rd_ecc_single_err & ~iccm_rd_ecc_single_err_ff)  & ~exu_flush_final) | iccm_dma_sb_error;
  assign iccm_rd_ecc_single_err_hold_in  = (iccm_rd_ecc_single_err | iccm_rd_ecc_single_err_ff) & ~exu_flush_final ;
  assign iccm_error_start                =  iccm_rd_ecc_single_err;
  assign iccm_ecc_corr_index_in[pt.ICCM_BITS-1:2] = iccm_single_ecc_error[0] ? iccm_rw_addr_f[pt.ICCM_BITS-1:2] : iccm_rw_addr_f[pt.ICCM_BITS-1:2] + 1'b1 ;

   rvdffie #(pt.ICCM_BITS-1) iccm_index_f   (.*, .clk(free_l2clk), .din({iccm_rw_addr[pt.ICCM_BITS-1:2],
                                                                         iccm_rd_ecc_single_err_hold_in
                                                                                                       }),
                                                                  .dout({iccm_rw_addr_f[pt.ICCM_BITS-1:2],
                                                                         iccm_rd_ecc_single_err_ff}));

   rvdffe #((39+(pt.ICCM_BITS-2)))      ecc_dat0_ff  (
                                                      .clk(clk),
                                                      .din({iccm_corrected_ecc_f_mux[6:0],  iccm_corrected_data_f_mux[31:0],iccm_ecc_corr_index_in[pt.ICCM_BITS-1:2]}),
                                                      .dout({iccm_ecc_corr_data_ff[38:0]   ,iccm_ecc_corr_index_ff[pt.ICCM_BITS-1:2]}),
                                                      .en(iccm_ecc_write_status),
                                                      .*
                                                      );

     end else begin : iccm_disabled
         assign iccm_dma_rvalid = 1'b0 ;
         assign iccm_dma_ecc_error = 1'b0 ;
         assign iccm_dma_rdata[63:0] = '0 ;
         assign iccm_single_ecc_error = '0 ;
         assign iccm_dma_rtag         = '0 ;






         assign iccm_rd_ecc_single_err                 = 1'b0 ;
         assign iccm_rd_ecc_double_err                 = '0 ;
         assign iccm_rd_ecc_single_err_ff              = 1'b0 ;
         assign iccm_error_start                         = 1'b0;
         assign iccm_ecc_corr_index_ff[pt.ICCM_BITS-1:2]  =  '0;
         assign iccm_ecc_corr_data_ff[38:0]            =  '0;
         assign iccm_ecc_write_status                  =  '0;






    end


////// ICCM signals


 assign   ic_rd_en    =  (ifc_fetch_req_bf & ~ifc_fetch_uncacheable_bf & ~ifc_iccm_access_bf  &
                            ~(((miss_state == STREAM) & ~miss_state_en)                                       |
                              ((miss_state == CRIT_BYP_OK) & ~miss_state_en)                                  |
                              ((miss_state == STALL_SCND_MISS) & ~miss_state_en)                              |
                              ((miss_state == MISS_WAIT) & ~miss_state_en)                                    |
                              ((miss_state == CRIT_WRD_RDY) & ~miss_state_en)  |
                              ((miss_state == CRIT_BYP_OK) &  miss_state_en &  (miss_nxtstate == MISS_WAIT))  ))  |
                             ( ifc_fetch_req_bf & exu_flush_final  & ~ifc_fetch_uncacheable_bf & ~ifc_iccm_access_bf )     ;

logic   ic_real_rd_wp_unused;
assign  ic_real_rd_wp_unused  =  (ifc_fetch_req_bf &  ~ifc_iccm_access_bf  &  ~ifc_region_acc_fault_final_bf & ~dec_tlu_fence_i_wb & ~stream_miss_f & ~ic_act_miss_f &
                            ~(((miss_state == STREAM) & ~miss_state_en) |
                              ((miss_state == CRIT_BYP_OK) & ~miss_state_en & ~(miss_nxtstate == MISS_WAIT)) |
                              ((miss_state == CRIT_BYP_OK) &  miss_state_en &  (miss_nxtstate == MISS_WAIT)) |
                              ((miss_state == MISS_WAIT) & ~miss_state_en) |
                              ((miss_state == STALL_SCND_MISS) & ~miss_state_en)  |
                              ((miss_state == CRIT_WRD_RDY) & ~miss_state_en)  |
                              ((miss_nxtstate == STREAM) &  miss_state_en)  |
                              ((miss_state == SCND_MISS) & ~miss_state_en))) |
                          (ifc_fetch_req_bf &  ~ifc_iccm_access_bf  &  ~ifc_region_acc_fault_final_bf & ~dec_tlu_fence_i_wb & ~stream_miss_f & exu_flush_final)  ;


assign ic_wr_en[pt.ICACHE_NUM_WAYS-1:0] = bus_ic_wr_en[pt.ICACHE_NUM_WAYS-1:0] & {pt.ICACHE_NUM_WAYS{write_ic_16_bytes}};
assign ic_write_stall                =  write_ic_16_bytes &  ~((((miss_state== CRIT_BYP_OK) | ((miss_state==STREAM) & ~(exu_flush_final | ifu_bp_hit_taken_q_f  | stream_eol_f ))) & ~(bus_ifu_wr_en_ff & last_beat & ~uncacheable_miss_ff)));




///////////////////////////////////////////////////////////////
// Icache status and LRU
///////////////////////////////////////////////////////////////
logic [pt.ICACHE_NUM_WAYS-1:0] ic_tag_valid_unq;
if (pt.ICACHE_ENABLE == 1 ) begin: icache_enabled
   assign  ic_valid  = ~ifu_wr_cumulative_err_data & ~(reset_ic_in | reset_ic_ff) & ~reset_tag_valid_for_miss;

   assign ifu_status_wr_addr_w_debug[pt.ICACHE_INDEX_HI:pt.ICACHE_TAG_INDEX_LO] = ((ic_debug_rd_en | ic_debug_wr_en ) & ic_debug_tag_array) ?
                                                                           ic_debug_addr[pt.ICACHE_INDEX_HI:pt.ICACHE_TAG_INDEX_LO] :
                                                                           ifu_status_wr_addr[pt.ICACHE_INDEX_HI:pt.ICACHE_TAG_INDEX_LO];

   // status

         assign way_status_wr_en_w_debug = way_status_wr_en | (ic_debug_wr_en  & ic_debug_tag_array);

         assign way_status_new_w_debug[pt.ICACHE_STATUS_BITS-1:0]  = (ic_debug_wr_en  & ic_debug_tag_array) ? (pt.ICACHE_STATUS_BITS == 1) ? ic_debug_wr_data[4] : ic_debug_wr_data[6:4] :
                                                way_status_new[pt.ICACHE_STATUS_BITS-1:0] ;

   rvdffie #(.WIDTH(pt.ICACHE_TAG_LO-pt.ICACHE_TAG_INDEX_LO+1+pt.ICACHE_STATUS_BITS),.OVERRIDE(1))  status_misc_ff
     (.*,
      .clk(free_l2clk),
      .din({ ifu_status_wr_addr_w_debug[pt.ICACHE_INDEX_HI:pt.ICACHE_TAG_INDEX_LO], way_status_wr_en_w_debug, way_status_new_w_debug[pt.ICACHE_STATUS_BITS-1:0]}),
      .dout({ifu_status_wr_addr_ff[pt.ICACHE_INDEX_HI:pt.ICACHE_TAG_INDEX_LO],      way_status_wr_en_ff,      way_status_new_ff[pt.ICACHE_STATUS_BITS-1:0]} )
      );

   logic [(pt.ICACHE_TAG_DEPTH/8)-1 : 0] way_status_clken;
   logic [(pt.ICACHE_TAG_DEPTH/8)-1 : 0] way_status_clk;

   for (genvar i=0 ; i<pt.ICACHE_TAG_DEPTH/8 ; i++) begin : CLK_GRP_WAY_STATUS
      assign way_status_clken[i] = (ifu_status_wr_addr_ff[pt.ICACHE_INDEX_HI:pt.ICACHE_TAG_INDEX_LO+3] == i );
     `ifdef RV_FPGA_OPTIMIZE
        assign way_status_clk[i] = 1'b0;
     `else
           rvclkhdr way_status_cgc ( .en(way_status_clken[i]),   .l1clk(way_status_clk[i]), .* );
     `endif


      for (genvar j=0 ; j<8 ; j++) begin : WAY_STATUS
         rvdffs_fpga #(pt.ICACHE_STATUS_BITS) ic_way_status (.*,
                   .clk(way_status_clk[i]),
                   .clken(way_status_clken[i]),
                   .rawclk(clk),
                   .en(((ifu_status_wr_addr_ff[pt.ICACHE_TAG_INDEX_LO+2:pt.ICACHE_TAG_INDEX_LO] == j) & way_status_wr_en_ff)),
                   .din(way_status_new_ff[pt.ICACHE_STATUS_BITS-1:0]),
                   .dout(way_status_out[8*i+j]));
      end  // WAY_STATUS
   end  // CLK_GRP_WAY_STATUS

  always_comb begin : way_status_out_mux
      way_status[pt.ICACHE_STATUS_BITS-1:0] = '0 ;
      for (int j=0; j< pt.ICACHE_TAG_DEPTH; j++) begin : status_mux_loop
        if (ifu_ic_rw_int_addr_ff[pt.ICACHE_INDEX_HI:pt.ICACHE_TAG_INDEX_LO] == (pt.ICACHE_TAG_LO-pt.ICACHE_TAG_INDEX_LO)'(j)) begin : mux_out
         way_status[pt.ICACHE_STATUS_BITS-1:0] =  way_status_out[j];
        end
      end
  end

         assign ifu_ic_rw_int_addr_w_debug[pt.ICACHE_INDEX_HI:pt.ICACHE_TAG_INDEX_LO] = ((ic_debug_rd_en | ic_debug_wr_en ) & ic_debug_tag_array) ?
                                                                        ic_debug_addr[pt.ICACHE_INDEX_HI:pt.ICACHE_TAG_INDEX_LO] :
                                                                        ifu_ic_rw_int_addr[pt.ICACHE_INDEX_HI:pt.ICACHE_TAG_INDEX_LO];
         assign ifu_tag_wren_w_debug[pt.ICACHE_NUM_WAYS-1:0] = ifu_tag_wren[pt.ICACHE_NUM_WAYS-1:0] | ic_debug_tag_wr_en[pt.ICACHE_NUM_WAYS-1:0] ;

         assign ic_valid_w_debug = (ic_debug_wr_en & ic_debug_tag_array) ? ic_debug_wr_data[0] : ic_valid;

         rvdffie #(pt.ICACHE_TAG_LO-pt.ICACHE_TAG_INDEX_LO+pt.ICACHE_NUM_WAYS+1) tag_addr_ff (.*,
                                                                                              .clk(free_l2clk),
                                                                                              .din({ifu_ic_rw_int_addr_w_debug[pt.ICACHE_INDEX_HI:pt.ICACHE_TAG_INDEX_LO],
                                                                                                    ifu_tag_wren_w_debug[pt.ICACHE_NUM_WAYS-1:0],
                                                                                                    ic_valid_w_debug}),
                                                                                              .dout({ifu_ic_rw_int_addr_ff[pt.ICACHE_INDEX_HI:pt.ICACHE_TAG_INDEX_LO],
                                                                                                     ifu_tag_wren_ff[pt.ICACHE_NUM_WAYS-1:0],
                                                                                                     ic_valid_ff})
                                                                                              );


   logic [pt.ICACHE_NUM_WAYS-1:0] [pt.ICACHE_TAG_DEPTH-1:0] ic_tag_valid_out ;

   logic [(pt.ICACHE_TAG_DEPTH/32)-1:0] [pt.ICACHE_NUM_WAYS-1:0] tag_valid_clken ;
   logic [(pt.ICACHE_TAG_DEPTH/32)-1:0] [pt.ICACHE_NUM_WAYS-1:0] tag_valid_clk   ;

   for (genvar i=0 ; i<pt.ICACHE_TAG_DEPTH/32 ; i++) begin : CLK_GRP_TAG_VALID
      for (genvar j=0; j<pt.ICACHE_NUM_WAYS; j++) begin : way_clken
      if (pt.ICACHE_TAG_DEPTH == 32 ) begin
        assign tag_valid_clken[i][j] =  ifu_tag_wren_ff[j] | perr_err_inv_way[j] | reset_all_tags;
      end else begin
         assign tag_valid_clken[i][j] = (((ifu_ic_rw_int_addr_ff[pt.ICACHE_INDEX_HI:pt.ICACHE_TAG_INDEX_LO+5] == i ) &  ifu_tag_wren_ff[j] ) |
                                        ((perr_ic_index_ff     [pt.ICACHE_INDEX_HI:pt.ICACHE_TAG_INDEX_LO+5] == i ) &  perr_err_inv_way[j]) | reset_all_tags);
      end

     `ifdef RV_FPGA_OPTIMIZE
        assign tag_valid_clk[i][j]  = 1'b0;
     `else
           rvclkhdr way_status_cgc ( .en(tag_valid_clken[i][j]),   .l1clk(tag_valid_clk[i][j]), .* );
     `endif



      for (genvar k=0 ; k<32 ; k++) begin : TAG_VALID
         rvdffs_fpga #(1) ic_way_tagvalid_dup (.*,
                   .clk(tag_valid_clk[i][j]),
                   .clken(tag_valid_clken[i][j]),
                   .rawclk(clk),
                   .en(((ifu_ic_rw_int_addr_ff[pt.ICACHE_INDEX_HI:pt.ICACHE_TAG_INDEX_LO] == (k + 32*i)) & ifu_tag_wren_ff[j] ) |
                       ((perr_ic_index_ff     [pt.ICACHE_INDEX_HI:pt.ICACHE_TAG_INDEX_LO] == (k + 32*i)) & perr_err_inv_way[j]) | reset_all_tags),
                   .din(ic_valid_ff & ~reset_all_tags & ~perr_sel_invalidate),
                   .dout(ic_tag_valid_out[j][32*i+k]));
      end
      end
   end


  always_comb begin : tag_valid_out_mux
      ic_tag_valid_unq[pt.ICACHE_NUM_WAYS-1:0] = '0;
      for (int j=0; j< pt.ICACHE_TAG_DEPTH; j++) begin : tag_valid_loop
        if (ifu_ic_rw_int_addr_ff[pt.ICACHE_INDEX_HI:pt.ICACHE_TAG_INDEX_LO] == (pt.ICACHE_TAG_LO-pt.ICACHE_TAG_INDEX_LO)'(j)) begin : valid_out
           for ( int k=0; k<pt.ICACHE_NUM_WAYS; k++) begin
             ic_tag_valid_unq[k] |= ic_tag_valid_out[k][j];
        end
      end
      end
  end
   //   four-way set associative - three bits
//   each bit represents one branch point in a binary decision tree; let 1
//   represent that the left side has been referenced more recently than the
//   right side, and 0 vice-versa
//
//              are all 4 ways valid?
//                   /       \
//                  |        no, use an invalid way.
//                  |
//                  |
//             bit_0 == 0?             state | replace      ref to | next state
//               /       \             ------+--------      -------+-----------
//              y         n             x00  |  way_0      way_0 |    _11
//             /           \            x10  |  way_1      way_1 |    _01
//      bit_1 == 0?    bit_2 == 0?      0x1  |  way_2      way_2 |    1_0
//        /    \          /    \        1x1  |  way_3      way_3 |    0_0
//       y      n        y      n
//      /        \      /        \        ('x' means don't care       ('_' means unchanged)
//    way_0    way_1  way_2     way_3      don't care)

   if (pt.ICACHE_NUM_WAYS == 4) begin: four_way_plru
   assign replace_way_mb_any[3] = ( way_status_mb_ff[2]  & way_status_mb_ff[0] & (&tagv_mb_ff[3:0])) |
                                  (~tagv_mb_ff[3]& tagv_mb_ff[2] &  tagv_mb_ff[1] &  tagv_mb_ff[0]) ;
   assign replace_way_mb_any[2] = (~way_status_mb_ff[2]  & way_status_mb_ff[0] & (&tagv_mb_ff[3:0])) |
                                  (~tagv_mb_ff[2]& tagv_mb_ff[1] &  tagv_mb_ff[0]) ;
   assign replace_way_mb_any[1] = ( way_status_mb_ff[1] & ~way_status_mb_ff[0] & (&tagv_mb_ff[3:0])) |
                                  (~tagv_mb_ff[1]& tagv_mb_ff[0] ) ;
   assign replace_way_mb_any[0] = (~way_status_mb_ff[1] & ~way_status_mb_ff[0] & (&tagv_mb_ff[3:0])) |
                                  (~tagv_mb_ff[0] ) ;

   assign way_status_hit_new[pt.ICACHE_STATUS_BITS-1:0] = ({3{~exu_flush_final & ic_rd_hit[0]}} & {way_status[2] , 1'b1 , 1'b1}) |
                                                          ({3{~exu_flush_final & ic_rd_hit[1]}} & {way_status[2] , 1'b0 , 1'b1}) |
                                                          ({3{~exu_flush_final & ic_rd_hit[2]}} & {1'b1 ,way_status[1]  , 1'b0}) |
                                                          ({3{~exu_flush_final & ic_rd_hit[3]}} & {1'b0 ,way_status[1]  , 1'b0}) ;

  assign way_status_rep_new[pt.ICACHE_STATUS_BITS-1:0] = ({3{replace_way_mb_any[0]}} & {way_status_mb_ff[2] , 1'b1 , 1'b1}) |
                                   ({3{replace_way_mb_any[1]}} & {way_status_mb_ff[2] , 1'b0 , 1'b1}) |
                                   ({3{replace_way_mb_any[2]}} & {1'b1 ,way_status_mb_ff[1]  , 1'b0}) |
                                   ({3{replace_way_mb_any[3]}} & {1'b0 ,way_status_mb_ff[1]  , 1'b0}) ;
  end
   else begin : two_ways_plru
      assign replace_way_mb_any[0]                      = (~way_status_mb_ff  & tagv_mb_ff[0] & tagv_mb_ff[1]) | ~tagv_mb_ff[0];
      assign replace_way_mb_any[1]                      = ( way_status_mb_ff  & tagv_mb_ff[0] & tagv_mb_ff[1]) | ~tagv_mb_ff[1] & tagv_mb_ff[0];
      assign way_status_hit_new[pt.ICACHE_STATUS_BITS-1:0] = ic_rd_hit[0];
      assign way_status_rep_new[pt.ICACHE_STATUS_BITS-1:0] = replace_way_mb_any[0];

   end
  // Make sure to select the way_status_hit_new even when in hit_under_miss.
  assign way_status_new[pt.ICACHE_STATUS_BITS-1:0]     = (bus_ifu_wr_en_ff_q  & last_beat )  ? way_status_rep_new[pt.ICACHE_STATUS_BITS-1:0] :
                                                          way_status_hit_new[pt.ICACHE_STATUS_BITS-1:0] ;


  assign way_status_wr_en  = (bus_ifu_wr_en_ff_q  & last_beat) | ic_act_hit_f;

   for (genvar i=0; i<pt.ICACHE_NUM_WAYS; i++) begin  : bus_wren_loop
      assign bus_wren[i]           = bus_ifu_wr_en_ff_q & replace_way_mb_any[i] & miss_pending ;
      assign bus_wren_last[i]      = bus_ifu_wr_en_ff_wo_err & replace_way_mb_any[i] & miss_pending & bus_last_data_beat;
      assign ifu_tag_wren[i]       = bus_wren_last[i] | wren_reset_miss[i];
      assign wren_reset_miss[i]    = replace_way_mb_any[i] & reset_tag_valid_for_miss ;

   end
   assign bus_ic_wr_en[pt.ICACHE_NUM_WAYS-1:0] = bus_wren[pt.ICACHE_NUM_WAYS-1:0];


end else begin: icache_disabled
   assign ic_tag_valid_unq[pt.ICACHE_NUM_WAYS-1:0]      = '0;
   assign way_status[pt.ICACHE_STATUS_BITS-1:0]         = '0;
   assign replace_way_mb_any[pt.ICACHE_NUM_WAYS-1:0]    = '0;
   assign way_status_hit_new[pt.ICACHE_STATUS_BITS-1:0] = '0;
   assign way_status_rep_new[pt.ICACHE_STATUS_BITS-1:0] = '0;
   assign way_status_new[pt.ICACHE_STATUS_BITS-1:0]     = '0;
   assign way_status_wr_en                           = '0;
   assign bus_wren[pt.ICACHE_NUM_WAYS-1:0]              = '0;

end

   assign ic_tag_valid[pt.ICACHE_NUM_WAYS-1:0] = ic_tag_valid_unq[pt.ICACHE_NUM_WAYS-1:0]   & {pt.ICACHE_NUM_WAYS{(~fetch_uncacheable_ff & ifc_fetch_req_f_raw) }} ;
   assign ic_debug_tag_val_rd_out           = |(ic_tag_valid_unq[pt.ICACHE_NUM_WAYS-1:0] &  ic_debug_way_ff[pt.ICACHE_NUM_WAYS-1:0]   & {pt.ICACHE_NUM_WAYS{ic_debug_rd_en_ff}}) ;
///////////////////////////////////////////
// PMU signals
///////////////////////////////////////////

 assign ifu_pmu_ic_miss_in   = ic_act_miss_f ;
 assign ifu_pmu_ic_hit_in    = ic_act_hit_f  ;
 assign ifu_pmu_bus_error_in = |ifc_bus_acc_fault_f;
 assign ifu_pmu_bus_trxn_in  = bus_cmd_sent ;
 assign ifu_pmu_bus_busy_in  = ifu_bus_arvalid_ff & ~ifu_bus_arready_ff & miss_pending ;

   rvdffie #(9) ifu_pmu_sigs_ff (.*,
                    .clk (free_l2clk),
                    .din ({ifc_fetch_uncacheable_bf, ifc_fetch_req_qual_bf, dma_sb_err_state, dec_tlu_fence_i_wb,
                           ifu_pmu_ic_miss_in,
                           ifu_pmu_ic_hit_in,
                           ifu_pmu_bus_error_in,
                           ifu_pmu_bus_busy_in,
                           ifu_pmu_bus_trxn_in
                          }),
                    .dout({fetch_uncacheable_ff, ifc_fetch_req_f_raw, dma_sb_err_state_ff, reset_all_tags,
                           ifu_pmu_ic_miss,
                           ifu_pmu_ic_hit,
                           ifu_pmu_bus_error,
                           ifu_pmu_bus_busy,
                           ifu_pmu_bus_trxn
                           }));


///////////////////////////////////////////////////////
// Cache debug logic                                 //
///////////////////////////////////////////////////////
assign ic_debug_addr[pt.ICACHE_INDEX_HI:3] = dec_tlu_ic_diag_pkt.icache_dicawics[pt.ICACHE_INDEX_HI-3:0] ;
assign ic_debug_way_enc[01:00]             = dec_tlu_ic_diag_pkt.icache_dicawics[15:14] ;


assign ic_debug_tag_array       = dec_tlu_ic_diag_pkt.icache_dicawics[16] ;
assign ic_debug_rd_en           = dec_tlu_ic_diag_pkt.icache_rd_valid ;
assign ic_debug_wr_en           = dec_tlu_ic_diag_pkt.icache_wr_valid ;


assign ic_debug_way[pt.ICACHE_NUM_WAYS-1:0]        = {(ic_debug_way_enc[1:0] == 2'b11),
                                                      (ic_debug_way_enc[1:0] == 2'b10),
                                                      (ic_debug_way_enc[1:0] == 2'b01),
                                                      (ic_debug_way_enc[1:0] == 2'b00) };

assign ic_debug_tag_wr_en[pt.ICACHE_NUM_WAYS-1:0] = {pt.ICACHE_NUM_WAYS{ic_debug_wr_en & ic_debug_tag_array}} & ic_debug_way[pt.ICACHE_NUM_WAYS-1:0] ;

assign ic_debug_ict_array_sel_in      =  ic_debug_rd_en & ic_debug_tag_array ;

rvdff_fpga #(01+pt.ICACHE_NUM_WAYS) ifu_debug_sel_ff (.*, .clk (debug_c1_clk),
                    .clken(debug_c1_clken), .rawclk(clk),
                    .din ({ic_debug_ict_array_sel_in,
                           ic_debug_way[pt.ICACHE_NUM_WAYS-1:0]
                          }),
                    .dout({ic_debug_ict_array_sel_ff,
                           ic_debug_way_ff[pt.ICACHE_NUM_WAYS-1:0]
                           }));




assign debug_data_clken  =  ic_debug_rd_en_ff;




// memory protection  - equation to look identical to the LSU equation
   if (pt.PMP_ENTRIES != 0) begin : g_ifc_access_check_pmp
      assign ifc_region_acc_okay = ~ifu_pmp_error;
      assign ifc_region_acc_fault_memory_bf = ~ifc_region_acc_okay & ifc_fetch_req_bf;
   end
   else begin : g_ifc_access_check
      assign ifc_region_acc_okay = (~(|{pt.INST_ACCESS_ENABLE0,pt.INST_ACCESS_ENABLE1,pt.INST_ACCESS_ENABLE2,pt.INST_ACCESS_ENABLE3,pt.INST_ACCESS_ENABLE4,pt.INST_ACCESS_ENABLE5,pt.INST_ACCESS_ENABLE6,pt.INST_ACCESS_ENABLE7})) |
                                 (pt.INST_ACCESS_ENABLE0 & (({ifc_fetch_addr_bf[31:1],1'b0} | pt.INST_ACCESS_MASK0)) == (pt.INST_ACCESS_ADDR0 | pt.INST_ACCESS_MASK0)) |
                                 (pt.INST_ACCESS_ENABLE1 & (({ifc_fetch_addr_bf[31:1],1'b0} | pt.INST_ACCESS_MASK1)) == (pt.INST_ACCESS_ADDR1 | pt.INST_ACCESS_MASK1)) |
                                 (pt.INST_ACCESS_ENABLE2 & (({ifc_fetch_addr_bf[31:1],1'b0} | pt.INST_ACCESS_MASK2)) == (pt.INST_ACCESS_ADDR2 | pt.INST_ACCESS_MASK2)) |
                                 (pt.INST_ACCESS_ENABLE3 & (({ifc_fetch_addr_bf[31:1],1'b0} | pt.INST_ACCESS_MASK3)) == (pt.INST_ACCESS_ADDR3 | pt.INST_ACCESS_MASK3)) |
                                 (pt.INST_ACCESS_ENABLE4 & (({ifc_fetch_addr_bf[31:1],1'b0} | pt.INST_ACCESS_MASK4)) == (pt.INST_ACCESS_ADDR4 | pt.INST_ACCESS_MASK4)) |
                                 (pt.INST_ACCESS_ENABLE5 & (({ifc_fetch_addr_bf[31:1],1'b0} | pt.INST_ACCESS_MASK5)) == (pt.INST_ACCESS_ADDR5 | pt.INST_ACCESS_MASK5)) |
                                 (pt.INST_ACCESS_ENABLE6 & (({ifc_fetch_addr_bf[31:1],1'b0} | pt.INST_ACCESS_MASK6)) == (pt.INST_ACCESS_ADDR6 | pt.INST_ACCESS_MASK6)) |
                                 (pt.INST_ACCESS_ENABLE7 & (({ifc_fetch_addr_bf[31:1],1'b0} | pt.INST_ACCESS_MASK7)) == (pt.INST_ACCESS_ADDR7 | pt.INST_ACCESS_MASK7));
      assign ifc_region_acc_fault_memory_bf = ~ifc_iccm_access_bf & ~ifc_region_acc_okay & ifc_fetch_req_bf;
   end

   assign ifc_region_acc_fault_final_bf = ifc_region_acc_fault_bf | ifc_region_acc_fault_memory_bf;




endmodule  // el2_ifu_mem_ctl
