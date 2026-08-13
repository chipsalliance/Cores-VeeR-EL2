// Copyright 2026 Antmicro <www.antmicro.com>
//
// SPDX-License-Identifier: Apache-2.0
//
module tmr_ic_wrapper
  import el2_pkg::*;
  import el2_mubi_pkg::*;
#(
    `include "el2_param.vh"
) (
    input logic clk,
    input  logic rst_l,

    // I-Cache Memory
    output logic [pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_NUM_WAYS-1:0]                       ic_b_sb_wren,
    output logic [pt.ICACHE_BANKS_WAY-1:0][(71*pt.ICACHE_NUM_WAYS)-1:0]                  ic_b_sb_bit_en_vec,
    output logic [pt.ICACHE_BANKS_WAY-1:0][70:0]                                         ic_sb_wr_data,
    output logic [pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_INDEX_HI : pt.ICACHE_DATA_INDEX_LO] ic_rw_addr_bank_q,
    output logic [pt.ICACHE_BANKS_WAY-1:0]                                               ic_bank_way_clken_final,
    output logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0]                       ic_bank_way_clken_final_up,
    input  logic [pt.ICACHE_BANKS_WAY-1:0][(71*pt.ICACHE_NUM_WAYS)-1:0]                  wb_packeddout_pre,
    input  logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0][71-1:0]               wb_dout_pre_up,

    output logic [pt.ICACHE_NUM_WAYS-1:0]                     ic_tag_clken_final,
    output logic [pt.ICACHE_NUM_WAYS-1:0]                     ic_tag_wren_q,
    output logic [(26*pt.ICACHE_NUM_WAYS)-1 :0]               ic_tag_wren_biten_vec,
    output logic [25:0]                                       ic_tag_wr_data,
    output logic [pt.ICACHE_INDEX_HI: pt.ICACHE_TAG_INDEX_LO] ic_rw_addr_q,
    input  logic [(26*pt.ICACHE_NUM_WAYS)-1 :0]               ic_tag_data_raw_packed_pre,
    input  logic [pt.ICACHE_NUM_WAYS-1:0] [25:0]              ic_tag_data_raw_pre,

    // I-Cache TMR
    input  logic [pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_NUM_WAYS-1:0]                       ic_b_sb_wren_veer[3],
    input  logic [pt.ICACHE_BANKS_WAY-1:0][(71*pt.ICACHE_NUM_WAYS)-1:0]                  ic_b_sb_bit_en_vec_veer[3],
    input  logic [pt.ICACHE_BANKS_WAY-1:0][70:0]                                         ic_sb_wr_data_veer[3],
    input  logic [pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_INDEX_HI : pt.ICACHE_DATA_INDEX_LO] ic_rw_addr_bank_q_veer[3],
    input  logic [pt.ICACHE_BANKS_WAY-1:0]                                               ic_bank_way_clken_final_veer[3],
    input  logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0]                       ic_bank_way_clken_final_up_veer[3],
    output logic [pt.ICACHE_BANKS_WAY-1:0][(71*pt.ICACHE_NUM_WAYS)-1:0]                  wb_packeddout_pre_veer[3],
    output logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0][71-1:0]               wb_dout_pre_up_veer[3],

    input  logic [pt.ICACHE_NUM_WAYS-1:0]                     ic_tag_clken_final_veer[3],
    input  logic [pt.ICACHE_NUM_WAYS-1:0]                     ic_tag_wren_q_veer[3],
    input  logic [(26*pt.ICACHE_NUM_WAYS)-1 :0]               ic_tag_wren_biten_vec_veer[3],
    input  logic [25:0]                                       ic_tag_wr_data_veer[3],
    input  logic [pt.ICACHE_INDEX_HI: pt.ICACHE_TAG_INDEX_LO] ic_rw_addr_q_veer[3],
    output logic [(26*pt.ICACHE_NUM_WAYS)-1 :0]               ic_tag_data_raw_packed_pre_veer[3],
    output logic [pt.ICACHE_NUM_WAYS-1:0] [25:0]              ic_tag_data_raw_pre_veer[3],

    // Fault inputs
    input  el2_mubi_pkg::el2_mubi_t ic_fault_d[3],
    // Fault outputs
    output el2_mubi_pkg::el2_mubi_t ic_fault_q[3],
    // Fault clear inputs
    input  el2_mubi_pkg::el2_mubi_t ic_fault_clr[3]
);

  el2_mem_if local_mem_export();
  el2_mem_if local_mem_export_veer[3]();

  // I-Cache data
  assign ic_b_sb_wren               = local_mem_export.ic_b_sb_wren;
  assign ic_b_sb_bit_en_vec         = local_mem_export.ic_b_sb_bit_en_vec;
  assign ic_sb_wr_data              = local_mem_export.ic_sb_wr_data;
  assign ic_rw_addr_bank_q          = local_mem_export.ic_rw_addr_bank_q;
  assign ic_bank_way_clken_final    = local_mem_export.ic_bank_way_clken_final;
  assign ic_bank_way_clken_final_up = local_mem_export.ic_bank_way_clken_final_up;
  assign local_mem_export.wb_packeddout_pre = wb_packeddout_pre;
  assign local_mem_export.wb_dout_pre_up    = wb_dout_pre_up;

  // I-Cache tag
  assign ic_tag_clken_final         = local_mem_export.ic_tag_clken_final;
  assign ic_tag_wren_q              = local_mem_export.ic_tag_wren_q;
  assign ic_tag_wren_biten_vec      = local_mem_export.ic_tag_wren_biten_vec;
  assign ic_tag_wr_data             = local_mem_export.ic_tag_wr_data;
  assign ic_rw_addr_q               = local_mem_export.ic_rw_addr_q;
  assign local_mem_export.ic_tag_data_raw_packed_pre = ic_tag_data_raw_packed_pre;
  assign local_mem_export.ic_tag_data_raw_pre        = ic_tag_data_raw_pre;

  // I-Cache TMR
  for(genvar i = 0; i < 3; i++) begin
    // I-Cache data
    assign local_mem_export_veer[i].ic_b_sb_wren               = ic_b_sb_wren_veer[i];
    assign local_mem_export_veer[i].ic_b_sb_bit_en_vec         = ic_b_sb_bit_en_vec_veer[i];
    assign local_mem_export_veer[i].ic_sb_wr_data              = ic_sb_wr_data_veer[i];
    assign local_mem_export_veer[i].ic_rw_addr_bank_q          = ic_rw_addr_bank_q_veer[i];
    assign local_mem_export_veer[i].ic_bank_way_clken_final    = ic_bank_way_clken_final_veer[i];
    assign local_mem_export_veer[i].ic_bank_way_clken_final_up = ic_bank_way_clken_final_up_veer[i];
    assign wb_packeddout_pre_veer[i] = local_mem_export_veer[i].wb_packeddout_pre;
    assign wb_dout_pre_up_veer[i]    = local_mem_export_veer[i].wb_dout_pre_up;

    // I-Cache tag
    assign local_mem_export_veer[i].ic_tag_clken_final    = ic_tag_clken_final_veer[i];
    assign local_mem_export_veer[i].ic_tag_wren_q         = ic_tag_wren_q_veer[i];
    assign local_mem_export_veer[i].ic_tag_wren_biten_vec = ic_tag_wren_biten_vec_veer[i];
    assign local_mem_export_veer[i].ic_tag_wr_data        = ic_tag_wr_data_veer[i];
    assign local_mem_export_veer[i].ic_rw_addr_q          = ic_rw_addr_q_veer[i];
    assign ic_tag_data_raw_packed_pre_veer[i] = local_mem_export_veer[i].ic_tag_data_raw_packed_pre;
    assign ic_tag_data_raw_pre_veer[i]        = local_mem_export_veer[i].ic_tag_data_raw_pre;
  end

  el2_tmr_ic #(.pt(pt)) u_el2_tmr_ic (
    .icache_export(local_mem_export.veer_icache_src),
    .icache_export_veer(local_mem_export_veer.veer_icache_sink),
    .*
  );
endmodule
