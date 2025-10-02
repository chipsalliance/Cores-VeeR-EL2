//********************************************************************************
// SPDX-License-Identifier: Apache-2.0
// Copyright 2020 Western Digital Corporation or its affiliates.
// Copyright 2022 Microsoft Corporation
// Copyright (c) 2023 Antmicro <www.antmicro.com>
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


import el2_pkg::*;
interface el2_mem_if #(
    `include "el2_param.vh"
) ();
  //////////////////////////////////////////
  // Clock
  logic                                                               clk;


  //////////////////////////////////////////
  // ICCM
  logic [pt.ICCM_NUM_BANKS-1:0]                                       iccm_clken;
  logic [pt.ICCM_NUM_BANKS-1:0]                                       iccm_wren_bank;
  logic [pt.ICCM_NUM_BANKS-1:0][pt.ICCM_BITS-1:pt.ICCM_BANK_INDEX_LO] iccm_addr_bank;

  logic [pt.ICCM_NUM_BANKS-1:0][                                31:0] iccm_bank_wr_data;
  logic [pt.ICCM_NUM_BANKS-1:0][               pt.ICCM_ECC_WIDTH-1:0] iccm_bank_wr_ecc;
  logic [pt.ICCM_NUM_BANKS-1:0][                                31:0] iccm_bank_dout;
  logic [pt.ICCM_NUM_BANKS-1:0][               pt.ICCM_ECC_WIDTH-1:0] iccm_bank_ecc;


  //////////////////////////////////////////
  // DCCM
  logic [pt.DCCM_NUM_BANKS-1:0]                                       dccm_clken;
  logic [pt.DCCM_NUM_BANKS-1:0]                                       dccm_wren_bank;
  logic [pt.DCCM_NUM_BANKS-1:0][pt.DCCM_BITS-1:(pt.DCCM_BANK_BITS+2)] dccm_addr_bank;
  logic [pt.DCCM_NUM_BANKS-1:0][              pt.DCCM_DATA_WIDTH-1:0] dccm_wr_data_bank;
  logic [pt.DCCM_NUM_BANKS-1:0][               pt.DCCM_ECC_WIDTH-1:0] dccm_wr_ecc_bank;
  logic [pt.DCCM_NUM_BANKS-1:0][              pt.DCCM_DATA_WIDTH-1:0] dccm_bank_dout;
  logic [pt.DCCM_NUM_BANKS-1:0][               pt.DCCM_ECC_WIDTH-1:0] dccm_bank_ecc;

  //////////////////////////////////////////
  // ICACHE DATA
  logic [pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_NUM_WAYS-1:0]                       ic_b_sb_wren;
  logic [pt.ICACHE_BANKS_WAY-1:0][(71*pt.ICACHE_NUM_WAYS)-1:0]                  ic_b_sb_bit_en_vec;
  logic [pt.ICACHE_BANKS_WAY-1:0][(71*pt.ICACHE_NUM_WAYS)-1:0]                  wb_packeddout_pre;
  logic [pt.ICACHE_BANKS_WAY-1:0][70:0]                                         ic_sb_wr_data;
  logic [pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_INDEX_HI : pt.ICACHE_DATA_INDEX_LO] ic_rw_addr_bank_q;
  logic [pt.ICACHE_BANKS_WAY-1:0]                                               ic_bank_way_clken_final;
  logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0]                       ic_bank_way_clken_final_up;
  logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0][71-1:0]               wb_dout_pre_up;

  //////////////////////////////////////////
  // ICACHE TAG
  logic [pt.ICACHE_NUM_WAYS-1:0]                     ic_tag_clken_final;
  logic [pt.ICACHE_NUM_WAYS-1:0]                     ic_tag_wren_q;
  logic [(26*pt.ICACHE_NUM_WAYS)-1 :0]               ic_tag_wren_biten_vec;
  logic [(26*pt.ICACHE_NUM_WAYS)-1 :0]               ic_tag_data_raw_packed_pre;
  logic [25:0]                                       ic_tag_wr_data;
  logic [pt.ICACHE_INDEX_HI: pt.ICACHE_TAG_INDEX_LO] ic_rw_addr_q;
  logic [pt.ICACHE_NUM_WAYS-1:0] [25:0]              ic_tag_data_raw_pre;

  //////////////////////////////////////////
  // MODPORTS
  // Complete modport
  modport veer_sram_icache_src(
      output clk,
      // ICCM
      output iccm_clken, iccm_wren_bank, iccm_addr_bank, iccm_bank_wr_data, iccm_bank_wr_ecc,
      input iccm_bank_dout, iccm_bank_ecc,
      // DCCM
      output dccm_clken, dccm_wren_bank, dccm_addr_bank, dccm_wr_data_bank, dccm_wr_ecc_bank,
      input dccm_bank_dout, dccm_bank_ecc,
      // ICACHE data
      output ic_b_sb_wren, ic_b_sb_bit_en_vec, ic_sb_wr_data, ic_rw_addr_bank_q, ic_bank_way_clken_final, ic_bank_way_clken_final_up,
      input wb_packeddout_pre, wb_dout_pre_up,
      // ICACHE tag
      output ic_tag_clken_final, ic_tag_wren_q, ic_tag_wren_biten_vec, ic_tag_wr_data, ic_rw_addr_q,
      input ic_tag_data_raw_packed_pre, ic_tag_data_raw_pre
  );

  modport veer_iccm(
      input clk,
      // ICCM
      output iccm_clken, iccm_wren_bank, iccm_addr_bank, iccm_bank_wr_data, iccm_bank_wr_ecc,
      input iccm_bank_dout, iccm_bank_ecc
  );

  modport veer_dccm(
      input clk,
      // DCCM
      output dccm_clken, dccm_wren_bank, dccm_addr_bank, dccm_wr_data_bank, dccm_wr_ecc_bank,
      input dccm_bank_dout, dccm_bank_ecc
  );

  modport veer_sram_src(
      output clk,
      // ICCM
      output iccm_clken, iccm_wren_bank, iccm_addr_bank, iccm_bank_wr_data, iccm_bank_wr_ecc,
      input iccm_bank_dout, iccm_bank_ecc,
      // DCCM
      output dccm_clken, dccm_wren_bank, dccm_addr_bank, dccm_wr_data_bank, dccm_wr_ecc_bank,
      input dccm_bank_dout, dccm_bank_ecc
  );

  modport veer_sram_sink(
      input clk,
      // ICCM
      input iccm_clken, iccm_wren_bank, iccm_addr_bank, iccm_bank_wr_data, iccm_bank_wr_ecc,
      output iccm_bank_dout, iccm_bank_ecc,
      // DCCM
      input dccm_clken, dccm_wren_bank, dccm_addr_bank, dccm_wr_data_bank, dccm_wr_ecc_bank,
      output dccm_bank_dout, dccm_bank_ecc
  );

  modport veer_icache_data(
      // data
      output ic_b_sb_wren, ic_b_sb_bit_en_vec, ic_sb_wr_data, ic_rw_addr_bank_q, ic_bank_way_clken_final, ic_bank_way_clken_final_up,
      input wb_packeddout_pre, wb_dout_pre_up
  );

  modport veer_icache_tag(
      // tag
      output ic_tag_clken_final, ic_tag_wren_q, ic_tag_wren_biten_vec, ic_tag_wr_data, ic_rw_addr_q,
      input ic_tag_data_raw_packed_pre,ic_tag_data_raw_pre
  );

  modport veer_icache_src(
      // cache uses the same clk as sram, we do not define clk port in this modport,
      // assuming the clk will be connected in sram_src
      // data
      output ic_b_sb_wren, ic_b_sb_bit_en_vec, ic_sb_wr_data, ic_rw_addr_bank_q, ic_bank_way_clken_final, ic_bank_way_clken_final_up,
      input wb_packeddout_pre, wb_dout_pre_up,
      // tag
      output ic_tag_clken_final, ic_tag_wren_q, ic_tag_wren_biten_vec, ic_tag_wr_data, ic_rw_addr_q,
      input ic_tag_data_raw_packed_pre,ic_tag_data_raw_pre
  );

endinterface
