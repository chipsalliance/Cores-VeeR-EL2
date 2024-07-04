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
  localparam DCCM_ECC_WIDTH = pt.DCCM_FDATA_WIDTH - pt.DCCM_DATA_WIDTH;

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
  logic [pt.DCCM_NUM_BANKS-1:0][                  DCCM_ECC_WIDTH-1:0] dccm_wr_ecc_bank;
  logic [pt.DCCM_NUM_BANKS-1:0][              pt.DCCM_DATA_WIDTH-1:0] dccm_bank_dout;
  logic [pt.DCCM_NUM_BANKS-1:0][                  DCCM_ECC_WIDTH-1:0] dccm_bank_ecc;


  //////////////////////////////////////////
  // MODPORTS
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

endinterface
