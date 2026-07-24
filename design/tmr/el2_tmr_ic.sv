// Copyright 2026 Antmicro <www.antmicro.com>
// //
// // SPDX-License-Identifier: Apache-2.0
//
//
module el2_tmr_ic
  import el2_pkg::*;
  import el2_mubi_pkg::*;
  import el2_lockstep_pkg::*;
#(
    `include "el2_param.vh"
) (
    // ICACHE
    output logic [31:1]                          ic_rw_addr,
    output logic [pt.ICACHE_NUM_WAYS-1:0]        ic_tag_valid,
    output logic [pt.ICACHE_NUM_WAYS-1:0]        ic_wr_en,
    output logic                                 ic_rd_en,

    output logic [pt.ICACHE_BANKS_WAY-1:0][70:0] ic_wr_data,         // Data to fill to the Icache. With ECC
    input  logic [141:0]                         ic_rd_data,              // Raw way-muxed 142-bit ECC-protected word pair. F2 stage.
    input  logic [1:0]                           ic_rd_addr_lo,            // F2-aligned ic_rw_addr_ff[2:1] for core-side rotate
    input  logic [pt.ICACHE_BANKS_WAY-1:0]       ic_rd_bank_check_en, // Per-bank ECC check enable for core-side decode
    input  logic [70:0]                          ic_debug_rd_data,        // Data read from Icache. 2x64bits + parity bits. F2 stage. With ECC
    input  logic [25:0]                          ictag_debug_rd_data,// Debug icache tag.
    output logic [70:0]                          ic_debug_wr_data,   // Debug wr cache.

    output logic [63:0]                          ic_premux_data,     // Premux data to be muxed with each way of the Icache.
    output logic                                 ic_sel_premux_data, // Select premux data

    output logic [pt.ICACHE_INDEX_HI:3]          ic_debug_addr,      // Read/Write address to the Icache.
    output logic                                 ic_debug_rd_en,     // Icache debug rd
    output logic                                 ic_debug_wr_en,     // Icache debug wr
    output logic                                 ic_debug_tag_array, // Debug tag array
    output logic [pt.ICACHE_NUM_WAYS-1:0]        ic_debug_way,       // Debug way. Rd or Wr.

    input  logic [pt.ICACHE_NUM_WAYS-1:0]        ic_rd_hit,
    input  logic                                 ic_tag_perr,        // Icache Tag parity error

    // ICACHE TMR
    input  logic [31:1]                          ic_rw_addr_veer[3],
    input  logic [pt.ICACHE_NUM_WAYS-1:0]        ic_tag_valid_veer[3],
    input  logic [pt.ICACHE_NUM_WAYS-1:0]        ic_wr_en_veer[3],
    input  logic                                 ic_rd_en_veer[3],

    input  logic [pt.ICACHE_BANKS_WAY-1:0][70:0] ic_wr_data_veer[3],
    output logic [141:0]                         ic_rd_data_veer[3],
    output logic [1:0]                           ic_rd_addr_lo_veer[3],
    output logic [pt.ICACHE_BANKS_WAY-1:0]       ic_rd_bank_check_en_veer[3],
    output logic [70:0]                          ic_debug_rd_data_veer[3],
    output logic [25:0]                          ictag_debug_rd_data_veer[3],
    input  logic [70:0]                          ic_debug_wr_data_veer[3],

    input  logic [63:0]                          ic_premux_data_veer[3],
    input  logic                                 ic_sel_premux_data_veer[3],

    input  logic [pt.ICACHE_INDEX_HI:3]          ic_debug_addr_veer[3],
    input  logic                                 ic_debug_rd_en_veer[3],
    input  logic                                 ic_debug_wr_en_veer[3],
    input  logic                                 ic_debug_tag_array_veer[3],
    input  logic [pt.ICACHE_NUM_WAYS-1:0]        ic_debug_way_veer[3],

    output logic [pt.ICACHE_NUM_WAYS-1:0]        ic_rd_hit_veer[3],
    output logic                                 ic_tag_perr_veer[3]
);

  //TODO: Change it to use voters

  always_comb begin
    // Propagate response to Cores
    for (int i=0;i < 3; i+=1) begin
      ic_rd_data_veer[i] = ic_rd_data;
      ic_rd_addr_lo_veer[i] = ic_rd_addr_lo;
      ic_rd_bank_check_en_veer[i] = ic_rd_bank_check_en;
      ic_debug_rd_data_veer[i] = ic_debug_rd_data;
      ictag_debug_rd_data_veer[i] = ictag_debug_rd_data;
      ic_rd_hit_veer[i] = ic_rd_hit;
      ic_tag_perr_veer[i] = ic_tag_perr;
    end
    // Get value from Core 0 for the time being
    ic_rw_addr = ic_rw_addr_veer[0];
    ic_tag_valid = ic_tag_valid_veer[0];
    ic_wr_en = ic_wr_en_veer[0];
    ic_rd_en = ic_rd_en_veer[0];
    ic_wr_data = ic_wr_data_veer[0];
    ic_debug_wr_data = ic_debug_wr_data_veer[0];
    ic_premux_data = ic_premux_data_veer[0];
    ic_sel_premux_data = ic_sel_premux_data_veer[0];
    ic_debug_addr = ic_debug_addr_veer[0];
    ic_debug_rd_en = ic_debug_rd_en_veer[0];
    ic_debug_wr_en = ic_debug_wr_en_veer[0];
    ic_debug_tag_array = ic_debug_tag_array_veer[0];
    ic_debug_way = ic_debug_way_veer[0];
  end

endmodule
