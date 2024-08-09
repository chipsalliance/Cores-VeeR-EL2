// Copyright (c) 2023 Antmicro
// SPDX-License-Identifier: Apache-2.0
module el2_lsu_trigger_wrapper
  import el2_pkg::*;
#(
    `include "el2_param.vh"
) (
    // Unpacked [3:0] trigger_pkt_t
    input logic [3:0] select,
    input logic [3:0] match,
    input logic [3:0] store,
    input logic [3:0] load,
    input logic [3:0] execute,
    input logic [3:0] m,

    input logic [31:0] tdata[4],

    // Fields from lsu_pkt_m relevant in this test
    // input logic lsu_word,
    // input logic lsu_half,
    // input logic lsu_dma,
    // input logic lsu_valid,
    // input logic lsu_store,

    input logic [31:0] lsu_addr_m,         // address
    input logic [31:0] store_data_m,       // store data

    output logic [3:0] lsu_trigger_match_m // match result
);

  // Pack triggers
  el2_trigger_pkt_t [3:0] trigger_pkt_any;
  for (genvar i = 0; i < 4; i++) begin : g_trigger_assigns
    assign trigger_pkt_any[i].select  = select[i];
    assign trigger_pkt_any[i].match   = match[i];
    assign trigger_pkt_any[i].store   = store[i];
    assign trigger_pkt_any[i].load    = load[i];
    assign trigger_pkt_any[i].execute = execute[i];
    assign trigger_pkt_any[i].m       = m[i];
    assign trigger_pkt_any[i].tdata2  = tdata[i];
  end

  // Pack lsu_pkt_m
  el2_lsu_pkt_t lsu_pkt_m;
  assign lsu_pkt_m.word  = 1; // lsu_word;
  assign lsu_pkt_m.half  = 1; // lsu_half;
  assign lsu_pkt_m.dma   = 0; // lsu_dma;
  assign lsu_pkt_m.valid = 1; // lsu_valid;
  assign lsu_pkt_m.store = 1; // lsu_store;

  // The trigger unit
  el2_lsu_trigger tu (
      .*
  );

endmodule
