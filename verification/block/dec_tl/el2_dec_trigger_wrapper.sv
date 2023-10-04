// Copyright (c) 2023 Antmicro
// SPDX-License-Identifier: Apache-2.0
module el2_dec_trigger_wrapper
  import el2_pkg::*;
#(
    `include "el2_param.vh"
) (
    input logic [31:1] dec_i0_pc_d,

    // Unpacked [3:0] trigger_pkt_t
    input logic [3:0] select,
    input logic [3:0] match,
    input logic [3:0] store,
    input logic [3:0] load,
    input logic [3:0] execute,
    input logic [3:0] m,

    input logic [31:0] tdata[4],

    output logic [3:0] dec_i0_trigger_match_d
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

  // The trigger unit
  el2_dec_trigger tu (
      .dec_i0_pc_d(dec_i0_pc_d[31:1]),
      .*
  );

endmodule
