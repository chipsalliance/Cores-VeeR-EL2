// Copyright (c) 2023 Antmicro
// SPDX-License-Identifier: Apache-2.0

module el2_pmp_wrapper
  import el2_pkg::*;
#(
    parameter PMP_CHANNELS = 3,
    `include "el2_param.vh"
) (
    input logic clk,       // Top level clock
    input logic rst_l,     // Reset
    input logic scan_mode, // Scan mode

    input                   [7:0]  pmp_pmpcfg [pt.PMP_ENTRIES],
    input logic             [31:0] pmp_pmpaddr[pt.PMP_ENTRIES],

    input  logic              [            31:0] pmp_chan_addr[PMP_CHANNELS],
    input  el2_pmp_type_pkt_t                    pmp_chan_type[PMP_CHANNELS],
    output logic              [0:PMP_CHANNELS-1] pmp_chan_err
);
  logic pmp_chan_err_unpacked[PMP_CHANNELS];
  el2_pmp_cfg_pkt_t pmp_pmpcfg_int [pt.PMP_ENTRIES];

  for (genvar c = 0; c < PMP_CHANNELS; c++) begin
    assign pmp_chan_err[c] = pmp_chan_err_unpacked[c];
  end

  for (genvar e = 0; e < pt.PMP_ENTRIES; e++) begin
    assign pmp_pmpcfg_int[e].lock = pmp_pmpcfg[e][7];
    assign pmp_pmpcfg_int[e].reserved = pmp_pmpcfg[e][6:5];
    assign pmp_pmpcfg_int[e].mode = el2_pkg::el2_pmp_mode_pkt_t'(pmp_pmpcfg[e][4:3]);
    assign pmp_pmpcfg_int[e].execute = pmp_pmpcfg[e][2];
    assign pmp_pmpcfg_int[e].write = pmp_pmpcfg[e][1];
    assign pmp_pmpcfg_int[e].read= pmp_pmpcfg[e][0];
  end

  // The PMP module
  el2_pmp pmp (
      .pmp_chan_err(pmp_chan_err_unpacked),
      .pmp_pmpcfg(pmp_pmpcfg_int),
      .*
  );

endmodule
