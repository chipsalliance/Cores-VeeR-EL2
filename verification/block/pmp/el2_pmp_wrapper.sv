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

    input el2_pmp_cfg_pkt_t        pmp_pmpcfg [pt.PMP_ENTRIES],
    input logic             [31:0] pmp_pmpaddr[pt.PMP_ENTRIES],

    input  logic              [            31:0] pmp_chan_addr[PMP_CHANNELS],
    input  el2_pmp_type_pkt_t                    pmp_chan_type[PMP_CHANNELS],
    output logic              [0:PMP_CHANNELS-1] pmp_chan_err
);
  logic pmp_chan_err_unpacked[PMP_CHANNELS];

  for (genvar c = 0; c < PMP_CHANNELS; c++) begin
    assign pmp_chan_err[c] = pmp_chan_err_unpacked[c];
  end

  // The PMP module
  el2_pmp pmp (
      .pmp_chan_err(pmp_chan_err_unpacked),
      .*
  );

endmodule
