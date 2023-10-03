// Copyright (c) 2023 Antmicro
// SPDX-License-Identifier: Apache-2.0
module el2_exu_div_ctl_wrapper
import el2_pkg::*;
#(
`include "el2_param.vh"
)
(
    input logic           clk,
    input logic           rst_l,
    input logic           scan_mode,

    // el2_div_pkt_t
    input logic           dp_valid,
    input logic           dp_unsign,
    input logic           dp_rem,

    input logic  [31:0]   dividend,
    input logic  [31:0]   divisor,

    input logic           cancel,

    output logic          finish_dly,
    output logic [31:0]   out
);

    // Pack el2_div_pkt_t
    el2_div_pkt_t dp;
    assign dp.valid  = dp_valid;
    assign dp.unsign = dp_unsign;
    assign dp.rem    = dp_rem;

    // The divider
    el2_exu_div_ctl div (.*);

endmodule
