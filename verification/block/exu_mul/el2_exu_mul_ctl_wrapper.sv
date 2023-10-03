// Copyright (c) 2023 Antmicro
// SPDX-License-Identifier: Apache-2.0
module el2_exu_mul_ctl_wrapper
import el2_pkg::*;
#(
`include "el2_param.vh"
)
(
    input  logic        clk,
    input  logic        rst_l,
    input  logic        scan_mode,

    // Unpacked mul_p
    input  logic        mul_p_valid,
    input  logic        mul_p_rs1_sign,
    input  logic        mul_p_rs2_sign,
    input  logic        mul_p_low,
    input  logic        mul_p_bcompress,
    input  logic        mul_p_bdecompress,
    input  logic        mul_p_clmul,
    input  logic        mul_p_clmulh,
    input  logic        mul_p_clmulr,
    input  logic        mul_p_grev,
    input  logic        mul_p_gorc,
    input  logic        mul_p_shfl,
    input  logic        mul_p_unshfl,
    input  logic        mul_p_crc32_b,
    input  logic        mul_p_crc32_h,
    input  logic        mul_p_crc32_w,
    input  logic        mul_p_crc32c_b,
    input  logic        mul_p_crc32c_h,
    input  logic        mul_p_crc32c_w,
    input  logic        mul_p_bfp,
    input  logic        mul_p_xperm_n,
    input  logic        mul_p_xperm_b,
    input  logic        mul_p_xperm_h,

    input  logic [31:0] rs1_in,
    input  logic [31:0] rs2_in,

    output logic [31:0] result_x
);

    // Pack mul_p
    el2_mul_pkt_t mul_p;
    assign mul_p.valid       = mul_p_valid;
    assign mul_p.rs1_sign    = mul_p_rs1_sign;
    assign mul_p.rs2_sign    = mul_p_rs2_sign;
    assign mul_p.low         = mul_p_low;
    assign mul_p.bcompress   = mul_p_bcompress;
    assign mul_p.bdecompress = mul_p_bdecompress;
    assign mul_p.clmul       = mul_p_clmul;
    assign mul_p.clmulh      = mul_p_clmulh;
    assign mul_p.clmulr      = mul_p_clmulr;
    assign mul_p.grev        = mul_p_grev;
    assign mul_p.gorc        = mul_p_gorc;
    assign mul_p.shfl        = mul_p_shfl;
    assign mul_p.unshfl      = mul_p_unshfl;
    assign mul_p.crc32_b     = mul_p_crc32_b;
    assign mul_p.crc32_h     = mul_p_crc32_h;
    assign mul_p.crc32_w     = mul_p_crc32_w;
    assign mul_p.crc32c_b    = mul_p_crc32c_b;
    assign mul_p.crc32c_h    = mul_p_crc32c_h;
    assign mul_p.crc32c_w    = mul_p_crc32c_w;
    assign mul_p.bfp         = mul_p_bfp;
    assign mul_p.xperm_n     = mul_p_xperm_n;
    assign mul_p.xperm_b     = mul_p_xperm_b;
    assign mul_p.xperm_h     = mul_p_xperm_h;

    // The multiplier
    el2_exu_mul_ctl mul (.*);

endmodule
