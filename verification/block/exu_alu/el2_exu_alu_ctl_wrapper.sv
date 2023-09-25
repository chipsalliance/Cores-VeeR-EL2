// Copyright (c) 2023 Antmicro
// SPDX-License-Identifier: Apache-2.0
module el2_exu_alu_ctl_wrapper
import el2_pkg::*;
#(
`include "el2_param.vh"
)
(
    input  logic                  clk,
    input  logic                  rst_l,
    input  logic                  scan_mode,
 
    input  logic                  flush_upper_x,
    input  logic                  flush_lower_r,
    input  logic                  enable,
    input  logic                  valid_in,
 
    // Unpacked el2_alu_pkt_t
    input  logic                  ap_clz,
    input  logic                  ap_ctz,
    input  logic                  ap_cpop,
    input  logic                  ap_sext_b,
    input  logic                  ap_sext_h,
    input  logic                  ap_min,
    input  logic                  ap_max,
    input  logic                  ap_pack,
    input  logic                  ap_packu,
    input  logic                  ap_packh,
    input  logic                  ap_rol,
    input  logic                  ap_ror,
    input  logic                  ap_grev,
    input  logic                  ap_gorc,
    input  logic                  ap_zbb,
    input  logic                  ap_bset,
    input  logic                  ap_bclr,
    input  logic                  ap_binv,
    input  logic                  ap_bext,
    input  logic                  ap_sh1add,
    input  logic                  ap_sh2add,
    input  logic                  ap_sh3add,
    input  logic                  ap_zba,
    input  logic                  ap_land,
    input  logic                  ap_lor,
    input  logic                  ap_lxor,
    input  logic                  ap_sll,
    input  logic                  ap_srl,
    input  logic                  ap_sra,
    input  logic                  ap_beq,
    input  logic                  ap_bne,
    input  logic                  ap_blt,
    input  logic                  ap_bge,
    input  logic                  ap_add,
    input  logic                  ap_sub,
    input  logic                  ap_slt,
    input  logic                  ap_unsignl,
    input  logic                  ap_jall,
    input  logic                  ap_predict_tl,
    input  logic                  ap_predict_nt,
    input  logic                  ap_csr_write,
    input  logic                  ap_csr_imm,
 
    input  logic                  csr_ren_in,
    input  logic        [31:0]    csr_rddata_in,
    input  logic signed [31:0]    a_in,
    input  logic        [31:0]    b_in,
    input  logic        [31:1]    pc_in,
    input  el2_predict_pkt_t      pp_in,
    input  logic        [12:1]    brimm_in,
 
 
    output logic        [31:0]    result_ff,
    output logic                  flush_upper_out,
    output logic                  flush_final_out,
    output logic        [31:1]    flush_path_out,
    output logic        [31:1]    pc_ff,
    output logic                  pred_correct_out,
    output el2_predict_pkt_t      predict_p_out
);

    // Pack ap
    el2_alu_pkt_t ap;
    assign ap.clz        = ap_clz;
    assign ap.ctz        = ap_ctz;
    assign ap.cpop       = ap_cpop;
    assign ap.sext_b     = ap_sext_b;
    assign ap.sext_h     = ap_sext_h;
    assign ap.min        = ap_min;
    assign ap.max        = ap_max;
    assign ap.pack       = ap_pack;
    assign ap.packu      = ap_packu;
    assign ap.packh      = ap_packh;
    assign ap.rol        = ap_rol;
    assign ap.ror        = ap_ror;
    assign ap.grev       = ap_grev;
    assign ap.gorc       = ap_gorc;
    assign ap.zbb        = ap_zbb;
    assign ap.bset       = ap_bset;
    assign ap.bclr       = ap_bclr;
    assign ap.binv       = ap_binv;
    assign ap.bext       = ap_bext;
    assign ap.sh1add     = ap_sh1add;
    assign ap.sh2add     = ap_sh2add;
    assign ap.sh3add     = ap_sh3add;
    assign ap.zba        = ap_zba;
    assign ap.land       = ap_land;
    assign ap.lor        = ap_lor;
    assign ap.lxor       = ap_lxor;
    assign ap.sll        = ap_sll;
    assign ap.srl        = ap_srl;
    assign ap.sra        = ap_sra;
    assign ap.beq        = ap_beq;
    assign ap.bne        = ap_bne;
    assign ap.blt        = ap_blt;
    assign ap.bge        = ap_bge;
    assign ap.add        = ap_add;
    assign ap.sub        = ap_sub;
    assign ap.slt        = ap_slt;
    assign ap.unsign     = ap_unsignl;
    assign ap.jal        = ap_jall;
    assign ap.predict_t  = ap_predict_tl;
    assign ap.predict_nt = ap_predict_nt;
    assign ap.csr_write  = ap_csr_write;
    assign ap.csr_imm    = ap_csr_imm;

    // EXU ALU
    el2_exu_alu_ctl alu (.*);

endmodule

