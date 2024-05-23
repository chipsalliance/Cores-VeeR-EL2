// Copyright (c) 2024 Antmicro
// SPDX-License-Identifier: Apache-2.0
module el2_dec_ib_ctl_wrapper
  import el2_pkg::*;
#(
    `include "el2_param.vh"
) (
    input logic        dbg_cmd_valid,  // valid dbg cmd
    input logic        dbg_cmd_write,  // dbg cmd is write
    input logic [ 1:0] dbg_cmd_type,   // dbg type
    input logic [31:0] dbg_cmd_addr,   // expand to 31:0

    // Unpacked input el2_br_pkt_t i0_brp                           // i0 branch packet from aligner
    input logic i0_brp_valid,
    input logic [11:0] i0_brp_toffset,
    input logic [1:0] i0_brp_hist,
    input logic i0_brp_br_error,
    input logic i0_brp_br_start_error,
    input logic i0_brp_bank,
    input logic [31:1] i0_brp_prett,  // predicted ret target
    input logic i0_brp_way,
    input logic i0_brp_ret,

    input logic [pt.BTB_ADDR_HI:pt.BTB_ADDR_LO] ifu_i0_bp_index,  // BP index
    input logic [          pt.BHT_GHR_SIZE-1:0] ifu_i0_bp_fghr,   // BP FGHR
    input logic [         pt.BTB_BTAG_SIZE-1:0] ifu_i0_bp_btag,   // BP tag
    input logic [      $clog2(pt.BTB_SIZE)-1:0] ifu_i0_fa_index,  // Fully associt btb index

    input logic       ifu_i0_pc4,       // i0 is 4B inst else 2B
    input logic       ifu_i0_valid,     // i0 valid from ifu
    input logic       ifu_i0_icaf,      // i0 instruction access fault
    input logic [1:0] ifu_i0_icaf_type, // i0 instruction access fault type

    input logic        ifu_i0_icaf_second,  // i0 has access fault on second 2B of 4B inst
    input logic        ifu_i0_dbecc,        // i0 double-bit error
    input logic [31:0] ifu_i0_instr,        // i0 instruction from the aligner
    input logic [31:1] ifu_i0_pc,           // i0 pc from the aligner


    output logic dec_ib0_valid_d,   // ib0 valid
    output logic dec_debug_valid_d, // Debug read or write at D-stage


    output logic [31:0] dec_i0_instr_d,  // i0 inst at decode

    output logic [31:1] dec_i0_pc_d,  // i0 pc at decode

    output logic dec_i0_pc4_d,  // i0 is 4B inst else 2B

    // Unpacked output el2_br_pkt_t dec_i0_brp                      // i0 branch packet at decode
    output logic dec_i0_brp_valid,
    output logic [11:0] dec_i0_brp_toffset,
    output logic [1:0] dec_i0_brp_hist,
    output logic dec_i0_brp_br_error,
    output logic dec_i0_brp_br_start_error,
    output logic dec_i0_brp_bank,
    output logic [31:1] dec_i0_brp_prett,  // predicted ret target
    output logic dec_i0_brp_way,
    output logic dec_i0_brp_ret,

    output logic [pt.BTB_ADDR_HI:pt.BTB_ADDR_LO] dec_i0_bp_index,    // i0 branch index
    output logic [          pt.BHT_GHR_SIZE-1:0] dec_i0_bp_fghr,     // BP FGHR
    output logic [         pt.BTB_BTAG_SIZE-1:0] dec_i0_bp_btag,     // BP tag
    output logic [      $clog2(pt.BTB_SIZE)-1:0] dec_i0_bp_fa_index, // Fully associt btb index

    output logic dec_i0_icaf_d,  // i0 instruction access fault at decode
    output logic dec_i0_icaf_second_d,  // i0 instruction access fault on second 2B of 4B inst
    output logic [1:0] dec_i0_icaf_type_d,  // i0 instruction access fault type
    output logic dec_i0_dbecc_d,  // i0 double-bit error at decode
    output logic dec_debug_wdata_rs1_d,  // put debug write data onto rs1 source: machine is halted

    output logic dec_debug_fence_d  // debug fence inst
);

  el2_br_pkt_t i0_brp;
  el2_br_pkt_t dec_i0_brp;

  assign i0_brp.valid = i0_brp_valid;
  assign i0_brp.toffset = i0_brp_toffset;
  assign i0_brp.hist = i0_brp_hist;
  assign i0_brp.br_error = i0_brp_br_error;
  assign i0_brp.br_start_error = i0_brp_br_start_error;
  assign i0_brp.bank = i0_brp_bank;
  assign i0_brp.prett = i0_brp_prett;
  assign i0_brp.way = i0_brp_way;
  assign i0_brp.ret = i0_brp_ret;

  assign dec_i0_brp_valid = dec_i0_brp.valid;
  assign dec_i0_brp_toffset = dec_i0_brp.toffset;
  assign dec_i0_brp_hist = dec_i0_brp.hist;
  assign dec_i0_brp_br_error = dec_i0_brp.br_error;
  assign dec_i0_brp_br_start_error = dec_i0_brp.br_start_error;
  assign dec_i0_brp_bank = dec_i0_brp.bank;
  assign dec_i0_brp_prett = dec_i0_brp.prett;
  assign dec_i0_brp_way = dec_i0_brp.way;
  assign dec_i0_brp_ret = dec_i0_brp.ret;

  // The trigger unit
  el2_dec_ib_ctl tu (.*);

endmodule
