// SPDX-License-Identifier: Apache-2.0
// Copyright 2020 Western Digital Corporation or its affiliates.
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

module el2_dec_ib_ctl
import el2_pkg::*;
#(
`include "el2_param.vh"
 )
  (
   input logic                 dbg_cmd_valid,                      // valid dbg cmd

   input logic                 dbg_cmd_write,                      // dbg cmd is write
   input logic [1:0]           dbg_cmd_type,                       // dbg type
   input logic [31:0]          dbg_cmd_addr,                       // expand to 31:0

   input el2_br_pkt_t i0_brp,                                     // i0 branch packet from aligner
   input logic [pt.BTB_ADDR_HI:pt.BTB_ADDR_LO] ifu_i0_bp_index,    // BP index
   input logic [pt.BHT_GHR_SIZE-1:0] ifu_i0_bp_fghr,               // BP FGHR
   input logic [pt.BTB_BTAG_SIZE-1:0] ifu_i0_bp_btag,              // BP tag
   input logic [$clog2(pt.BTB_SIZE)-1:0] ifu_i0_fa_index,          // Fully associt btb index

   input logic       ifu_i0_pc4,                                   // i0 is 4B inst else 2B
   input logic       ifu_i0_valid,                                 // i0 valid from ifu
   input logic       ifu_i0_icaf,                                  // i0 instruction access fault
   input logic [1:0] ifu_i0_icaf_type,                             // i0 instruction access fault type

   input logic   ifu_i0_icaf_second,                               // i0 has access fault on second 2B of 4B inst
   input logic   ifu_i0_dbecc,                                     // i0 double-bit error
   input logic [31:0]  ifu_i0_instr,                               // i0 instruction from the aligner
   input logic [31:1]  ifu_i0_pc,                                  // i0 pc from the aligner


   output logic dec_ib0_valid_d,                                   // ib0 valid
   output logic dec_debug_valid_d,                                 // Debug read or write at D-stage


   output logic [31:0] dec_i0_instr_d,                             // i0 inst at decode

   output logic [31:1] dec_i0_pc_d,                                // i0 pc at decode

   output logic dec_i0_pc4_d,                                      // i0 is 4B inst else 2B

   output el2_br_pkt_t dec_i0_brp,                                // i0 branch packet at decode
   output logic [pt.BTB_ADDR_HI:pt.BTB_ADDR_LO] dec_i0_bp_index,   // i0 branch index
   output logic [pt.BHT_GHR_SIZE-1:0] dec_i0_bp_fghr,              // BP FGHR
   output logic [pt.BTB_BTAG_SIZE-1:0] dec_i0_bp_btag,             // BP tag
   output logic [$clog2(pt.BTB_SIZE)-1:0] dec_i0_bp_fa_index,          // Fully associt btb index

   output logic dec_i0_icaf_d,                                     // i0 instruction access fault at decode
   output logic dec_i0_icaf_second_d,                              // i0 instruction access fault on second 2B of 4B inst
   output logic [1:0] dec_i0_icaf_type_d,                          // i0 instruction access fault type
   output logic dec_i0_dbecc_d,                                    // i0 double-bit error at decode
   output logic dec_debug_wdata_rs1_d,                             // put debug write data onto rs1 source: machine is halted

   output logic dec_debug_fence_d                                  // debug fence inst

   );


   logic         debug_valid;
   logic [4:0]   dreg;
   logic [11:0]  dcsr;
   logic [31:0]  ib0, ib0_debug_in;

   logic         debug_read;
   logic         debug_write;
   logic         debug_read_gpr;
   logic         debug_write_gpr;
   logic         debug_read_csr;
   logic         debug_write_csr;

   logic [34:0]  ifu_i0_pcdata, pc0;

   assign ifu_i0_pcdata[34:0] = { ifu_i0_icaf_second, ifu_i0_dbecc, ifu_i0_icaf,
                                  ifu_i0_pc[31:1], ifu_i0_pc4 };

   assign pc0[34:0] = ifu_i0_pcdata[34:0];

   assign dec_i0_icaf_second_d = pc0[34];   // icaf's can only decode as i0

   assign dec_i0_dbecc_d = pc0[33];

   assign dec_i0_icaf_d = pc0[32];
   assign dec_i0_pc_d[31:1] = pc0[31:1];
   assign dec_i0_pc4_d = pc0[0];

   assign dec_i0_icaf_type_d[1:0] = ifu_i0_icaf_type[1:0];

// GPR accesses

// put reg to read on rs1
// read ->   or %x0,  %reg,%x0      {000000000000,reg[4:0],110000000110011}

// put write date on rs1
// write ->  or %reg, %x0, %x0      {00000000000000000110,reg[4:0],0110011}


// CSR accesses
// csr is of form rd, csr, rs1

// read  -> csrrs %x0, %csr, %x0     {csr[11:0],00000010000001110011}

// put write data on rs1
// write -> csrrw %x0, %csr, %x0     {csr[11:0],00000001000001110011}

// abstract memory command not done here
   assign debug_valid = dbg_cmd_valid & (dbg_cmd_type[1:0] != 2'h2);


   assign debug_read  = debug_valid & ~dbg_cmd_write;
   assign debug_write = debug_valid &  dbg_cmd_write;

   assign debug_read_gpr  = debug_read  & (dbg_cmd_type[1:0]==2'h0);
   assign debug_write_gpr = debug_write & (dbg_cmd_type[1:0]==2'h0);
   assign debug_read_csr  = debug_read  & (dbg_cmd_type[1:0]==2'h1);
   assign debug_write_csr = debug_write & (dbg_cmd_type[1:0]==2'h1);

   assign dreg[4:0]  = dbg_cmd_addr[4:0];
   assign dcsr[11:0] = dbg_cmd_addr[11:0];


   assign ib0_debug_in[31:0] = ({32{debug_read_gpr}}  & {12'b000000000000,dreg[4:0],15'b110000000110011}) |
                               ({32{debug_write_gpr}} & {20'b00000000000000000110,dreg[4:0],7'b0110011}) |
                               ({32{debug_read_csr}}  & {dcsr[11:0],20'b00000010000001110011}) |
                               ({32{debug_write_csr}} & {dcsr[11:0],20'b00000001000001110011});



   // machine is in halted state, pipe empty, write will always happen next cycle

   assign dec_debug_wdata_rs1_d = debug_write_gpr | debug_write_csr;


   // special fence csr for use only in debug mode

   assign dec_debug_fence_d = debug_write_csr & (dcsr[11:0] == 12'h7c4);

   assign ib0[31:0] = (debug_valid) ? ib0_debug_in[31:0] : ifu_i0_instr[31:0];

   assign dec_ib0_valid_d = ifu_i0_valid | debug_valid;

   assign dec_debug_valid_d = debug_valid;

   assign dec_i0_instr_d[31:0] = ib0[31:0];

   assign dec_i0_brp = i0_brp;
   assign dec_i0_bp_index = ifu_i0_bp_index;
   assign dec_i0_bp_fghr = ifu_i0_bp_fghr;
   assign dec_i0_bp_btag = ifu_i0_bp_btag;
   assign dec_i0_bp_fa_index = ifu_i0_fa_index;

endmodule
