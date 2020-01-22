// SPDX-License-Identifier: Apache-2.0
// Copyright 2020 Western Digital Corporation or it's affiliates.
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


module el2_exu_alu_ctl
import el2_pkg::*;
#(
`include "el2_param.vh"
)
  (
   input  logic                  clk,                // Top level clock
   input  logic                  rst_l,              // Reset
   input  logic                  scan_mode,          // Scan control

   input  logic                  flush_upper_x,      // Branch flush from previous cycle
   input  logic                  flush_lower_r,      // Master flush of entire pipeline
   input  logic                  enable,             // Clock enable
   input  logic                  valid_in,           // Valid
   input  el2_alu_pkt_t         ap,                 // predecodes
   input  logic                  csr_ren_in,         // extra decode
   input  logic signed [31:0]    a_in,               // A operand
   input  logic        [31:0]    b_in,               // B operand
   input  logic        [31:1]    pc_in,              // for pc=pc+2,4 calculations
   input  el2_predict_pkt_t     pp_in,              // Predicted branch structure
   input  logic        [12:1]    brimm_in,           // Branch offset


   output logic        [31:0]    result_ff,          // final result
   output logic                  flush_upper_out,    // Branch flush
   output logic                  flush_final_out,    // Branch flush or flush entire pipeline
   output logic        [31:1]    flush_path_out,     // Branch flush PC
   output logic        [31:1]    pc_ff,              // flopped PC
   output logic                  pred_correct_out,   // NPC control
   output el2_predict_pkt_t     predict_p_out       // Predicted branch structure
  );


   logic               [31:0]    aout;
   logic                         cout,ov,neg;
   logic               [31:0]    lout;
   logic               [5:0]     shift_amount;
   logic               [31:0]    shift_mask;
   logic               [62:0]    shift_extend;
   logic               [62:0]    shift_long;
   logic               [31:0]    sout;
   logic                         sel_shift;
   logic                         sel_adder;
   logic                         slt_one;
   logic                         actual_taken;
   logic               [31:1]    pcout;
   logic                         cond_mispredict;
   logic                         target_mispredict;
   logic                         eq, ne, lt, ge;
   logic                         any_jal;
   logic               [1:0]     newhist;
   logic                         sel_pc;
   logic               [31:0]    csr_write_data;
   logic               [31:0]    result;






   rvdffe #(31) i_pc_ff       (.*, .en(enable),   .din(pc_in[31:1]),    .dout(pc_ff[31:1]));   // any PC is run through here - doesn't have to be alu
   rvdffe #(32) i_result_ff   (.*, .en(enable),   .din(result[31:0]),   .dout(result_ff[31:0]));



   // immediates are just muxed into rs2

   // add    =>  add=1;
   // sub    =>  add=1; sub=1;

   // and    =>  lctl=3
   // or     =>  lctl=2
   // xor    =>  lctl=1

   // sll    =>  sctl=3
   // srl    =>  sctl=2
   // sra    =>  sctl=1

   // slt    =>  slt

   // lui    =>  lctl=2; or x0, imm20 previously << 12
   // auipc  =>  add;   add pc, imm20 previously << 12

   // beq    =>  bctl=4; add; add x0, pc, sext(offset[12:1])
   // bne    =>  bctl=3; add; add x0, pc, sext(offset[12:1])
   // blt    =>  bctl=2; add; add x0, pc, sext(offset[12:1])
   // bge    =>  bctl=1; add; add x0, pc, sext(offset[12:1])

   // jal    =>  rs1=pc {pc[31:1],1'b0},  rs2=sext(offset20:1]);   rd=pc+[2,4]
   // jalr   =>  rs1=rs1,                 rs2=sext(offset20:1]);   rd=pc+[2,4]


   logic        [31:0]    bm;

   assign bm[31:0]            = ( ap.sub )  ?  ~b_in[31:0]  :  b_in[31:0];

   assign {cout, aout[31:0]}  = {1'b0, a_in[31:0]} + {1'b0, bm[31:0]} + {32'b0, ap.sub};

   assign ov                  = (~a_in[31] & ~bm[31] &  aout[31]) |
                                ( a_in[31] &  bm[31] & ~aout[31] );

   assign lt                  = (~ap.unsign & (neg ^ ov)) |
                                ( ap.unsign & ~cout);


   assign eq                  = (a_in[31:0] == b_in[31:0]);
   assign ne                  = ~eq;
   assign neg                 =  aout[31];
   assign ge                  = ~lt;



   assign lout[31:0]          =  ( {32{csr_ren_in}} &                b_in[31:0]  ) |
                                 ( {32{ap.land   }} &  a_in[31:0] &  b_in[31:0]  ) |
                                 ( {32{ap.lor    }} & (a_in[31:0] |  b_in[31:0]) ) |
                                 ( {32{ap.lxor   }} & (a_in[31:0] ^  b_in[31:0]) );





   assign shift_amount[5:0]            = ( { 6{ap.sll}}   & (6'd32 - {1'b0,b_in[4:0]}) ) |   // [5] unused
                                         ( { 6{ap.srl}}   &          {1'b0,b_in[4:0]}  ) |
                                         ( { 6{ap.sra}}   &          {1'b0,b_in[4:0]}  );


   assign shift_mask[31:0]             = ( 32'hffffffff << ({5{ap.sll}} & b_in[4:0]) );


   assign shift_extend[31:0]           =  a_in[31:0];

   assign shift_extend[62:32]          = ( {31{ap.sra}} & {31{a_in[31]}} ) |
                                         ( {31{ap.sll}} &     a_in[30:0] );


   assign shift_long[62:0]    = ( shift_extend[62:0] >> shift_amount[4:0] );   // 62-32 unused

   assign sout[31:0]          = ( shift_long[31:0] & shift_mask[31:0] );





   assign sel_shift           =  ap.sll  | ap.srl | ap.sra;
   assign sel_adder           = (ap.add  | ap.sub) & ~ap.slt;
   assign sel_pc              =  ap.jal  | pp_in.pcall | pp_in.pja | pp_in.pret;
   assign csr_write_data[31:0]= (ap.csr_imm)  ?  b_in[31:0]  :  a_in[31:0];

   assign slt_one             =  ap.slt & lt;



   assign result[31:0]        =                        lout[31:0]             |
                                ({32{sel_shift}}    &  sout[31:0]           ) |
                                ({32{sel_adder}}    &  aout[31:0]           ) |
                                ({32{sel_pc}}       & {pcout[31:1],1'b0}    ) |
                                ({32{ap.csr_write}} &  csr_write_data[31:0] ) |
                                                      {31'b0, slt_one}       ;



   // *** branch handling ***

   assign any_jal             =  ap.jal      |
                                 pp_in.pcall |
                                 pp_in.pja   |
                                 pp_in.pret;

   assign actual_taken        = (ap.beq & eq) |
                                (ap.bne & ne) |
                                (ap.blt & lt) |
                                (ap.bge & ge) |
                                 any_jal;

   // for a conditional br pcout[] will be the opposite of the branch prediction
   // for jal or pcall, it will be the link address pc+2 or pc+4

   rvbradder ibradder (
                     .pc     ( pc_in[31:1]    ),
                     .offset ( brimm_in[12:1] ),
                     .dout   ( pcout[31:1]    ));


   // pred_correct is for the npc logic
   // pred_correct indicates not to use the flush_path
   // for any_jal pred_correct==0

   assign pred_correct_out    = (valid_in & ap.predict_nt & ~actual_taken & ~any_jal) |
                                (valid_in & ap.predict_t  &  actual_taken & ~any_jal);


   // for any_jal adder output is the flush path
   assign flush_path_out[31:1]= (any_jal) ? aout[31:1] : pcout[31:1];


   // pcall and pret are included here
   assign cond_mispredict     = (ap.predict_t  & ~actual_taken) |
                                (ap.predict_nt &  actual_taken);


   // target mispredicts on ret's

   assign target_mispredict   =  pp_in.pret & (pp_in.prett[31:1] != aout[31:1]);

   assign flush_upper_out     =   (ap.jal | cond_mispredict | target_mispredict) & valid_in & ~flush_upper_x   & ~flush_lower_r;
   assign flush_final_out     = ( (ap.jal | cond_mispredict | target_mispredict) & valid_in & ~flush_upper_x ) |  flush_lower_r;


   // .i 3
   // .o 2
   // .ilb hist[1] hist[0] taken
   // .ob newhist[1] newhist[0]
   // .type fd
   //
   // 00 0 01
   // 01 0 01
   // 10 0 00
   // 11 0 10
   // 00 1 10
   // 01 1 00
   // 10 1 11
   // 11 1 11

   assign newhist[1]          = ( pp_in.hist[1] &  pp_in.hist[0]) | (~pp_in.hist[0] & actual_taken);
   assign newhist[0]          = (~pp_in.hist[1] & ~actual_taken)  | ( pp_in.hist[1] & actual_taken);

   always_comb begin
      predict_p_out           =  pp_in;

      predict_p_out.misp      = ~flush_upper_x & ~flush_lower_r & (cond_mispredict | target_mispredict);
      predict_p_out.ataken    =  actual_taken;
      predict_p_out.hist[1]   =  newhist[1];
      predict_p_out.hist[0]   =  newhist[0];

   end



endmodule // el2_exu_alu_ctl
