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


module el2_exu_mul_ctl
import el2_pkg::*;
#(
`include "el2_param.vh"
 )
  (
   input logic          clk,              // Top level clock
   input logic          rst_l,            // Reset
   input logic          scan_mode,        // Scan mode

   input el2_mul_pkt_t mul_p,            // {Valid, RS1 signed operand, RS2 signed operand, Select low 32-bits of result}

   input logic [31:0]   rs1_in,           // A operand
   input logic [31:0]   rs2_in,           // B operand


   output logic [31:0]  result_x          // Result
  );


   logic                mul_x_enable;
   logic signed [32:0]  rs1_ext_in;
   logic signed [32:0]  rs2_ext_in;
   logic        [65:0]  prod_x;
   logic                low_x;




   assign mul_x_enable           =  mul_p.valid;

   assign rs1_ext_in[32]         =  mul_p.rs1_sign & rs1_in[31];
   assign rs2_ext_in[32]         =  mul_p.rs2_sign & rs2_in[31];

   assign rs1_ext_in[31:0]       =  rs1_in[31:0];
   assign rs2_ext_in[31:0]       =  rs2_in[31:0];



   // --------------------------- Multiply       ----------------------------------


   logic signed [32:0]  rs1_x;
   logic signed [32:0]  rs2_x;

   rvdffe #(34) i_a_x_ff         (.*, .din({mul_p.low,rs1_ext_in[32:0]}),        .dout({low_x,rs1_x[32:0]}),                 .en(mul_x_enable));
   rvdffe #(33) i_b_x_ff         (.*, .din(           rs2_ext_in[32:0] ),        .dout(       rs2_x[32:0] ),                 .en(mul_x_enable));


   assign prod_x[65:0]           =  rs1_x  *  rs2_x;


   assign result_x[31:0]         =  ( {32{~low_x}} & prod_x[63:32]    ) |
                                    ( {32{ low_x}} & prod_x[31:0]     );




endmodule  // el2_exu_mul_ctl
