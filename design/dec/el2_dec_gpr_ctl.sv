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

module el2_dec_gpr_ctl
import el2_pkg::*;
#(
   `include "el2_param.vh"
 )  (
    input logic [4:0]  raddr0,       // logical read addresses
    input logic [4:0]  raddr1,

    input logic        wen0,         // write enable
    input logic [4:0]  waddr0,       // write address
    input logic [31:0] wd0,          // write data

    input logic        wen1,         // write enable
    input logic [4:0]  waddr1,       // write address
    input logic [31:0] wd1,          // write data

    input logic        wen2,         // write enable
    input logic [4:0]  waddr2,       // write address
    input logic [31:0] wd2,          // write data

    input logic        clk,
    input logic        rst_l,

    output logic [31:0] rd0,         // read data
    output logic [31:0] rd1,

    input  logic        scan_mode
);

   logic [31:1] [31:0] gpr_out;      // 31 x 32 bit GPRs
   logic [31:1] [31:0] gpr_in;
   logic [31:1] w0v,w1v,w2v;
   logic [31:1] gpr_wr_en;

   // GPR Write Enables
   assign gpr_wr_en[31:1] = (w0v[31:1] | w1v[31:1] | w2v[31:1]);
   for ( genvar j=1; j<32; j++ )  begin : gpr
      rvdffe #(32) gprff (.*, .en(gpr_wr_en[j]), .din(gpr_in[j][31:0]), .dout(gpr_out[j][31:0]));
   end : gpr

   // the read out
   always_comb begin
      rd0[31:0] = 32'b0;
      rd1[31:0] = 32'b0;
      w0v[31:1] = 31'b0;
      w1v[31:1] = 31'b0;
      w2v[31:1] = 31'b0;
      gpr_in[31:1] = '0;

      // GPR Read logic
      for (int j=1; j<32; j++ )  begin
         rd0[31:0] |= ({32{(raddr0[4:0]== 5'(j))}} & gpr_out[j][31:0]);
         rd1[31:0] |= ({32{(raddr1[4:0]== 5'(j))}} & gpr_out[j][31:0]);
      end

     // GPR Write logic
     for (int j=1; j<32; j++ )  begin
         w0v[j]     = wen0  & (waddr0[4:0]== 5'(j) );
         w1v[j]     = wen1  & (waddr1[4:0]== 5'(j) );
         w2v[j]     = wen2  & (waddr2[4:0]== 5'(j) );
         gpr_in[j]  =    ({32{w0v[j]}} & wd0[31:0]) |
                         ({32{w1v[j]}} & wd1[31:0]) |
                         ({32{w2v[j]}} & wd2[31:0]);
     end
   end // always_comb begin

`ifdef RV_ASSERT_ON

   logic  write_collision_unused;
   assign write_collision_unused = ( (w0v[31:1] == w1v[31:1]) & wen0 & wen1 ) |
                                   ( (w0v[31:1] == w2v[31:1]) & wen0 & wen2 ) |
                                   ( (w1v[31:1] == w2v[31:1]) & wen1 & wen2 );


   // asserting that no 2 ports will write to the same gpr simultaneously
   assert_multiple_wen_to_same_gpr: assert #0 (~( write_collision_unused ) );

`endif

endmodule
