//********************************************************************************
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
//********************************************************************************

module el2_ifu_tb_memread;

   logic [15:0] compressed [0:128000]; // vector of compressed instructions
   logic [31:0] expected [0:128000];   // vector of correspoding expected instruction


   logic        rst_l;
   logic        clk;

   int          clk_count;



   logic [31:0] expected_val;
   logic [15:0] compressed_din;

   logic [31:0] actual;

   logic        error;

   integer      i;
   initial begin

      clk=0;
      rst_l=0;

      // initialize the reads and populate the instruction arrays
      $readmemh ("left64k", compressed );
      $readmemh ("right64k", expected );

      $dumpfile ("top.vcd");
      $dumpvars;
      $dumpon;

   end

   always #50 clk =~clk;

   always @(posedge clk) begin
      clk_count = clk_count +1;
      if (clk_count>=1 & clk_count<=3) rst_l <= 1'b0;
      else rst_l <= 1'b1;

      if (clk_count > 3) begin

         compressed_din[15:0] <= compressed[clk_count-3]; // c.mv
         expected_val[31:0] <= expected[clk_count-3];

      end

      if (clk_count == 65000) begin
         $dumpoff;
         $finish;
      end
   end // always @ (posedge clk)

   always @(negedge clk) begin
      if (clk_count > 3 & error) begin
         $display("clock: %d compressed %h error actual %h expected %h",clk_count,compressed_din,actual,expected_val);
      end
   end


   el2_ifu_compress_ctl align (.*,.din(compressed_din[15:0]),.dout(actual[31:0]));

   assign error = actual[31:0] != expected_val[31:0];



endmodule // el2_ifu_tb_memread


