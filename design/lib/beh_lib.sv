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

// all flops call the rvdff flop


module rvdff #( parameter WIDTH=1, SHORT=0 )
   (
     input logic [WIDTH-1:0] din,
     input logic           clk,
     input logic                   rst_l,

     output logic [WIDTH-1:0] dout
     );

if (SHORT == 1) begin
   assign dout = din;
end
else begin
`ifdef RV_CLOCKGATE
   always @(posedge tb_top.clk) begin
      #0 $strobe("CG: %0t %m din %x dout %x clk %b width %d",$time,din,dout,clk,WIDTH);
   end
`endif

   always_ff @(posedge clk or negedge rst_l) begin
      if (rst_l == 0)
        dout[WIDTH-1:0] <= 0;
      else
        dout[WIDTH-1:0] <= din[WIDTH-1:0];
   end

end
endmodule

// rvdff with 2:1 input mux to flop din iff sel==1
module rvdffs #( parameter WIDTH=1, SHORT=0 )
   (
     input logic [WIDTH-1:0] din,
     input logic             en,
     input logic           clk,
     input logic                   rst_l,
     output logic [WIDTH-1:0] dout
     );

if (SHORT == 1) begin : genblock
   assign dout = din;
end
else begin : genblock
   rvdff #(WIDTH) dffs (.din((en) ? din[WIDTH-1:0] : dout[WIDTH-1:0]), .*);
end

endmodule

// rvdff with en and clear
module rvdffsc #( parameter WIDTH=1, SHORT=0 )
   (
     input logic [WIDTH-1:0] din,
     input logic             en,
     input logic             clear,
     input logic           clk,
     input logic                   rst_l,
     output logic [WIDTH-1:0] dout
     );

   logic [WIDTH-1:0]          din_new;
if (SHORT == 1) begin : genblock
   assign dout = din;
end
else begin : genblock
   assign din_new = {WIDTH{~clear}} & (en ? din[WIDTH-1:0] : dout[WIDTH-1:0]);
   rvdff #(WIDTH) dffsc (.din(din_new[WIDTH-1:0]), .*);
end
endmodule

// _fpga versions
module rvdff_fpga #( parameter WIDTH=1, SHORT=0 )
   (
     input logic [WIDTH-1:0] din,
     input logic           clk,
     input logic           clken,
     input logic           rawclk,
     input logic           rst_l,

     output logic [WIDTH-1:0] dout
     );

if (SHORT == 1) begin : genblock
   assign dout = din;
end
else begin : genblock
   `ifdef RV_FPGA_OPTIMIZE
    rvdffs #(WIDTH) dffs (.clk(rawclk), .en(clken), .*);
`else
    rvdff #(WIDTH)  dff (.*);
`endif
end
endmodule

// rvdff with 2:1 input mux to flop din iff sel==1
module rvdffs_fpga #( parameter WIDTH=1, SHORT=0 )
   (
     input logic [WIDTH-1:0] din,
     input logic             en,
     input logic           clk,
     input logic           clken,
     input logic           rawclk,
     input logic           rst_l,

     output logic [WIDTH-1:0] dout
     );

if (SHORT == 1) begin : genblock
   assign dout = din;
end
else begin : genblock
`ifdef RV_FPGA_OPTIMIZE
   rvdffs #(WIDTH)   dffs (.clk(rawclk), .en(clken & en), .*);
`else
   rvdffs #(WIDTH)   dffs (.*);
`endif
end

endmodule

// rvdff with en and clear
module rvdffsc_fpga #( parameter WIDTH=1, SHORT=0 )
   (
     input logic [WIDTH-1:0] din,
     input logic             en,
     input logic             clear,
     input logic             clk,
     input logic             clken,
     input logic             rawclk,
     input logic             rst_l,

     output logic [WIDTH-1:0] dout
     );

   logic [WIDTH-1:0]          din_new;
if (SHORT == 1) begin : genblock
   assign dout = din;
end
else begin : genblock
`ifdef RV_FPGA_OPTIMIZE
   rvdffs  #(WIDTH)   dffs  (.clk(rawclk), .din(din[WIDTH-1:0] & {WIDTH{~clear}}),.en((en | clear) & clken), .*);
`else
   rvdffsc #(WIDTH)   dffsc (.*);
`endif
end
endmodule


module rvdffe #( parameter WIDTH=1, SHORT=0, OVERRIDE=0 )
   (
     input  logic [WIDTH-1:0] din,
     input  logic           en,
     input  logic           clk,
     input  logic           rst_l,
     // Excluding scan_mode from coverage as its usage is determined by the integrator of the VeeR core.
     /*pragma coverage off*/
     input  logic             scan_mode,
     /*pragma coverage on*/
     output logic [WIDTH-1:0] dout
     );

   logic                      l1clk;

if (SHORT == 1) begin : genblock
   if (1) begin : genblock
      assign dout = din;
   end
end
else begin : genblock

`ifndef RV_PHYSICAL
   if (WIDTH >= 8 || OVERRIDE==1) begin: genblock
`endif

`ifdef RV_FPGA_OPTIMIZE
      rvdffs #(WIDTH) dff ( .* );
`else
      rvclkhdr clkhdr ( .* );
      rvdff #(WIDTH) dff (.*, .clk(l1clk));
`endif

`ifndef RV_PHYSICAL
   end
   else
      $error("%m: rvdffe must be WIDTH >= 8");
`endif
end // else: !if(SHORT == 1)

endmodule // rvdffe


module rvdffpcie #( parameter WIDTH=31 )
   (
     input  logic [WIDTH-1:0] din,
     input  logic             clk,
     input  logic             rst_l,
     input  logic             en,
     // Excluding scan_mode from coverage as its usage is determined by the integrator of the VeeR core.
     /*pragma coverage off*/
     input  logic             scan_mode,
     /*pragma coverage on*/
     output logic [WIDTH-1:0] dout
     );



`ifndef RV_PHYSICAL
   if (WIDTH == 31) begin: genblock
`endif

`ifdef RV_FPGA_OPTIMIZE
      rvdffs #(WIDTH) dff ( .* );
`else

      rvdfflie #(.WIDTH(WIDTH), .LEFT(19)) dff (.*);

`endif

`ifndef RV_PHYSICAL
   end
   else
      $error("%m: rvdffpcie width must be 31");
`endif
endmodule

// format: { LEFT, EXTRA }
// LEFT # of bits will be done with rvdffie, all else EXTRA with rvdffe
module rvdfflie #( parameter WIDTH=16, LEFT=8 )
   (
     input  logic [WIDTH-1:0] din,
     input  logic             clk,
     input  logic             rst_l,
     input  logic             en,
     // Excluding scan_mode from coverage as its usage is determined by the integrator of the VeeR core.
     /*pragma coverage off*/
     input  logic             scan_mode,
     /*pragma coverage on*/
     output logic [WIDTH-1:0] dout
     );

   localparam EXTRA = WIDTH-LEFT;







   localparam LMSB = WIDTH-1;
   localparam LLSB = LMSB-LEFT+1;
   localparam XMSB = LLSB-1;
   localparam XLSB = LLSB-EXTRA;


`ifndef RV_PHYSICAL
   if (WIDTH >= 16 && LEFT >= 8 && EXTRA >= 8) begin: genblock
`endif

`ifdef RV_FPGA_OPTIMIZE
      rvdffs #(WIDTH) dff ( .* );
`else

      rvdffiee #(LEFT)  dff_left  (.*, .din(din[LMSB:LLSB]), .dout(dout[LMSB:LLSB]));


      rvdffe  #(EXTRA)  dff_extra (.*, .din(din[XMSB:XLSB]), .dout(dout[XMSB:XLSB]));




`endif

`ifndef RV_PHYSICAL
   end
   else
      $error("%m: rvdfflie musb be WIDTH >= 16 && LEFT >= 8 && EXTRA >= 8");
`endif
endmodule




// special power flop for predict packet
// format: { LEFT, RIGHT==31 }
// LEFT # of bits will be done with rvdffe; RIGHT is enabled by LEFT[LSB] & en
module rvdffppe #( parameter integer WIDTH = 39 )
   (
     input  logic [WIDTH-1:0] din,
     input  logic             clk,
     input  logic             rst_l,
     input  logic             en,
     // Excluding scan_mode from coverage as its usage is determined by the integrator of the VeeR core.
     /*pragma coverage off*/
     input  logic             scan_mode,
     /*pragma coverage on*/
     output logic [WIDTH-1:0] dout
     );

   localparam integer RIGHT = 31;
   localparam integer LEFT  = WIDTH - RIGHT;

   localparam integer LMSB  = WIDTH-1;
   localparam integer LLSB  = LMSB-LEFT+1;
   localparam integer RMSB  = LLSB-1;
   localparam integer RLSB  = LLSB-RIGHT;


`ifndef RV_PHYSICAL
   if (WIDTH>=32 && LEFT>=8 && RIGHT>=8) begin: genblock
`endif

`ifdef RV_FPGA_OPTIMIZE
      rvdffs #(WIDTH) dff ( .* );
`else
      rvdffe #(LEFT)     dff_left (.*, .din(din[LMSB:LLSB]), .dout(dout[LMSB:LLSB]));

      rvdffe #(RIGHT)   dff_right (.*, .din(din[RMSB:RLSB]), .dout(dout[RMSB:RLSB]), .en(en & din[LLSB]));  // qualify with pret


`endif

`ifndef RV_PHYSICAL
   end
   else
      $error("%m: must be WIDTH>=32 && LEFT>=8 && RIGHT>=8");
`endif
endmodule




module rvdffie #( parameter WIDTH=1, OVERRIDE=0 )
   (
     input  logic [WIDTH-1:0] din,

     input  logic           clk,
     input  logic           rst_l,
     // Excluding scan_mode from coverage as its usage is determined by the integrator of the VeeR core.
     /*pragma coverage off*/
     input  logic             scan_mode,
     /*pragma coverage on*/
     output logic [WIDTH-1:0] dout
     );

   logic                      l1clk;
   logic                      en;








`ifndef RV_PHYSICAL
   if (WIDTH >= 8 || OVERRIDE==1) begin: genblock
`endif

      assign en = |(din ^ dout);

`ifdef RV_FPGA_OPTIMIZE
      rvdffs #(WIDTH) dff ( .* );
`else
      rvclkhdr clkhdr ( .* );
      rvdff #(WIDTH) dff (.*, .clk(l1clk));
`endif

`ifndef RV_PHYSICAL
   end
   else
     $error("%m: rvdffie must be WIDTH >= 8");
`endif


endmodule

// ie flop but it has an .en input
module rvdffiee #( parameter WIDTH=1, OVERRIDE=0 )
   (
     input  logic [WIDTH-1:0] din,

     input  logic           clk,
     input  logic           rst_l,
     // Excluding scan_mode from coverage as its usage is determined by the integrator of the VeeR core.
     /*pragma coverage off*/
     input  logic           scan_mode,
     /*pragma coverage on*/
     input  logic           en,
     output logic [WIDTH-1:0] dout
     );

   logic                      l1clk;
   logic                      final_en;

`ifndef RV_PHYSICAL
   if (WIDTH >= 8 || OVERRIDE==1) begin: genblock
`endif

      assign final_en = (|(din ^ dout)) & en;

`ifdef RV_FPGA_OPTIMIZE
      rvdffs #(WIDTH) dff ( .*, .en(final_en) );
`else
      rvdffe #(WIDTH) dff (.*,  .en(final_en));
`endif

`ifndef RV_PHYSICAL
   end
   else
      $error("%m: rvdffie width must be >= 8");
`endif

endmodule



module rvsyncss #(parameter WIDTH = 251)
   (
     input  logic                 clk,
     input  logic                 rst_l,
     input  logic [WIDTH-1:0]     din,
     output logic [WIDTH-1:0]     dout
     );

   logic [WIDTH-1:0]              din_ff1;

   rvdff #(WIDTH) sync_ff1  (.*, .din (din[WIDTH-1:0]),     .dout(din_ff1[WIDTH-1:0]));
   rvdff #(WIDTH) sync_ff2  (.*, .din (din_ff1[WIDTH-1:0]), .dout(dout[WIDTH-1:0]));

endmodule // rvsyncss

module rvsyncss_fpga #(parameter WIDTH = 251)
   (
     input  logic                 gw_clk,
     input  logic                 rawclk,
     input  logic                 clken,
     input  logic                 rst_l,
     input  logic [WIDTH-1:0]     din,
     output logic [WIDTH-1:0]     dout
     );

   logic [WIDTH-1:0]              din_ff1;

   rvdff_fpga #(WIDTH) sync_ff1  (.*, .clk(gw_clk), .rawclk(rawclk), .clken(clken), .din (din[WIDTH-1:0]),     .dout(din_ff1[WIDTH-1:0]));
   rvdff_fpga #(WIDTH) sync_ff2  (.*, .clk(gw_clk), .rawclk(rawclk), .clken(clken), .din (din_ff1[WIDTH-1:0]), .dout(dout[WIDTH-1:0]));

endmodule // rvsyncss

module rvlsadder
  (
    input logic [31:0] rs1,
    input logic [11:0] offset,

    output logic [31:0] dout
    );

   logic                cout;
   logic                sign;

   logic [31:12]        rs1_inc;
   logic [31:12]        rs1_dec;

   assign {cout,dout[11:0]} = {1'b0,rs1[11:0]} + {1'b0,offset[11:0]};

   assign rs1_inc[31:12] = rs1[31:12] + 1;

   assign rs1_dec[31:12] = rs1[31:12] - 1;

   assign sign = offset[11];

   assign dout[31:12] = ({20{  sign ^~  cout}} &     rs1[31:12]) |
                        ({20{ ~sign &   cout}}  & rs1_inc[31:12]) |
                        ({20{  sign &  ~cout}}  & rs1_dec[31:12]);

endmodule // rvlsadder

// assume we only maintain pc[31:1] in the pipe

module rvbradder
  (
    input [31:1] pc,
    input [12:1] offset,

    output [31:1] dout
    );

   logic          cout;
   logic          sign;

   logic [31:13]  pc_inc;
   logic [31:13]  pc_dec;

   assign {cout,dout[12:1]} = {1'b0,pc[12:1]} + {1'b0,offset[12:1]};

   assign pc_inc[31:13] = pc[31:13] + 1;

   assign pc_dec[31:13] = pc[31:13] - 1;

   assign sign = offset[12];


   assign dout[31:13] = ({19{  sign ^~  cout}} &     pc[31:13]) |
                        ({19{ ~sign &   cout}}  & pc_inc[31:13]) |
                        ({19{  sign &  ~cout}}  & pc_dec[31:13]);


endmodule // rvbradder


// 2s complement circuit
module rvtwoscomp #( parameter WIDTH=32 )
   (
     input logic [WIDTH-1:0] din,

     output logic [WIDTH-1:0] dout
     );

   logic [WIDTH-1:1]          dout_temp;   // holding for all other bits except for the lsb. LSB is always din

   genvar                     i;

   for ( i = 1; i < WIDTH; i++ )  begin : flip_after_first_one
      assign dout_temp[i] = (|din[i-1:0]) ? ~din[i] : din[i];
   end : flip_after_first_one

   assign dout[WIDTH-1:0]  = { dout_temp[WIDTH-1:1], din[0] };

endmodule  // 2'scomp

// find first
module rvfindfirst1 #( parameter WIDTH=32, SHIFT=$clog2(WIDTH) )
   (
     input logic [WIDTH-1:0] din,

     output logic [SHIFT-1:0] dout
     );
   logic                      done;

   always_comb begin
      dout[SHIFT-1:0] = {SHIFT{1'b0}};
      done    = 1'b0;

      for ( int i = WIDTH-1; i > 0; i-- )  begin : find_first_one
         done |= din[i];
         dout[SHIFT-1:0] += done ? 1'b0 : 1'b1;
      end : find_first_one
   end
endmodule // rvfindfirst1

module rvfindfirst1hot #( parameter WIDTH=32 )
   (
     input logic [WIDTH-1:0] din,

     output logic [WIDTH-1:0] dout
     );
   logic                      done;

   always_comb begin
      dout[WIDTH-1:0] = {WIDTH{1'b0}};
      done    = 1'b0;
      for ( int i = 0; i < WIDTH; i++ )  begin : find_first_one
         dout[i] = ~done & din[i];
         done   |= din[i];
      end : find_first_one
   end
endmodule // rvfindfirst1hot

// mask and match function matches bits after finding the first 0 position
// find first starting from LSB. Skip that location and match the rest of the bits
module rvmaskandmatch #( parameter WIDTH=32 )
   (
     input  logic [WIDTH-1:0] mask,     // this will have the mask in the lower bit positions
     input  logic [WIDTH-1:0] data,     // this is what needs to be matched on the upper bits with the mask's upper bits
     input  logic             masken,   // when 1 : do mask. 0 : full match
     output logic             match
     );

   logic [WIDTH-1:0]          matchvec;
   logic                      masken_or_fullmask;

   assign masken_or_fullmask = masken &  ~(&mask[WIDTH-1:0]);

   assign matchvec[0]        = masken_or_fullmask | (mask[0] == data[0]);
   genvar                     i;

   for ( i = 1; i < WIDTH; i++ )  begin : match_after_first_zero
      assign matchvec[i] = (&mask[i-1:0] & masken_or_fullmask) ? 1'b1 : (mask[i] == data[i]);
   end : match_after_first_zero

   assign match  = &matchvec[WIDTH-1:0];    // all bits either matched or were masked off

endmodule // rvmaskandmatch




// Check if the S_ADDR <= addr < E_ADDR
module rvrangecheck  #(CCM_SADR = 32'h0,
                       CCM_SIZE  = 128) (
   input  logic [31:0]   addr,                             // Address to be checked for range
   output logic          in_range,                            // S_ADDR <= start_addr < E_ADDR
   output logic          in_region
);

   localparam REGION_BITS = 4;
   localparam MASK_BITS = 10 + $clog2(CCM_SIZE);

   logic [31:0]          start_addr;
   logic [3:0]           region;

   assign start_addr[31:0]        = CCM_SADR;
   assign region[REGION_BITS-1:0] = start_addr[31:(32-REGION_BITS)];

   assign in_region = (addr[31:(32-REGION_BITS)] == region[REGION_BITS-1:0]);
   if (CCM_SIZE  == 48)
    assign in_range  = (addr[31:MASK_BITS] == start_addr[31:MASK_BITS]) & ~(&addr[MASK_BITS-1 : MASK_BITS-2]);
   else
    assign in_range  = (addr[31:MASK_BITS] == start_addr[31:MASK_BITS]);

endmodule  // rvrangechecker

// 16 bit even parity generator
module rveven_paritygen #(WIDTH = 16)  (
                                         input  logic [WIDTH-1:0]  data_in,         // Data
                                         output logic              parity_out       // generated even parity
                                         );

   assign  parity_out =  ^(data_in[WIDTH-1:0]) ;

endmodule  // rveven_paritygen

module rveven_paritycheck #(WIDTH = 16)  (
                                           input  logic [WIDTH-1:0]  data_in,         // Data
                                           input  logic              parity_in,
                                           output logic              parity_err       // Parity error
                                           );

   assign  parity_err =  ^(data_in[WIDTH-1:0]) ^ parity_in ;

endmodule  // rveven_paritycheck

module rvecc_encode  (
                      input [31:0] din,
                      output [6:0] ecc_out
                      );
logic [5:0] ecc_out_temp;

   assign ecc_out_temp[0] = din[0]^din[1]^din[3]^din[4]^din[6]^din[8]^din[10]^din[11]^din[13]^din[15]^din[17]^din[19]^din[21]^din[23]^din[25]^din[26]^din[28]^din[30];
   assign ecc_out_temp[1] = din[0]^din[2]^din[3]^din[5]^din[6]^din[9]^din[10]^din[12]^din[13]^din[16]^din[17]^din[20]^din[21]^din[24]^din[25]^din[27]^din[28]^din[31];
   assign ecc_out_temp[2] = din[1]^din[2]^din[3]^din[7]^din[8]^din[9]^din[10]^din[14]^din[15]^din[16]^din[17]^din[22]^din[23]^din[24]^din[25]^din[29]^din[30]^din[31];
   assign ecc_out_temp[3] = din[4]^din[5]^din[6]^din[7]^din[8]^din[9]^din[10]^din[18]^din[19]^din[20]^din[21]^din[22]^din[23]^din[24]^din[25];
   assign ecc_out_temp[4] = din[11]^din[12]^din[13]^din[14]^din[15]^din[16]^din[17]^din[18]^din[19]^din[20]^din[21]^din[22]^din[23]^din[24]^din[25];
   assign ecc_out_temp[5] = din[26]^din[27]^din[28]^din[29]^din[30]^din[31];

   assign ecc_out[6:0] = {(^din[31:0])^(^ecc_out_temp[5:0]),ecc_out_temp[5:0]};

endmodule // rvecc_encode

module rvecc_decode  (
                      input         en,
                      input [31:0]  din,
                      input [6:0]   ecc_in,
                      input         sed_ded,    // only do detection and no correction. Used for the I$
                      output [31:0] dout,
                      output [6:0]  ecc_out,
                      output        single_ecc_error,
                      output        double_ecc_error

                      );

   logic [6:0]                      ecc_check;
   logic [38:0]                     error_mask;
   logic [38:0]                     din_plus_parity, dout_plus_parity;

   // Generate the ecc bits
   assign ecc_check[0] = ecc_in[0]^din[0]^din[1]^din[3]^din[4]^din[6]^din[8]^din[10]^din[11]^din[13]^din[15]^din[17]^din[19]^din[21]^din[23]^din[25]^din[26]^din[28]^din[30];
   assign ecc_check[1] = ecc_in[1]^din[0]^din[2]^din[3]^din[5]^din[6]^din[9]^din[10]^din[12]^din[13]^din[16]^din[17]^din[20]^din[21]^din[24]^din[25]^din[27]^din[28]^din[31];
   assign ecc_check[2] = ecc_in[2]^din[1]^din[2]^din[3]^din[7]^din[8]^din[9]^din[10]^din[14]^din[15]^din[16]^din[17]^din[22]^din[23]^din[24]^din[25]^din[29]^din[30]^din[31];
   assign ecc_check[3] = ecc_in[3]^din[4]^din[5]^din[6]^din[7]^din[8]^din[9]^din[10]^din[18]^din[19]^din[20]^din[21]^din[22]^din[23]^din[24]^din[25];
   assign ecc_check[4] = ecc_in[4]^din[11]^din[12]^din[13]^din[14]^din[15]^din[16]^din[17]^din[18]^din[19]^din[20]^din[21]^din[22]^din[23]^din[24]^din[25];
   assign ecc_check[5] = ecc_in[5]^din[26]^din[27]^din[28]^din[29]^din[30]^din[31];

   // This is the parity bit
   assign ecc_check[6] = ((^din[31:0])^(^ecc_in[6:0])) & ~sed_ded;

   assign single_ecc_error = en & (ecc_check[6:0] != 0) & ecc_check[6];   // this will never be on for sed_ded
   assign double_ecc_error = en & (ecc_check[6:0] != 0) & ~ecc_check[6];  // all errors in the sed_ded case will be recorded as DE

   // Generate the mask for error correctiong
   for (genvar i=1; i<40; i++) begin
      assign error_mask[i-1] = (ecc_check[5:0] == i);
   end

   // Generate the corrected data
   assign din_plus_parity[38:0] = {ecc_in[6], din[31:26], ecc_in[5], din[25:11], ecc_in[4], din[10:4], ecc_in[3], din[3:1], ecc_in[2], din[0], ecc_in[1:0]};

   assign dout_plus_parity[38:0] = single_ecc_error ? (error_mask[38:0] ^ din_plus_parity[38:0]) : din_plus_parity[38:0];
   assign dout[31:0]             = {dout_plus_parity[37:32], dout_plus_parity[30:16], dout_plus_parity[14:8], dout_plus_parity[6:4], dout_plus_parity[2]};
   assign ecc_out[6:0]           = {(dout_plus_parity[38] ^ (ecc_check[6:0] == 7'b1000000)), dout_plus_parity[31], dout_plus_parity[15], dout_plus_parity[7], dout_plus_parity[3], dout_plus_parity[1:0]};

endmodule // rvecc_decode

module rvecc_encode_64  (
                      input [63:0] din,
                      output [6:0] ecc_out
                      );
  assign ecc_out[0] = din[0]^din[1]^din[3]^din[4]^din[6]^din[8]^din[10]^din[11]^din[13]^din[15]^din[17]^din[19]^din[21]^din[23]^din[25]^din[26]^din[28]^din[30]^din[32]^din[34]^din[36]^din[38]^din[40]^din[42]^din[44]^din[46]^din[48]^din[50]^din[52]^din[54]^din[56]^din[57]^din[59]^din[61]^din[63];

   assign ecc_out[1] = din[0]^din[2]^din[3]^din[5]^din[6]^din[9]^din[10]^din[12]^din[13]^din[16]^din[17]^din[20]^din[21]^din[24]^din[25]^din[27]^din[28]^din[31]^din[32]^din[35]^din[36]^din[39]^din[40]^din[43]^din[44]^din[47]^din[48]^din[51]^din[52]^din[55]^din[56]^din[58]^din[59]^din[62]^din[63];

   assign ecc_out[2] = din[1]^din[2]^din[3]^din[7]^din[8]^din[9]^din[10]^din[14]^din[15]^din[16]^din[17]^din[22]^din[23]^din[24]^din[25]^din[29]^din[30]^din[31]^din[32]^din[37]^din[38]^din[39]^din[40]^din[45]^din[46]^din[47]^din[48]^din[53]^din[54]^din[55]^din[56]^din[60]^din[61]^din[62]^din[63];

   assign ecc_out[3] = din[4]^din[5]^din[6]^din[7]^din[8]^din[9]^din[10]^din[18]^din[19]^din[20]^din[21]^din[22]^din[23]^din[24]^din[25]^din[33]^din[34]^din[35]^din[36]^din[37]^din[38]^din[39]^din[40]^din[49]^din[50]^din[51]^din[52]^din[53]^din[54]^din[55]^din[56];

   assign ecc_out[4] = din[11]^din[12]^din[13]^din[14]^din[15]^din[16]^din[17]^din[18]^din[19]^din[20]^din[21]^din[22]^din[23]^din[24]^din[25]^din[41]^din[42]^din[43]^din[44]^din[45]^din[46]^din[47]^din[48]^din[49]^din[50]^din[51]^din[52]^din[53]^din[54]^din[55]^din[56];

   assign ecc_out[5] = din[26]^din[27]^din[28]^din[29]^din[30]^din[31]^din[32]^din[33]^din[34]^din[35]^din[36]^din[37]^din[38]^din[39]^din[40]^din[41]^din[42]^din[43]^din[44]^din[45]^din[46]^din[47]^din[48]^din[49]^din[50]^din[51]^din[52]^din[53]^din[54]^din[55]^din[56];

   assign ecc_out[6] = din[57]^din[58]^din[59]^din[60]^din[61]^din[62]^din[63];

endmodule // rvecc_encode_64


module rvecc_decode_64  (
                      input         en,
                      input [63:0]  din,
                      input [6:0]   ecc_in,
                      output        ecc_error
                      );

   logic [6:0]                      ecc_check;

   // Generate the ecc bits
   assign ecc_check[0] = ecc_in[0]^din[0]^din[1]^din[3]^din[4]^din[6]^din[8]^din[10]^din[11]^din[13]^din[15]^din[17]^din[19]^din[21]^din[23]^din[25]^din[26]^din[28]^din[30]^din[32]^din[34]^din[36]^din[38]^din[40]^din[42]^din[44]^din[46]^din[48]^din[50]^din[52]^din[54]^din[56]^din[57]^din[59]^din[61]^din[63];

   assign ecc_check[1] = ecc_in[1]^din[0]^din[2]^din[3]^din[5]^din[6]^din[9]^din[10]^din[12]^din[13]^din[16]^din[17]^din[20]^din[21]^din[24]^din[25]^din[27]^din[28]^din[31]^din[32]^din[35]^din[36]^din[39]^din[40]^din[43]^din[44]^din[47]^din[48]^din[51]^din[52]^din[55]^din[56]^din[58]^din[59]^din[62]^din[63];

   assign ecc_check[2] = ecc_in[2]^din[1]^din[2]^din[3]^din[7]^din[8]^din[9]^din[10]^din[14]^din[15]^din[16]^din[17]^din[22]^din[23]^din[24]^din[25]^din[29]^din[30]^din[31]^din[32]^din[37]^din[38]^din[39]^din[40]^din[45]^din[46]^din[47]^din[48]^din[53]^din[54]^din[55]^din[56]^din[60]^din[61]^din[62]^din[63];

   assign ecc_check[3] = ecc_in[3]^din[4]^din[5]^din[6]^din[7]^din[8]^din[9]^din[10]^din[18]^din[19]^din[20]^din[21]^din[22]^din[23]^din[24]^din[25]^din[33]^din[34]^din[35]^din[36]^din[37]^din[38]^din[39]^din[40]^din[49]^din[50]^din[51]^din[52]^din[53]^din[54]^din[55]^din[56];

   assign ecc_check[4] = ecc_in[4]^din[11]^din[12]^din[13]^din[14]^din[15]^din[16]^din[17]^din[18]^din[19]^din[20]^din[21]^din[22]^din[23]^din[24]^din[25]^din[41]^din[42]^din[43]^din[44]^din[45]^din[46]^din[47]^din[48]^din[49]^din[50]^din[51]^din[52]^din[53]^din[54]^din[55]^din[56];

   assign ecc_check[5] = ecc_in[5]^din[26]^din[27]^din[28]^din[29]^din[30]^din[31]^din[32]^din[33]^din[34]^din[35]^din[36]^din[37]^din[38]^din[39]^din[40]^din[41]^din[42]^din[43]^din[44]^din[45]^din[46]^din[47]^din[48]^din[49]^din[50]^din[51]^din[52]^din[53]^din[54]^din[55]^din[56];

   assign ecc_check[6] = ecc_in[6]^din[57]^din[58]^din[59]^din[60]^din[61]^din[62]^din[63];

   assign ecc_error = en & (ecc_check[6:0] != 0);  // all errors in the sed_ded case will be recorded as DE

 endmodule // rvecc_decode_64

`ifndef TECH_SPECIFIC_EC_RV_ICG
module `TEC_RV_ICG
  (
   input logic SE, EN, CK,
   output Q
   );

   logic  en_ff;
   logic  enable;

   assign      enable = EN | SE;

   always @(CK, enable) begin
      if(!CK)
        en_ff = enable;
   end
   assign Q = CK & en_ff;

endmodule
`endif

`ifndef RV_FPGA_OPTIMIZE
module rvclkhdr
  (
   input  logic en,
   input  logic clk,
   // Excluding scan_mode from coverage as its usage is determined by the integrator of the VeeR core.
   /*pragma coverage off*/
   input  logic scan_mode,
   /*pragma coverage on*/
   output logic l1clk
   );

   logic   SE;
   assign       SE = 0;

`ifdef TECH_SPECIFIC_EC_RV_ICG
   `USER_EC_RV_ICG clkhdr ( .*, .EN(en), .CK(clk), .Q(l1clk));
`else
   `TEC_RV_ICG clkhdr ( .*, .EN(en), .CK(clk), .Q(l1clk));
`endif

endmodule // rvclkhdr
`endif

module rvoclkhdr
  (
   input  logic en,
   input  logic clk,
   // Excluding scan_mode from coverage as its usage is determined by the integrator of the VeeR core.
   /*pragma coverage off*/
   input  logic scan_mode,
   /*pragma coverage on*/
   output logic l1clk
   );

   logic   SE;
   assign       SE = 0;

`ifdef RV_FPGA_OPTIMIZE
   assign l1clk = clk;
`else
   `ifdef TECH_SPECIFIC_EC_RV_ICG
      `USER_EC_RV_ICG clkhdr ( .*, .EN(en), .CK(clk), .Q(l1clk));
   `else
      `TEC_RV_ICG clkhdr ( .*, .EN(en), .CK(clk), .Q(l1clk));
    `endif
`endif

endmodule



