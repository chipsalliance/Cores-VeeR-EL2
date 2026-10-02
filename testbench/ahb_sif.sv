// SPDX-License-Identifier: Apache-2.0
// Copyright 2019 Western Digital Corporation or its affiliates.
// Copyright 2024 Antmicro <www.antmicro.com>
// //
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
//
`ifdef RV_BUILD_AHB_LITE

module ahb_sif #(
    parameter int MAX_DELAY = -1,
    parameter int MIN_DELAY = 0
) (
    input logic [63:0] HWDATA,
    input logic HCLK,
    input logic HSEL,
    input logic [3:0] HPROT,
    input logic HWRITE,
    input logic [1:0] HTRANS,
    input logic [2:0] HSIZE,
    input logic HREADY,
    input logic HRESETn,
    input logic [31:0] HADDR,
    input logic [2:0] HBURST,

    output logic HREADYOUT,
    output logic HRESP,
    output logic [63:0] HRDATA
);

  logic write;
  logic [31:0] laddr, addr;
  logic [7:0] strb_lat;
  logic [63:0] rdata;

  bit [7:0] mem[bit [31:0]];
  bit [7:0] wscnt;
  int dws = 0;
  int iws = 0;
  bit dws_rand;
  bit iws_rand;
  bit ok;

  // Wires
  wire [7:0] strb =  HSIZE == 3'b000 ? 8'h1 << HADDR[2:0] :
                     HSIZE == 3'b001 ? 8'h3 << {HADDR[2:1],1'b0} :
                     HSIZE == 3'b010 ? 8'hf << {HADDR[2],2'b0} : 8'hff;


  initial begin
    if ($value$plusargs("iws=%d", iws));
    if ($value$plusargs("dws=%d", dws));
    dws_rand = dws < 0;
    iws_rand = iws < 0;
  end



  always @(negedge HCLK) begin
    if (HREADY) addr = HADDR;
    if (write & HREADY) begin
      if (strb_lat[7]) mem[{laddr[31:3], 3'd7}] = HWDATA[63:56];
      if (strb_lat[6]) mem[{laddr[31:3], 3'd6}] = HWDATA[55:48];
      if (strb_lat[5]) mem[{laddr[31:3], 3'd5}] = HWDATA[47:40];
      if (strb_lat[4]) mem[{laddr[31:3], 3'd4}] = HWDATA[39:32];
      if (strb_lat[3]) mem[{laddr[31:3], 3'd3}] = HWDATA[31:24];
      if (strb_lat[2]) mem[{laddr[31:3], 3'd2}] = HWDATA[23:16];
      if (strb_lat[1]) mem[{laddr[31:3], 3'd1}] = HWDATA[15:08];
      if (strb_lat[0]) mem[{laddr[31:3], 3'd0}] = HWDATA[07:00];
    end
    if (HREADY & HSEL & |HTRANS) begin
      if (MAX_DELAY < 0) begin
`ifdef VERILATOR
        if (iws_rand & ~HPROT[0]) iws = $random & 15;
        if (dws_rand & HPROT[0]) dws = $random & 15;
`else
        if (iws_rand & ~HPROT[0])
          ok = std::randomize(
              iws
          ) with {
            iws dist {
              0 := 10,
              [1 : 3] :/ 2,
              [4 : 15] :/ 1
            };
          };
        if (dws_rand & HPROT[0])
          ok = std::randomize(
              dws
          ) with {
            dws dist {
              0 := 10,
              [1 : 3] :/ 2,
              [4 : 15] :/ 1
            };
          };
`endif
      end else begin
        if (~HPROT[0]) iws = MIN_DELAY + $random % (MAX_DELAY-MIN_DELAY+1);
        if (HPROT[0]) dws = MIN_DELAY + $random % (MAX_DELAY-MIN_DELAY+1);
      end
    end
  end

  logic hresp;

  assign HRDATA = HREADY ? rdata : ~rdata;
  assign HREADYOUT = wscnt == 0;
  assign HRESP = hresp;

  always @(posedge HCLK or negedge HRESETn) begin
    if (~HRESETn) begin
      laddr <= 32'b0;
      write <= 1'b0;
      rdata <= '0;
      wscnt <= 0;
      hresp <= '0;
    end else begin
      if (HREADY & HSEL) begin
        laddr <= HADDR;
        write <= HWRITE & |HTRANS;
        if (|HTRANS & ~HWRITE)
          rdata <= {
            mem[{addr[31:3], 3'd7}] & {8{strb[7]}},
            mem[{addr[31:3], 3'd6}] & {8{strb[6]}},
            mem[{addr[31:3], 3'd5}] & {8{strb[5]}},
            mem[{addr[31:3], 3'd4}] & {8{strb[4]}},
            mem[{addr[31:3], 3'd3}] & {8{strb[3]}},
            mem[{addr[31:3], 3'd2}] & {8{strb[2]}},
            mem[{addr[31:3], 3'd1}] & {8{strb[1]}},
            mem[{addr[31:3], 3'd0}] & {8{strb[0]}}
          };
        strb_lat <= strb;
      end
    end
    if (HREADY & HSEL & |HTRANS) wscnt <= HPROT[0] ? dws[7:0] : iws[7:0];
    else if (wscnt != 0) wscnt <= wscnt - 1;
  end


endmodule
`endif
