// SPDX-License-Identifier: Apache-2.0
// Copyright 2019 Western Digital Corporation or its affiliates.
// Copyright 2026 Antmicro <www.antmicro.com>
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
`ifdef RV_BUILD_AXI4

module axi_slv #(
    TAGW = 1
) (
    input                 aclk,
    input                 rst_l,
    input                 arvalid,
    output reg            arready,
    input      [    31:0] araddr,
    input      [TAGW-1:0] arid,
    input      [     7:0] arlen,
    input      [     1:0] arburst,
    input      [     2:0] arsize,

    output reg            rvalid,
    input                 rready,
    output reg [    63:0] rdata,
    output reg [     1:0] rresp,
    output reg [TAGW-1:0] rid,
    output reg            rlast,

    input             awvalid,
    output reg        awready,
    input  [    31:0] awaddr,
    input  [TAGW-1:0] awid,
    input  [     7:0] awlen,
    input  [     1:0] awburst,
    input  [     2:0] awsize,

    input  [63:0] wdata,
    input  [ 7:0] wstrb,
    input         wvalid,
    output reg    wready,

    output reg            bvalid,
    input                 bready,
    output reg [     1:0] bresp,
    output reg [TAGW-1:0] bid
);

  bit [7:0] mem[bit [31:0]];
  bit [31:0] write_address;
  bit [31:0] read_address;

  initial begin
    wready  = 1;
    awready = 1;
    arready = 1'b1;
    rlast   = 1'b0;
    rvalid  = 0;
    bvalid  = 0;
  end

  always @(posedge aclk) begin
    if (arvalid && arready) begin
      read_address = {araddr[31:3], 3'b000};
       rdata <= {
        mem[read_address+7],
        mem[read_address+6],
        mem[read_address+5],
        mem[read_address+4],
        mem[read_address+3],
        mem[read_address+2],
        mem[read_address+1],
        mem[read_address]
      };
       arready <= 0;
       rvalid <= 1;
       rid <= arid;
       rlast <= 1;
       rresp <= 0;
    end else if (rready) begin
       rvalid <= 0;
       arready <= 1;
       rlast <= 0;
    end

    if (awvalid) begin
       write_address = {awaddr[31:3], 3'b000};
       awready <= 0;
    end
     if (wvalid) begin
        bid    <= awid;
        bvalid <= 1;
        wready <= 0;
        bresp <= 0;
      if (wstrb[7]) mem[write_address+7] = wdata[63:56];
      if (wstrb[6]) mem[write_address+6] = wdata[55:48];
      if (wstrb[5]) mem[write_address+5] = wdata[47:40];
      if (wstrb[4]) mem[write_address+4] = wdata[39:32];
      if (wstrb[3]) mem[write_address+3] = wdata[31:24];
      if (wstrb[2]) mem[write_address+2] = wdata[23:16];
      if (wstrb[1]) mem[write_address+1] = wdata[15:08];
      if (wstrb[0]) mem[write_address+0] = wdata[07:00];
     end if (bready && bvalid) begin
        bvalid <= 0;
        awready <= 1;
        wready <= 1;
     end
  end
endmodule

`endif
