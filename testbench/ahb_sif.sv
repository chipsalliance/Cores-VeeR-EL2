// SPDX-License-Identifier: Apache-2.0
// Copyright 2019 Western Digital Corporation or its affiliates.
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
//
`ifdef RV_BUILD_AHB_LITE

module ahb_sif (
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

parameter MAILBOX_ADDR = 32'hD0580000;

logic write;
logic [31:0] laddr, addr;
logic [7:0] strb_lat;
logic [63:0] rdata;

bit [7:0] mem [bit[31:0]];
bit [7:0] wscnt;
int dws = 0;
int iws = 0;
bit dws_rand;
bit iws_rand;
bit ok;

// Wires
wire [63:0] WriteData = HWDATA;
wire [7:0] strb =  HSIZE == 3'b000 ? 8'h1 << HADDR[2:0] :
                   HSIZE == 3'b001 ? 8'h3 << {HADDR[2:1],1'b0} :
                   HSIZE == 3'b010 ? 8'hf << {HADDR[2],2'b0} : 8'hff;


wire mailbox_write = write && laddr==MAILBOX_ADDR;


initial begin
    if ($value$plusargs("iws=%d", iws));
    if ($value$plusargs("dws=%d", dws));
    dws_rand = dws < 0;
    iws_rand = iws < 0;
end



always @ (negedge HCLK ) begin
    if(HREADY)
        addr = HADDR;
    if (write & HREADY) begin
        if(strb_lat[7]) mem[{laddr[31:3],3'd7}] = HWDATA[63:56];
        if(strb_lat[6]) mem[{laddr[31:3],3'd6}] = HWDATA[55:48];
        if(strb_lat[5]) mem[{laddr[31:3],3'd5}] = HWDATA[47:40];
        if(strb_lat[4]) mem[{laddr[31:3],3'd4}] = HWDATA[39:32];
        if(strb_lat[3]) mem[{laddr[31:3],3'd3}] = HWDATA[31:24];
        if(strb_lat[2]) mem[{laddr[31:3],3'd2}] = HWDATA[23:16];
        if(strb_lat[1]) mem[{laddr[31:3],3'd1}] = HWDATA[15:08];
        if(strb_lat[0]) mem[{laddr[31:3],3'd0}] = HWDATA[07:00];
    end
    if(HREADY & HSEL & |HTRANS) begin
`ifdef VERILATOR
        if(iws_rand & ~HPROT[0])
            iws = $urandom & 15;
        if(dws_rand & HPROT[0])
            dws = $urandom & 15;
`else
        if(iws_rand & ~HPROT[0])
            ok = std::randomize(iws) with {iws dist {0:=10, [1:3]:/2, [4:15]:/1};};
        if(dws_rand & HPROT[0])
            ok = std::randomize(dws) with {dws dist {0:=10, [1:3]:/2, [4:15]:/1};};
`endif
    end
end


assign HRDATA = HREADY ? rdata : ~rdata;
assign HREADYOUT = wscnt == 0;
assign HRESP = 0;

always @(posedge HCLK or negedge HRESETn) begin
    if(~HRESETn) begin
        laddr <= 32'b0;
        write <= 1'b0;
        rdata <= '0;
        wscnt <= 0;
    end
    else begin
        if(HREADY & HSEL) begin
            laddr <= HADDR;
            write <= HWRITE & |HTRANS;
            if(|HTRANS & ~HWRITE)
                rdata <= {mem[{addr[31:3],3'd7}],
                          mem[{addr[31:3],3'd6}],
                          mem[{addr[31:3],3'd5}],
                          mem[{addr[31:3],3'd4}],
                          mem[{addr[31:3],3'd3}],
                          mem[{addr[31:3],3'd2}],
                          mem[{addr[31:3],3'd1}],
                          mem[{addr[31:3],3'd0}]};
            strb_lat <= strb;
        end
    end
    if(HREADY & HSEL & |HTRANS)
        wscnt <= HPROT[0] ? dws[7:0] : iws[7:0];
    else if(wscnt != 0)
        wscnt <= wscnt-1;
end


endmodule
`endif

`ifdef RV_BUILD_AXI4
module axi_slv #(TAGW=1) (
input                   aclk,
input                   rst_l,
input                   arvalid,
output reg              arready,
input [31:0]            araddr,
input [TAGW-1:0]        arid,
input [7:0]             arlen,
input [1:0]             arburst,
input [2:0]             arsize,

output reg              rvalid,
input                   rready,
output reg [63:0]       rdata,
output reg [1:0]        rresp,
output reg [TAGW-1:0]   rid,
output                  rlast,

input                   awvalid,
output                  awready,
input [31:0]            awaddr,
input [TAGW-1:0]        awid,
input [7:0]             awlen,
input [1:0]             awburst,
input [2:0]             awsize,

input [63:0]            wdata,
input [7:0]             wstrb,
input                   wvalid,
output                  wready,

output  reg             bvalid,
input                   bready,
output reg [1:0]        bresp,
output reg [TAGW-1:0]   bid
);

parameter MAILBOX_ADDR = 32'hD0580000;
parameter MEM_SIZE_DW = 8192;

bit [7:0] mem [bit[31:0]];
bit [63:0] memdata;
wire [63:0] WriteData;
wire mailbox_write;


assign mailbox_write = awvalid && awaddr==MAILBOX_ADDR && rst_l;
assign WriteData = wdata;

always @ ( posedge aclk or negedge rst_l) begin
    if(!rst_l) begin
        rvalid  <= 0;
        bvalid  <= 0;
    end
    else begin
        bid     <= awid;
        rid     <= arid;
        rvalid  <= arvalid;
        bvalid  <= awvalid;
        rdata   <= memdata;
    end
end

always @ ( negedge aclk) begin
    if(arvalid) memdata <= {mem[araddr+7], mem[araddr+6], mem[araddr+5], mem[araddr+4],
                            mem[araddr+3], mem[araddr+2], mem[araddr+1], mem[araddr]};
    if(awvalid) begin
        if(wstrb[7]) mem[awaddr+7] = wdata[63:56];
        if(wstrb[6]) mem[awaddr+6] = wdata[55:48];
        if(wstrb[5]) mem[awaddr+5] = wdata[47:40];
        if(wstrb[4]) mem[awaddr+4] = wdata[39:32];
        if(wstrb[3]) mem[awaddr+3] = wdata[31:24];
        if(wstrb[2]) mem[awaddr+2] = wdata[23:16];
        if(wstrb[1]) mem[awaddr+1] = wdata[15:08];
        if(wstrb[0]) mem[awaddr+0] = wdata[07:00];
    end
end


assign arready = 1'b1;
assign awready = 1'b1;
assign wready  = 1'b1;
assign rresp   = 2'b0;
assign bresp   = 2'b0;
assign rlast   = 1'b1;

endmodule
`endif

