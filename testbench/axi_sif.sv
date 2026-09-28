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

/*
  AXI memory model
*/
module axi_slv #(
    parameter unsigned TAGW = 1,
    // Min/max cycle count to drop AWREADY for after a successful AW transaction
    parameter unsigned AWREADY_DELAY_MIN = 0,
    parameter unsigned AWREADY_DELAY_MAX = 0,
    // Min/max cycle count to drop WREADY for after a successful W transaction
    parameter unsigned WREADY_DELAY_MIN  = 0,
    parameter unsigned WREADY_DELAY_MAX  = 0,
    // Min/max cycle count to drop ARREADY for after a successful AR transaction
    parameter unsigned ARREADY_DELAY_MIN = 0,
    parameter unsigned ARREADY_DELAY_MAX = 0,
    // Min/max latency between write request and response (in cycles)
    parameter unsigned WRITE_LATENCY_MIN = 0,
    parameter unsigned WRITE_LATENCY_MAX = 0,
    // Min/max latency between read request and response (in cycles)
    parameter unsigned READ_LATENCY_MIN  = 0,
    parameter unsigned READ_LATENCY_MAX  = 0
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

  typedef struct packed {
    bit [    31:0] addr;
    bit [TAGW-1:0] id;
  } ax_t;

  typedef struct packed {
    bit [63:0] data;
    bit [ 7:0] strb;
  } w_t;

  ax_t write_addr_q [$];
  w_t  write_data_q [$];
  ax_t read_addr_q  [$];

  initial begin
    wready  = '0;
    awready = '0;
    arready = '0;
    rlast   = '0;
    rvalid  = '0;
    bvalid  = '0;
  end

  // Write request
  initial forever begin
    @(posedge aclk or negedge rst_l);
    awready <= rst_l;
    if (awvalid & awready) begin
      write_addr_q.push_back('{addr: {awaddr[31:3], 3'b000}, id: awid});
      awready <= '0;
      for (int i=$urandom_range(AWREADY_DELAY_MIN, AWREADY_DELAY_MAX); i>0; i--) begin
        @(posedge aclk or negedge rst_l);
        if (!rst_l) break;
      end
      awready <= rst_l;
    end
  end

  // Write data
  initial forever begin
    @(posedge aclk or negedge rst_l);
    wready <= rst_l;
    if (wvalid & wready) begin
      write_data_q.push_back('{data: wdata, strb: wstrb});
      wready <= '0;
      for (int i=$urandom_range(WREADY_DELAY_MIN, WREADY_DELAY_MAX); i>0; i--) begin
        @(posedge aclk or negedge rst_l);
        if (!rst_l) break;
      end
      wready <= rst_l;
    end
  end

  // Write execution
  initial forever begin
    @(posedge aclk or negedge rst_l);
    if (!rst_l) continue;

    if (write_addr_q.size() > 0 && write_data_q.size() > 0) begin
      ax_t aw;
      w_t   w;

      aw = write_addr_q.pop_front();
      w  = write_data_q.pop_front();

      for (int i=$urandom_range(WRITE_LATENCY_MIN, WRITE_LATENCY_MAX); i>0; i--) begin
        @(posedge aclk or negedge rst_l);
        if (!rst_l) break;
      end
      if (!rst_l) continue;

      if (w.strb[7]) mem[aw.addr+7] = w.data[63:56];
      if (w.strb[6]) mem[aw.addr+6] = w.data[55:48];
      if (w.strb[5]) mem[aw.addr+5] = w.data[47:40];
      if (w.strb[4]) mem[aw.addr+4] = w.data[39:32];
      if (w.strb[3]) mem[aw.addr+3] = w.data[31:24];
      if (w.strb[2]) mem[aw.addr+2] = w.data[23:16];
      if (w.strb[1]) mem[aw.addr+1] = w.data[15:08];
      if (w.strb[0]) mem[aw.addr+0] = w.data[07:00];

      bvalid <= '1;
      bid    <= aw.id;
      bresp  <= '0;

      do begin @(posedge aclk or negedge rst_l); end while (!bready || !rst_l);

      bvalid <= '0;
    end
  end

  // Read request
  initial forever begin
    @(posedge aclk or negedge rst_l);
    arready <= rst_l;
    if (arvalid & arready) begin
      read_addr_q.push_back('{addr: {araddr[31:3], 3'b000}, id: arid});
      arready <= '0;
      for (int i=$urandom_range(ARREADY_DELAY_MIN, ARREADY_DELAY_MAX); i>0; i--) begin
        @(posedge aclk or negedge rst_l);
        if (!rst_l) break;
      end
      arready <= rst_l;
    end
  end

  // Read execution
  initial forever begin
    @(posedge aclk or negedge rst_l);
    if (!rst_l) continue;

    if (read_addr_q.size() > 0) begin
      ax_t ar;
      ar = read_addr_q.pop_front();

      for (int i=$urandom_range(READ_LATENCY_MIN, READ_LATENCY_MAX); i>0; i--) begin
        @(posedge aclk or negedge rst_l);
        if (!rst_l) break;
      end
      if (!rst_l) continue;

      rdata <= {
        mem[ar.addr+7],
        mem[ar.addr+6],
        mem[ar.addr+5],
        mem[ar.addr+4],
        mem[ar.addr+3],
        mem[ar.addr+2],
        mem[ar.addr+1],
        mem[ar.addr]
      };

      rvalid <= '1;
      rid    <= ar.id;
      rlast  <= '1;
      rresp  <= '0;

      do begin @(posedge aclk or negedge rst_l); end while (!rready || !rst_l);

      rvalid <= '0;
      rlast  <= '0;
    end
  end
endmodule

/*
  AXI manager model. Issues randomized requests to the given address range
*/
module axi_mst #(
    // AXI ID width
    parameter unsigned TAGW = 1,
    // Number of AXI IDs to use starting from 0
    parameter unsigned TAGC = 1,
    // Address range count
    parameter unsigned ADDR_N = 1,
    // Address ranges boundaries. Concatenated 32b each
    parameter bit [ADDR_N*32-1:0] ADDR_LO = 0,
    parameter bit [ADDR_N*32-1:0] ADDR_HI = 0,
    // Transaction interval range
    parameter unsigned INTERVAL_MIN = 10,
    parameter unsigned INTERVAL_MAX = 100,
    // Min/max cycle count to drop BREADY for after a successful B transaction
    parameter unsigned BREADY_DELAY_MIN = 0,
    parameter unsigned BREADY_DELAY_MAX = 0,
    // Min/max cycle count to drop RREADY for after a successful R transaction
    parameter unsigned RREADY_DELAY_MIN = 0,
    parameter unsigned RREADY_DELAY_MAX = 0
) (
    input  logic            aclk,
    input  logic            aresetn,

    input  logic            enable,

    output logic            arvalid,
    input  logic            arready,
    output logic [    31:0] araddr,
    output logic [TAGW-1:0] arid,
    output logic [     7:0] arlen,
    output logic [     1:0] arburst,
    output logic [     2:0] arsize,

    input  logic            rvalid,
    output logic            rready,
    input  logic [    63:0] rdata,
    input  logic [     1:0] rresp,
    input  logic [TAGW-1:0] rid,
    input  logic            rlast,

    output logic            awvalid,
    input  logic            awready,
    output logic [    31:0] awaddr,
    output logic [TAGW-1:0] awid,
    output logic [     7:0] awlen,
    output logic [     1:0] awburst,
    output logic [     2:0] awsize,

    output logic [    63:0] wdata,
    output logic [     7:0] wstrb,
    output logic            wlast,
    output logic            wvalid,
    input  logic            wready,

    input  logic            bvalid,
    output logic            bready,
    input  logic [     1:0] bresp,
    input  logic [TAGW-1:0] bid
);

  typedef struct packed {
    bit [    31:0] addr;
    bit [TAGW-1:0] id;
  } ax_t;

  typedef struct packed {
    bit [    63:0] data;
    bit [     7:0] strb;
  } w_t;

  function automatic bit [31:0] randomize_address ();
    int        which;
    bit [31:0] addr_lo;
    bit [31:0] addr_hi;

    which   = $urandom_range(0, ADDR_N - 1);
    addr_lo = (ADDR_LO >> (32 * which));
    addr_hi = (ADDR_HI >> (32 * which));

    return $urandom_range(addr_lo, addr_hi) & 32'hFFFF_FFF8; // Align to 8
  endfunction

  bit [TAGC-1:0] pending_w;
  bit [TAGC-1:0] pending_r;

  ax_t write_addr_q [$];
  w_t  write_data_q [$];
  ax_t read_addr_q  [$];

  bit [TAGW-1:0] next_awid;
  bit [TAGW-1:0] next_arid;

  // Generate write requests
  initial forever begin
    @(posedge aclk or negedge aresetn);
    if (!aresetn) begin
      pending_w = '0;
      next_awid = '0;

    end else begin

      // There are free slots
      if (pending_w != {TAGC{1'b1}} && enable) begin
        bit [TAGW-1:0] tag;
        ax_t           aw;
        w_t            w;

        // Wait
        for (int i=$urandom_range(INTERVAL_MIN, INTERVAL_MAX); i>0; i--) begin
          @(posedge aclk or negedge aresetn);
          if (!aresetn) break;
        end
        if (!aresetn) continue;

        // Find the free slot
        for (int i=0; i<TAGC; ++i) begin
          if (!pending_w[next_awid]) break;
          next_awid = (next_awid + 1) % TAGC;
        end

        // Randomize
        aw.addr = randomize_address();
        aw.id   = next_awid;
/* verilator lint_off IGNOREDRETURN */
        std::randomize(w);
/* verilator lint_on IGNOREDRETURN */

        // Enqueue
        pending_w[next_awid] = 1'b1;
        next_awid = (next_awid + 1) % TAGC;
        write_addr_q.push_back(aw);
        write_data_q.push_back(w);
      end
    end
  end

  // Generate read requests
  initial forever begin
    @(posedge aclk or negedge aresetn);
    if (!aresetn) begin
      pending_r = '0;
      next_arid = '0;

    end else begin

      // There are free slots
      if (pending_r != {TAGC{1'b1}} && enable) begin
        bit [TAGW-1:0] tag;
        ax_t           ar;

        // Wait
        for (int i=$urandom_range(INTERVAL_MIN, INTERVAL_MAX); i>0; i--) begin
          @(posedge aclk or negedge aresetn);
          if (!aresetn) break;
        end
        if (!aresetn) continue;

        // Find the free slot
        for (int i=0; i<TAGC; ++i) begin
          if (!pending_r[next_arid]) break;
          next_arid = (next_arid + 1) % TAGC;
        end

        // Randomize
        ar.addr = randomize_address();
        ar.id   = next_arid;

        // Enqueue
        pending_r[next_arid] = 1'b1;
        next_arid = (next_arid + 1) % TAGC;
        read_addr_q.push_back(ar);
      end
    end
  end

  // Handle responses
  always @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
      write_addr_q.delete();
      write_data_q.delete();
      read_addr_q.delete();
    end else begin
      if (bvalid && bready) begin
        pending_w[bid] = '0;
      end
      if (rvalid && rready && rlast) begin
        pending_r[rid] = '0;
      end
    end
  end

  // AW
  always @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
      awvalid <= '0;
    end else begin

      // Begin
      if (!awvalid && write_addr_q.size() > 0) begin
        ax_t aw;
        aw = write_addr_q.pop_front();

        awvalid <= '1;
        awaddr  <= aw.addr;
        awid    <= aw.id;
        awlen   <= '0; // 1
        awburst <=  1; // INCR
        awsize  <=  3; // 8B
      // Finish
      end else if (awvalid && awready) begin
        awvalid <= '0;
      end
    end
  end

  // W
  always @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
      wvalid <= '0;
    end else begin

      // Begin
      if (!wvalid && write_data_q.size() > 0) begin
        w_t w;
        w = write_data_q.pop_front();

        wvalid <= '1;
        wdata  <= w.data;
        wstrb  <= w.strb;
        wlast  <= '1;
      // Finish
      end else if (wvalid && wready) begin
        wvalid <= '0;
      end
    end
  end

  // B
  initial forever begin
    @(posedge aclk or negedge aresetn)
    bready <= aresetn;
    if (!aresetn) continue;

    if (bvalid && bready) begin
      bready <= '0;
      for (int i=$urandom_range(BREADY_DELAY_MIN, BREADY_DELAY_MAX); i>0; i--) begin
        @(posedge aclk or negedge aresetn);
        if (!aresetn) break;
      end
      bready <= aresetn;
    end
  end

  // AR
  always @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
      arvalid <= '0;
    end else begin

      // Begin
      if (!arvalid && read_addr_q.size() > 0) begin
        ax_t ar;
        ar = read_addr_q.pop_front();

        arvalid <= '1;
        araddr  <= ar.addr;
        arid    <= ar.id;
        arlen   <= '0; // 1
        arburst <=  1; // INCR
        arsize  <=  3; // 8B
      // Finish
      end else if (arvalid && arready) begin
        arvalid <= '0;
      end
    end
  end

  // R
  initial forever begin
    @(posedge aclk or negedge aresetn)
    rready <= aresetn;
    if (!aresetn) continue;

    if (rvalid && rready) begin
      rready <= '0;
      for (int i=$urandom_range(RREADY_DELAY_MIN, RREADY_DELAY_MAX); i>0; i--) begin
        @(posedge aclk or negedge aresetn);
        if (!aresetn) break;
      end
      rready <= aresetn;
    end
  end
endmodule

`endif
