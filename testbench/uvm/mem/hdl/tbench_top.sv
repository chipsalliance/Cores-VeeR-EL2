// Copyright (c) 2023 Antmicro
// SPDX-License-Identifier: Apache-2.0

`include "uvm_pkg.sv"

import uvm_pkg::*;

`include "dccm_interface.sv"
`include "dccm_base_test.sv"
`include "dccm_memtest.sv"

module tbench_top #(
    `include "el2_param.vh"
);

  bit clk;
  bit reset;

  always #5 clk = ~clk;

  initial begin
    reset = 1;
    #5 reset = 0;
  end

  initial begin
    $dumpfile("dump.vcd");
    $dumpvars(0, tbench_top);
  end

  dccm_interface intf (
      clk,
      reset
  );

  el2_mem_if mem_export ();

  localparam DCCM_INDEX_DEPTH = ((pt.DCCM_SIZE)*1024)/((pt.DCCM_BYTE_WIDTH)*(pt.DCCM_NUM_BANKS));  // Depth of memory bank
  logic [pt.DCCM_NUM_BANKS-1:0][pt.DCCM_FDATA_WIDTH-1:0] dccm_wr_fdata_bank;
  logic [pt.DCCM_NUM_BANKS-1:0][pt.DCCM_FDATA_WIDTH-1:0] dccm_bank_fdout;

  // 8 Banks, 16KB each (2048 x 72)
  for (genvar i = 0; i < pt.DCCM_NUM_BANKS; i++) begin : gen_dccm_mem
    assign dccm_wr_fdata_bank[i][pt.DCCM_DATA_WIDTH-1:0] = mem_export.dccm_wr_data_bank[i];
    assign dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:pt.DCCM_DATA_WIDTH] = mem_export.dccm_wr_ecc_bank[i];
    assign {mem_export.dccm_bank_ecc[i], mem_export.dccm_bank_dout[i]} = dccm_bank_fdout[i];

    el2_ram #(DCCM_INDEX_DEPTH, 39) ram (
        // Primary ports
        .ME (mem_export.dccm_clken[i]),
        .CLK(mem_export.clk),
        .WE (mem_export.dccm_wren_bank[i]),
        .ADR(mem_export.dccm_addr_bank[i]),
        .D  (dccm_wr_fdata_bank[i]),
        .Q  (dccm_bank_fdout[i]),
        .ROP()
    );
  end : gen_dccm_mem

  el2_lsu_dccm_mem DUT (
      .clk         (intf.clk),
      .active_clk  (intf.clk),
      .rst_l       (~intf.reset),
      .clk_override(1'b0),
      .scan_mode   (1'b0),

      .dccm_wren      (intf.wr_en),
      .dccm_rden      (intf.rd_en),
      .dccm_wr_addr_hi(intf.addr),
      .dccm_wr_addr_lo(intf.addr),
      .dccm_rd_addr_hi(intf.addr),
      .dccm_rd_addr_lo(intf.addr),
      .dccm_wr_data_hi(intf.wdata),
      .dccm_wr_data_lo(intf.wdata),
      .dccm_rd_data_hi(),            // For aligned read/write this should match the lo part
      .dccm_rd_data_lo(intf.rdata),

      .dccm_mem_export(mem_export.veer_dccm)
  );

  // Debug, dump memory signals on each clock cycle
  always @(posedge intf.clk)
    $display(
        "a:%08X w:%d wd:%08X r:%d rd:%08X",
        intf.addr,
        intf.wr_en,
        intf.wdata,
        intf.rd_en,
        intf.rdata
    );

  initial begin
    uvm_config_db#(virtual dccm_interface)::set(uvm_root::get(), "*", "memory_vif", intf);
  end

  initial begin
    run_test();
  end

endmodule
