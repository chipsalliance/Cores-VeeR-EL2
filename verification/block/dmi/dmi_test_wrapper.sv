// Copyright (c) 2023 Antmicro
// SPDX-License-Identifier: Apache-2.0

module dmi_test_wrapper
  import el2_pkg::*;
#(
    `include "el2_param.vh"
) (
    // JTAG signals
    input  trst_n,    // JTAG reset
    input  tck,       // JTAG clock
    input  tms,       // Test mode select
    input  tdi,       // Test Data Input
    output tdo,       // Test Data Output
    output tdoEnable, // Test Data Output enable

    // Processor Signals
    input core_rst_n,  // Core reset
    input core_clk,  // Core clock
    input [31:1] jtag_id,
    output [31:0] rd_data,  // 32 bit Read data from  Processor
    output dmi_hard_reset,

    // Uncore access enable
    input wire uncore_enable,

    // DMI downstream for core
    output wire dmi_core_en,
    output wire dmi_core_wr_en,
    output wire [6:0] dmi_core_addr,
    output wire [31:0] dmi_core_wdata,
    input wire [31:0] dmi_core_rdata,

    // DMI downstream for uncore
    output wire dmi_uncore_en,
    output wire dmi_uncore_wr_en,
    output wire [6:0] dmi_uncore_addr,
    output wire [31:0] dmi_uncore_wdata,
    input wire [31:0] dmi_uncore_rdata
);

  logic [ 6:0] reg_wr_addr;  // Reg address to Processor
  logic [31:0] reg_wr_data;  // Reg address to Processor
  logic        reg_en;  // Read enable to Processor
  logic        reg_wr_en;  // Write enable to Processor

  logic        dmi_en;
  logic        dmi_wr_en;
  logic [ 6:0] dmi_addr;
  logic [31:0] dmi_wdata;
  logic [31:0] dmi_rdata;

  assign dmi_en = reg_en;
  assign dmi_wr_en = reg_wr_en;
  assign dmi_addr = reg_wr_addr;
  assign dmi_wdata = reg_wr_data;
  assign rd_data = dmi_rdata;

  dmi_wrapper wrapper (.*);

  dmi_mux mux (.*);

endmodule
