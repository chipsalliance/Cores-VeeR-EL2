// SPDX-License-Identifier: Apache-2.0
// Copyright (c) 2026 Antmicro <www.antmicro.com>

/*
  This interface encapsulates clocking, trace port and VeeR internal signals
  for execution trace monitoring
*/
interface trace_monitor_if();
    logic        clk;
    logic        rst_n;

    logic [31:0] trace_insn;
    logic [31:0] trace_address;
    logic        trace_valid;
    logic        trace_exception;
    logic [ 4:0] trace_ecause;
    logic        trace_interrupt;
    logic [31:0] trace_tval;

    // GPR writes
    logic        gpr_wvalid;
    logic [ 4:0] gpr_waddr;
    logic [31:0] gpr_wdata;

    // CSR writes
    logic        csr_wvalid;
    logic [11:0] csr_waddr;
    logic [31:0] csr_wdata;

    // Deferred non-blocking exu_div_resultGPR loads
    logic        nonblock_load_wvalid;
    logic [ 4:0] nonblock_load_waddr;
    logic [31:0] nonblock_load_wdata;

    // Out-of-pipeline division result
    logic        div_wvalid;
    logic [ 4:0] div_waddr;
    logic [31:0] div_wdata;

endinterface
