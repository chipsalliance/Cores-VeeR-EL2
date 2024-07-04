//********************************************************************************
// SPDX-License-Identifier: Apache-2.0
// Copyright (c) 2023 Antmicro <www.antmicro.com>
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

module veer_wrapper
  import el2_pkg::*;
#(
    `include "el2_param.vh"
) (
    input logic        clk,
    input logic        rst_l,
    input logic        dbg_rst_l,
    input logic [31:1] rst_vec,
    input logic        nmi_int,
    input logic [31:1] nmi_vec,
    input logic [31:1] jtag_id,


    output logic [31:0] trace_rv_i_insn_ip,
    output logic [31:0] trace_rv_i_address_ip,
    output logic        trace_rv_i_valid_ip,
    output logic        trace_rv_i_exception_ip,
    output logic [ 4:0] trace_rv_i_ecause_ip,
    output logic        trace_rv_i_interrupt_ip,
    output logic [31:0] trace_rv_i_tval_ip,

    // Bus signals
`ifdef RV_BUILD_AXI4
    //-------------------------- LSU AXI signals--------------------------
    // AXI Write Channels
    output logic                      lsu_axi_awvalid,
    input  logic                      lsu_axi_awready,
    output logic [pt.LSU_BUS_TAG-1:0] lsu_axi_awid,
    output logic [              31:0] lsu_axi_awaddr,
    output logic [               3:0] lsu_axi_awregion,
    output logic [               7:0] lsu_axi_awlen,
    output logic [               2:0] lsu_axi_awsize,
    output logic [               1:0] lsu_axi_awburst,
    output logic                      lsu_axi_awlock,
    output logic [               3:0] lsu_axi_awcache,
    output logic [               2:0] lsu_axi_awprot,
    output logic [               3:0] lsu_axi_awqos,

    output logic        lsu_axi_wvalid,
    input  logic        lsu_axi_wready,
    output logic [63:0] lsu_axi_wdata,
    output logic [ 7:0] lsu_axi_wstrb,
    output logic        lsu_axi_wlast,

    input  logic                      lsu_axi_bvalid,
    output logic                      lsu_axi_bready,
    input  logic [               1:0] lsu_axi_bresp,
    input  logic [pt.LSU_BUS_TAG-1:0] lsu_axi_bid,

    // AXI Read Channels
    output logic                      lsu_axi_arvalid,
    input  logic                      lsu_axi_arready,
    output logic [pt.LSU_BUS_TAG-1:0] lsu_axi_arid,
    output logic [              31:0] lsu_axi_araddr,
    output logic [               3:0] lsu_axi_arregion,
    output logic [               7:0] lsu_axi_arlen,
    output logic [               2:0] lsu_axi_arsize,
    output logic [               1:0] lsu_axi_arburst,
    output logic                      lsu_axi_arlock,
    output logic [               3:0] lsu_axi_arcache,
    output logic [               2:0] lsu_axi_arprot,
    output logic [               3:0] lsu_axi_arqos,

    input  logic                      lsu_axi_rvalid,
    output logic                      lsu_axi_rready,
    input  logic [pt.LSU_BUS_TAG-1:0] lsu_axi_rid,
    input  logic [              63:0] lsu_axi_rdata,
    input  logic [               1:0] lsu_axi_rresp,
    input  logic                      lsu_axi_rlast,

    //-------------------------- IFU AXI signals--------------------------
    // AXI Write Channels
    output logic                      ifu_axi_awvalid,
    input  logic                      ifu_axi_awready,
    output logic [pt.IFU_BUS_TAG-1:0] ifu_axi_awid,
    output logic [              31:0] ifu_axi_awaddr,
    output logic [               3:0] ifu_axi_awregion,
    output logic [               7:0] ifu_axi_awlen,
    output logic [               2:0] ifu_axi_awsize,
    output logic [               1:0] ifu_axi_awburst,
    output logic                      ifu_axi_awlock,
    output logic [               3:0] ifu_axi_awcache,
    output logic [               2:0] ifu_axi_awprot,
    output logic [               3:0] ifu_axi_awqos,

    output logic        ifu_axi_wvalid,
    input  logic        ifu_axi_wready,
    output logic [63:0] ifu_axi_wdata,
    output logic [ 7:0] ifu_axi_wstrb,
    output logic        ifu_axi_wlast,

    input  logic                      ifu_axi_bvalid,
    output logic                      ifu_axi_bready,
    input  logic [               1:0] ifu_axi_bresp,
    input  logic [pt.IFU_BUS_TAG-1:0] ifu_axi_bid,

    // AXI Read Channels
    output logic                      ifu_axi_arvalid,
    input  logic                      ifu_axi_arready,
    output logic [pt.IFU_BUS_TAG-1:0] ifu_axi_arid,
    output logic [              31:0] ifu_axi_araddr,
    output logic [               3:0] ifu_axi_arregion,
    output logic [               7:0] ifu_axi_arlen,
    output logic [               2:0] ifu_axi_arsize,
    output logic [               1:0] ifu_axi_arburst,
    output logic                      ifu_axi_arlock,
    output logic [               3:0] ifu_axi_arcache,
    output logic [               2:0] ifu_axi_arprot,
    output logic [               3:0] ifu_axi_arqos,

    input  logic                      ifu_axi_rvalid,
    output logic                      ifu_axi_rready,
    input  logic [pt.IFU_BUS_TAG-1:0] ifu_axi_rid,
    input  logic [              63:0] ifu_axi_rdata,
    input  logic [               1:0] ifu_axi_rresp,
    input  logic                      ifu_axi_rlast,

    //-------------------------- SB AXI signals--------------------------
    // AXI Write Channels
    output logic                     sb_axi_awvalid,
    input  logic                     sb_axi_awready,
    output logic [pt.SB_BUS_TAG-1:0] sb_axi_awid,
    output logic [             31:0] sb_axi_awaddr,
    output logic [              3:0] sb_axi_awregion,
    output logic [              7:0] sb_axi_awlen,
    output logic [              2:0] sb_axi_awsize,
    output logic [              1:0] sb_axi_awburst,
    output logic                     sb_axi_awlock,
    output logic [              3:0] sb_axi_awcache,
    output logic [              2:0] sb_axi_awprot,
    output logic [              3:0] sb_axi_awqos,

    output logic        sb_axi_wvalid,
    input  logic        sb_axi_wready,
    output logic [63:0] sb_axi_wdata,
    output logic [ 7:0] sb_axi_wstrb,
    output logic        sb_axi_wlast,

    input  logic                     sb_axi_bvalid,
    output logic                     sb_axi_bready,
    input  logic [              1:0] sb_axi_bresp,
    input  logic [pt.SB_BUS_TAG-1:0] sb_axi_bid,

    // AXI Read Channels
    output logic                     sb_axi_arvalid,
    input  logic                     sb_axi_arready,
    output logic [pt.SB_BUS_TAG-1:0] sb_axi_arid,
    output logic [             31:0] sb_axi_araddr,
    output logic [              3:0] sb_axi_arregion,
    output logic [              7:0] sb_axi_arlen,
    output logic [              2:0] sb_axi_arsize,
    output logic [              1:0] sb_axi_arburst,
    output logic                     sb_axi_arlock,
    output logic [              3:0] sb_axi_arcache,
    output logic [              2:0] sb_axi_arprot,
    output logic [              3:0] sb_axi_arqos,

    input  logic                     sb_axi_rvalid,
    output logic                     sb_axi_rready,
    input  logic [pt.SB_BUS_TAG-1:0] sb_axi_rid,
    input  logic [             63:0] sb_axi_rdata,
    input  logic [              1:0] sb_axi_rresp,
    input  logic                     sb_axi_rlast,

    //-------------------------- DMA AXI signals--------------------------
    // AXI Write Channels
    input  logic                      dma_axi_awvalid,
    output logic                      dma_axi_awready,
    input  logic [pt.DMA_BUS_TAG-1:0] dma_axi_awid,
    input  logic [              31:0] dma_axi_awaddr,
    input  logic [               2:0] dma_axi_awsize,
    input  logic [               2:0] dma_axi_awprot,
    input  logic [               7:0] dma_axi_awlen,
    input  logic [               1:0] dma_axi_awburst,


    input  logic        dma_axi_wvalid,
    output logic        dma_axi_wready,
    input  logic [63:0] dma_axi_wdata,
    input  logic [ 7:0] dma_axi_wstrb,
    input  logic        dma_axi_wlast,

    output logic                      dma_axi_bvalid,
    input  logic                      dma_axi_bready,
    output logic [               1:0] dma_axi_bresp,
    output logic [pt.DMA_BUS_TAG-1:0] dma_axi_bid,

    // AXI Read Channels
    input  logic                      dma_axi_arvalid,
    output logic                      dma_axi_arready,
    input  logic [pt.DMA_BUS_TAG-1:0] dma_axi_arid,
    input  logic [              31:0] dma_axi_araddr,
    input  logic [               2:0] dma_axi_arsize,
    input  logic [               2:0] dma_axi_arprot,
    input  logic [               7:0] dma_axi_arlen,
    input  logic [               1:0] dma_axi_arburst,

    output logic                      dma_axi_rvalid,
    input  logic                      dma_axi_rready,
    output logic [pt.DMA_BUS_TAG-1:0] dma_axi_rid,
    output logic [              63:0] dma_axi_rdata,
    output logic [               1:0] dma_axi_rresp,
    output logic                      dma_axi_rlast,
`endif

`ifdef RV_BUILD_AHB_LITE
    //// AHB LITE BUS
    output logic [31:0] haddr,
    output logic [ 2:0] hburst,
    output logic        hmastlock,
    output logic [ 3:0] hprot,
    output logic [ 2:0] hsize,
    output logic [ 1:0] htrans,
    output logic        hwrite,

    input logic [63:0] hrdata,
    input logic        hready,
    input logic        hresp,

    // LSU AHB Master
    output logic [31:0] lsu_haddr,
    output logic [ 2:0] lsu_hburst,
    output logic        lsu_hmastlock,
    output logic [ 3:0] lsu_hprot,
    output logic [ 2:0] lsu_hsize,
    output logic [ 1:0] lsu_htrans,
    output logic        lsu_hwrite,
    output logic [63:0] lsu_hwdata,

    input  logic [63:0] lsu_hrdata,
    input  logic        lsu_hready,
    input  logic        lsu_hresp,
    // Debug Syster Bus AHB
    output logic [31:0] sb_haddr,
    output logic [ 2:0] sb_hburst,
    output logic        sb_hmastlock,
    output logic [ 3:0] sb_hprot,
    output logic [ 2:0] sb_hsize,
    output logic [ 1:0] sb_htrans,
    output logic        sb_hwrite,
    output logic [63:0] sb_hwdata,

    input logic [63:0] sb_hrdata,
    input logic        sb_hready,
    input logic        sb_hresp,

    // DMA Slave
    input logic        dma_hsel,
    input logic [31:0] dma_haddr,
    input logic [ 2:0] dma_hburst,
    input logic        dma_hmastlock,
    input logic [ 3:0] dma_hprot,
    input logic [ 2:0] dma_hsize,
    input logic [ 1:0] dma_htrans,
    input logic        dma_hwrite,
    input logic [63:0] dma_hwdata,
    input logic        dma_hreadyin,

    output logic [63:0] dma_hrdata,
    output logic        dma_hreadyout,
    output logic        dma_hresp,
`endif
    // clk ratio signals
    input  logic        lsu_bus_clk_en,  // Clock ratio b/w cpu core clk & AHB master interface
    input  logic        ifu_bus_clk_en,  // Clock ratio b/w cpu core clk & AHB master interface
    input  logic        dbg_bus_clk_en,  // Clock ratio b/w cpu core clk & AHB master interface
    input  logic        dma_bus_clk_en,  // Clock ratio b/w cpu core clk & AHB slave interface

    // all of these test inputs are brought to top-level; must be tied off based on usage by physical design (ie. icache or not, iccm or not, dccm or not)

    input                                   el2_ic_data_ext_in_pkt_t  [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0] ic_data_ext_in_pkt,
    input el2_ic_tag_ext_in_pkt_t [pt.ICACHE_NUM_WAYS-1:0] ic_tag_ext_in_pkt,

    input logic                      timer_int,
    input logic                      soft_int,
    input logic [pt.PIC_TOTAL_INT:1] extintsrc_req,

    output logic dec_tlu_perfcnt0,  // toggles when slot0 perf counter 0 has an event inc
    output logic dec_tlu_perfcnt1,
    output logic dec_tlu_perfcnt2,
    output logic dec_tlu_perfcnt3,

    // ports added by the soc team
    input  logic jtag_tck,     // JTAG clk
    input  logic jtag_tms,     // JTAG TMS
    input  logic jtag_tdi,     // JTAG tdi
    input  logic jtag_trst_n,  // JTAG Reset
    output logic jtag_tdo,     // JTAG TDO
    output logic jtag_tdoEn,   // JTAG Test Data Output enable

    input logic [31:4] core_id,

    // Memory Export Interface
    output logic mem_clk,
    // ICCM
    output logic [pt.ICCM_NUM_BANKS-1:0] iccm_clken,
    output logic [pt.ICCM_NUM_BANKS-1:0] iccm_wren_bank,
    output logic [pt.ICCM_NUM_BANKS-1:0][pt.ICCM_BITS-1:pt.ICCM_BANK_INDEX_LO] iccm_addr_bank,
    output logic [pt.ICCM_NUM_BANKS-1:0][31:0] iccm_bank_wr_data,
    output logic [pt.ICCM_NUM_BANKS-1:0][pt.ICCM_ECC_WIDTH-1:0] iccm_bank_wr_ecc,
    input logic [pt.ICCM_NUM_BANKS-1:0][31:0] iccm_bank_dout,
    input logic [pt.ICCM_NUM_BANKS-1:0][pt.ICCM_ECC_WIDTH-1:0] iccm_bank_ecc,
    // DCCM
    output logic [pt.DCCM_NUM_BANKS-1:0] dccm_clken,
    output logic [pt.DCCM_NUM_BANKS-1:0] dccm_wren_bank,
    output logic [pt.DCCM_NUM_BANKS-1:0][pt.DCCM_BITS-1:(pt.DCCM_BANK_BITS+2)] dccm_addr_bank,
    output logic [pt.DCCM_NUM_BANKS-1:0][pt.DCCM_DATA_WIDTH-1:0] dccm_wr_data_bank,
    output logic [pt.DCCM_NUM_BANKS-1:0][pt.DCCM_FDATA_WIDTH-pt.DCCM_DATA_WIDTH-1:0] dccm_wr_ecc_bank,
    input logic [pt.DCCM_NUM_BANKS-1:0][pt.DCCM_DATA_WIDTH-1:0] dccm_bank_dout,
    input logic [pt.DCCM_NUM_BANKS-1:0][pt.DCCM_FDATA_WIDTH-pt.DCCM_DATA_WIDTH-1:0] dccm_bank_ecc,

    // ICCM/DCCM ECC status
    output logic iccm_ecc_single_error,
    output logic iccm_ecc_double_error,
    output logic dccm_ecc_single_error,
    output logic dccm_ecc_double_error,

    // external MPC halt/run interface
    input  logic mpc_debug_halt_req,  // Async halt request
    input  logic mpc_debug_run_req,   // Async run request
    input  logic mpc_reset_run_req,   // Run/halt after reset
    output logic mpc_debug_halt_ack,  // Halt ack
    output logic mpc_debug_run_ack,   // Run ack
    output logic debug_brkpt_status,  // debug breakpoint

    input logic i_cpu_halt_req,  // Async halt req to CPU
    output logic o_cpu_halt_ack,  // core response to halt
    output logic o_cpu_halt_status,  // 1'b1 indicates core is halted
    output logic                            o_debug_mode_status, // Core to the PMU that core is in debug mode. When core is in debug mode, the PMU should refrain from sendng a halt or run request
    input logic i_cpu_run_req,  // Async restart req to CPU
    output logic o_cpu_run_ack,  // Core response to run req
    input logic scan_mode,  // To enable scan mode
    input logic mbist_mode,  // to enable mbist

    // DMI port for uncore
    input  logic        dmi_uncore_enable,
    output logic        dmi_uncore_en,
    output logic        dmi_uncore_wr_en,
    output logic [ 6:0] dmi_uncore_addr,
    output logic [31:0] dmi_uncore_wdata,
    input  logic [31:0] dmi_uncore_rdata
);

  el2_mem_if mem_export ();
  assign mem_clk                   = mem_export.clk;
  assign dccm_clken                = mem_export.dccm_clken;
  assign dccm_wren_bank            = mem_export.dccm_wren_bank;
  assign dccm_addr_bank            = mem_export.dccm_addr_bank;
  assign dccm_wr_data_bank         = mem_export.dccm_wr_data_bank;
  assign dccm_wr_ecc_bank          = mem_export.dccm_wr_ecc_bank;
  assign mem_export.dccm_bank_dout = dccm_bank_dout;
  assign mem_export.dccm_bank_ecc  = dccm_bank_ecc;
  assign iccm_clken                = mem_export.iccm_clken;
  assign iccm_wren_bank            = mem_export.iccm_wren_bank;
  assign iccm_addr_bank            = mem_export.iccm_addr_bank;
  assign iccm_bank_wr_data         = mem_export.iccm_bank_wr_data;
  assign iccm_bank_wr_ecc          = mem_export.iccm_bank_wr_ecc;
  assign mem_export.iccm_bank_dout = iccm_bank_dout;
  assign mem_export.iccm_bank_ecc  = iccm_bank_ecc;

  el2_veer_wrapper rvtop (
      .el2_mem_export(mem_export.veer_sram_src),
      .*
  );

endmodule
