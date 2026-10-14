// SPDX-License-Identifier: Apache-2.0
// Copyright (c) 2026 Antmicro <www.antmicro.com>
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
// $Id$
//
// Function: Synthesis netlist top wrapper file with el2_veer/mem instantiated inside
// Comments:
//
//********************************************************************************

`include "common_defines.vh"

module el2_veer_wrapper_gate_level
import el2_pkg::*;
 #(
`include "el2_param.vh"
)
(
   input logic                             clk,
   input logic                             rst_l,
   input logic                             dbg_rst_l,
   // rst_vec is supposed to be tied to constant in the top level
   /*pragma coverage off*/
   input logic [31:1]                      rst_vec,
   /*pragma coverage on*/
   input logic                             nmi_int,
   // jtag_id and nmi_vec are supposed to be tied to constants in the top level
   /*pragma coverage off*/
   input logic [31:1]                      nmi_vec,
   input logic [31:1]                      jtag_id,
   /*pragma coverage on*/


   output logic [31:0]                     trace_rv_i_insn_ip,
   output logic [31:0]                     trace_rv_i_address_ip,
   output logic                            trace_rv_i_valid_ip,
   output logic                            trace_rv_i_exception_ip,
   output logic [4:0]                      trace_rv_i_ecause_ip,
   output logic                            trace_rv_i_interrupt_ip,
   output logic [31:0]                     trace_rv_i_tval_ip,

   // Bus signals
`ifdef RV_BUILD_AXI4
   //-------------------------- LSU AXI signals--------------------------
   // AXI Write Channels
   output logic                            lsu_axi_awvalid,
   input  logic                            lsu_axi_awready,
   output logic [pt.LSU_BUS_TAG-1:0]       lsu_axi_awid,
   output logic [31:0]                     lsu_axi_awaddr,
   output logic [3:0]                      lsu_axi_awregion,
   /* exclude signals that are tied to constant value in el2_lsu_bus_buffer.sv */
   /*pragma coverage off*/
   output logic [7:0]                      lsu_axi_awlen,
   /*pragma coverage on*/
   output logic [2:0]                      lsu_axi_awsize,
   /* exclude signals that are tied to constant value in el2_lsu_bus_buffer.sv */
   /*pragma coverage off*/
   output logic [1:0]                      lsu_axi_awburst,
   output logic                            lsu_axi_awlock,
   /*pragma coverage on*/
   output logic [3:0]                      lsu_axi_awcache,
   /* exclude signals that are tied to constant value in el2_lsu_bus_buffer.sv */
   /*pragma coverage off*/
   output logic [2:0]                      lsu_axi_awprot,
   output logic [3:0]                      lsu_axi_awqos,
   /*pragma coverage on*/

   output logic                            lsu_axi_wvalid,
   input  logic                            lsu_axi_wready,
   output logic [63:0]                     lsu_axi_wdata,
   output logic [7:0]                      lsu_axi_wstrb,
   output logic                            lsu_axi_wlast,

   input  logic                            lsu_axi_bvalid,
   /* exclude signals that are tied to constant value in el2_lsu_bus_buffer.sv */
   /*pragma coverage off*/
   output logic                            lsu_axi_bready,
   /*pragma coverage on*/
   input  logic [1:0]                      lsu_axi_bresp,
   input  logic [pt.LSU_BUS_TAG-1:0]       lsu_axi_bid,

   // AXI Read Channels
   output logic                            lsu_axi_arvalid,
   input  logic                            lsu_axi_arready,
   output logic [pt.LSU_BUS_TAG-1:0]       lsu_axi_arid,
   output logic [31:0]                     lsu_axi_araddr,
   output logic [3:0]                      lsu_axi_arregion,
   /* exclude signals that are tied to constant value in el2_lsu_bus_buffer.sv */
   /*pragma coverage off*/
   output logic [7:0]                      lsu_axi_arlen,
   /*pragma coverage on*/
   output logic [2:0]                      lsu_axi_arsize,
   /* exclude signals that are tied to constant value in el2_lsu_bus_buffer.sv */
   /*pragma coverage off*/
   output logic [1:0]                      lsu_axi_arburst,
   output logic                            lsu_axi_arlock,
   /*pragma coverage on*/
   output logic [3:0]                      lsu_axi_arcache,
   /* exclude signals that are tied to constant value in el2_lsu_bus_buffer.sv */
   /*pragma coverage off*/
   output logic [2:0]                      lsu_axi_arprot,
   output logic [3:0]                      lsu_axi_arqos,
   /*pragma coverage on*/

   input  logic                            lsu_axi_rvalid,
   /* exclude signals that are tied to constant value in el2_lsu_bus_buffer.sv */
   /*pragma coverage off*/
   output logic                            lsu_axi_rready,
   /*pragma coverage on*/
   input  logic [pt.LSU_BUS_TAG-1:0]       lsu_axi_rid,
   input  logic [63:0]                     lsu_axi_rdata,
   input  logic [1:0]                      lsu_axi_rresp,
   input  logic                            lsu_axi_rlast,

   //-------------------------- IFU AXI signals--------------------------
   // AXI Write Channels
   /* exclude signals that are tied to constant value in el2_ifu_mem_ctl.sv
      IFU does not use AXI write channel */
   /*pragma coverage off*/
   output logic                            ifu_axi_awvalid,
   input  logic                            ifu_axi_awready,
   output logic [pt.IFU_BUS_TAG-1:0]       ifu_axi_awid,
   output logic [31:0]                     ifu_axi_awaddr,
   output logic [3:0]                      ifu_axi_awregion,
   output logic [7:0]                      ifu_axi_awlen,
   output logic [2:0]                      ifu_axi_awsize,
   output logic [1:0]                      ifu_axi_awburst,
   output logic                            ifu_axi_awlock,
   output logic [3:0]                      ifu_axi_awcache,
   output logic [2:0]                      ifu_axi_awprot,
   output logic [3:0]                      ifu_axi_awqos,

   output logic                            ifu_axi_wvalid,
   input  logic                            ifu_axi_wready,
   output logic [63:0]                     ifu_axi_wdata,
   output logic [7:0]                      ifu_axi_wstrb,
   output logic                            ifu_axi_wlast,

   input  logic                            ifu_axi_bvalid,
   output logic                            ifu_axi_bready,
   input  logic [1:0]                      ifu_axi_bresp,
   input  logic [pt.IFU_BUS_TAG-1:0]       ifu_axi_bid,
   /*pragma coverage on*/

   // AXI Read Channels
   output logic                            ifu_axi_arvalid,
   input  logic                            ifu_axi_arready,
   output logic [pt.IFU_BUS_TAG-1:0]       ifu_axi_arid,
   output logic [31:0]                     ifu_axi_araddr,
   output logic [3:0]                      ifu_axi_arregion,
   /* exclude signals that are tied to constant value in el2_ifu_mem_ctl.sv */
   /*pragma coverage off*/
   output logic [7:0]                      ifu_axi_arlen,
   output logic [2:0]                      ifu_axi_arsize,
   output logic [1:0]                      ifu_axi_arburst,
   output logic                            ifu_axi_arlock,
   output logic [3:0]                      ifu_axi_arcache,
   output logic [2:0]                      ifu_axi_arprot,
   output logic [3:0]                      ifu_axi_arqos,
   /*pragma coverage on*/

   input  logic                            ifu_axi_rvalid,
   /* exclude signals that are tied to constant value in el2_ifu_mem_ctl.sv */
   /*pragma coverage off*/
   output logic                            ifu_axi_rready,
   /*pragma coverage on*/
   input  logic [pt.IFU_BUS_TAG-1:0]       ifu_axi_rid,
   input  logic [63:0]                     ifu_axi_rdata,
   input  logic [1:0]                      ifu_axi_rresp,
   input  logic                            ifu_axi_rlast,

   //-------------------------- SB AXI signals--------------------------
   // AXI Write Channels
   output logic                            sb_axi_awvalid,
   input  logic                            sb_axi_awready,
   /* exclude signals that are tied to constant value in dbg/el2_dbg.sv */
   /*pragma coverage off*/
   output logic [pt.SB_BUS_TAG-1:0]        sb_axi_awid,
   /*pragma coverage on*/
   output logic [31:0]                     sb_axi_awaddr,
   output logic [3:0]                      sb_axi_awregion,
   /* exclude signals that are tied to constant value in dbg/el2_dbg.sv */
   /*pragma coverage off*/
   output logic [7:0]                      sb_axi_awlen,
   /*pragma coverage on*/
   output logic [2:0]                      sb_axi_awsize,
   /* exclude signals that are tied to constant value in dbg/el2_dbg.sv */
   /*pragma coverage off*/
   output logic [1:0]                      sb_axi_awburst,
   output logic                            sb_axi_awlock,
   output logic [3:0]                      sb_axi_awcache,
   output logic [2:0]                      sb_axi_awprot,
   output logic [3:0]                      sb_axi_awqos,
   /*pragma coverage on*/

   output logic                            sb_axi_wvalid,
   input  logic                            sb_axi_wready,
   output logic [63:0]                     sb_axi_wdata,
   output logic [7:0]                      sb_axi_wstrb,
   output logic                            sb_axi_wlast,

   input  logic                            sb_axi_bvalid,
   output logic                            sb_axi_bready,
   input  logic [1:0]                      sb_axi_bresp,
   input  logic [pt.SB_BUS_TAG-1:0]        sb_axi_bid,

   // AXI Read Channels
   output logic                            sb_axi_arvalid,
   input  logic                            sb_axi_arready,
   /* exclude signals that are tied to constant value in dbg/el2_dbg.sv */
   /*pragma coverage off*/
   output logic [pt.SB_BUS_TAG-1:0]        sb_axi_arid,
   /*pragma coverage on*/
   output logic [31:0]                     sb_axi_araddr,
   output logic [3:0]                      sb_axi_arregion,
   /* exclude signals that are tied to constant value in dbg/el2_dbg.sv */
   /*pragma coverage off*/
   output logic [7:0]                      sb_axi_arlen,
   /*pragma coverage on*/
   output logic [2:0]                      sb_axi_arsize,
   /* exclude signals that are tied to constant value in dbg/el2_dbg.sv */
   /*pragma coverage off*/
   output logic [1:0]                      sb_axi_arburst,
   output logic                            sb_axi_arlock,
   output logic [3:0]                      sb_axi_arcache,
   output logic [2:0]                      sb_axi_arprot,
   output logic [3:0]                      sb_axi_arqos,
   /*pragma coverage on*/

   input  logic                            sb_axi_rvalid,
   /* exclude signals that are tied to constant value in dbg/el2_dbg.sv */
   /*pragma coverage off*/
   output logic                            sb_axi_rready,
   /*pragma coverage on*/
   input  logic [pt.SB_BUS_TAG-1:0]        sb_axi_rid,
   input  logic [63:0]                     sb_axi_rdata,
   input  logic [1:0]                      sb_axi_rresp,
   input  logic                            sb_axi_rlast,

   //-------------------------- DMA AXI signals--------------------------
   // AXI Write Channels
   input  logic                            dma_axi_awvalid,
   output logic                            dma_axi_awready,
   /* exclude signals that are tied to constant value in tb_top.sv */
   /*pragma coverage off*/
   input  logic [pt.DMA_BUS_TAG-1:0]       dma_axi_awid,
   /*pragma coverage on*/
   input  logic [31:0]                     dma_axi_awaddr,
   input  logic [2:0]                      dma_axi_awsize,
   input  logic [2:0]                      dma_axi_awprot,
   input  logic [7:0]                      dma_axi_awlen,
   input  logic [1:0]                      dma_axi_awburst,


   input  logic                            dma_axi_wvalid,
   output logic                            dma_axi_wready,
   input  logic [63:0]                     dma_axi_wdata,
   input  logic [7:0]                      dma_axi_wstrb,
   input  logic                            dma_axi_wlast,

   output logic                            dma_axi_bvalid,
   input  logic                            dma_axi_bready,
   output logic [1:0]                      dma_axi_bresp,
   output logic [pt.DMA_BUS_TAG-1:0]       dma_axi_bid,

   // AXI Read Channels
   input  logic                            dma_axi_arvalid,
   output logic                            dma_axi_arready,
   /* exclude signals that are tied to constant value in tb_top.sv */
   /*pragma coverage off*/
   input  logic [pt.DMA_BUS_TAG-1:0]       dma_axi_arid,
   /*pragma coverage on*/
   input  logic [31:0]                     dma_axi_araddr,
   input  logic [2:0]                      dma_axi_arsize,
   input  logic [2:0]                      dma_axi_arprot,
   input  logic [7:0]                      dma_axi_arlen,
   input  logic [1:0]                      dma_axi_arburst,

   output logic                            dma_axi_rvalid,
   input  logic                            dma_axi_rready,
   output logic [pt.DMA_BUS_TAG-1:0]       dma_axi_rid,
   output logic [63:0]                     dma_axi_rdata,
   output logic [1:0]                      dma_axi_rresp,
   output logic                            dma_axi_rlast,
`endif

`ifdef RV_BUILD_AHB_LITE
 //// AHB LITE BUS
   output logic [31:0]                     haddr,
   /* exclude signals that are tied to constant value in axi4_to_ahb.sv */
   /*pragma coverage off*/
   output logic [2:0]                      hburst,
   output logic                            hmastlock,
   /*pragma coverage on*/
   output logic [3:0]                      hprot,
   output logic [2:0]                      hsize,
   output logic [1:0]                      htrans,
   output logic                            hwrite,

   /* exclude signals that are tied to constant value in this file */
   /*pragma coverage off*/
   input logic [63:0]                      hrdata,
   input logic                             hready,
   input logic                             hresp,
   /*pragma coverage on*/

   // LSU AHB Master
   output logic [31:0]                     lsu_haddr,
   /* exclude signals that are tied to constant value in axi4_to_ahb.sv */
   /*pragma coverage off*/
   output logic [2:0]                      lsu_hburst,
   output logic                            lsu_hmastlock,
   /*pragma coverage on*/
   output logic [3:0]                      lsu_hprot,
   output logic [2:0]                      lsu_hsize,
   output logic [1:0]                      lsu_htrans,
   output logic                            lsu_hwrite,
   output logic [63:0]                     lsu_hwdata,

   /* exclude signals that are tied to constant value in this file */
   /*pragma coverage off*/
   input logic [63:0]                      lsu_hrdata,
   input logic                             lsu_hready,
   input logic                             lsu_hresp,
   /*pragma coverage on*/
   // Debug System Bus AHB
   output logic [31:0]                     sb_haddr,
   /* exclude signals that are tied to constant value in axi4_to_ahb.sv */
   /*pragma coverage off*/
   output logic [2:0]                      sb_hburst,
   output logic                            sb_hmastlock,
   /*pragma coverage on*/
   output logic [3:0]                      sb_hprot,
   output logic [2:0]                      sb_hsize,
   output logic [1:0]                      sb_htrans,
   output logic                            sb_hwrite,
   output logic [63:0]                     sb_hwdata,

   /* exclude signals that are tied to constant value in this file */
   /*pragma coverage off*/
   input  logic [63:0]                     sb_hrdata,
   input  logic                            sb_hready,
   input  logic                            sb_hresp,
   /*pragma coverage on*/

   // DMA Slave
   /* exclude signals that are tied to constant value in tb_top.sv */
   /*pragma coverage off*/
   input logic                             dma_hsel,
   input logic [31:0]                      dma_haddr,
   input logic [2:0]                       dma_hburst,
   input logic                             dma_hmastlock,
   input logic [3:0]                       dma_hprot,
   input logic [2:0]                       dma_hsize,
   input logic [1:0]                       dma_htrans,
   input logic                             dma_hwrite,
   input logic [63:0]                      dma_hwdata,
   /*pragma coverage on*/
   input logic                             dma_hreadyin,

   output logic [63:0]                     dma_hrdata,
   output logic                            dma_hreadyout,
   output logic                            dma_hresp,
`endif
   // clk ratio signals
   input logic                             lsu_bus_clk_en, // Clock ratio b/w cpu core clk & AHB master interface
   input logic                             ifu_bus_clk_en, // Clock ratio b/w cpu core clk & AHB master interface
   input logic                             dbg_bus_clk_en, // Clock ratio b/w cpu core clk & AHB master interface
   input logic                             dma_bus_clk_en, // Clock ratio b/w cpu core clk & AHB slave interface

   // ICCM/DCCM ECC status
   output logic                            iccm_ecc_single_error,
   output logic                            iccm_ecc_double_error,
   output logic                            dccm_ecc_single_error,
   output logic                            dccm_ecc_double_error,
   output logic                            dccm_write_readback_error,

   // ICache export interface
   el2_mem_if.veer_icache_src              el2_icache_export,

   input logic                             timer_int,
   input logic                             soft_int,
   input logic [pt.PIC_TOTAL_INT:1]        extintsrc_req,

   output logic                            dec_tlu_perfcnt0, // toggles when slot0 perf counter 0 has an event inc
   output logic                            dec_tlu_perfcnt1,
   output logic                            dec_tlu_perfcnt2,
   output logic                            dec_tlu_perfcnt3,

   // ports added by the soc team
   input logic                             jtag_tck,    // JTAG clk
   input logic                             jtag_tms,    // JTAG TMS
   input logic                             jtag_tdi,    // JTAG tdi
   input logic                             jtag_trst_n, // JTAG Reset
   output logic                            jtag_tdo,    // JTAG TDO
   output logic                            jtag_tdoEn,  // JTAG Test Data Output enable

   /*pragma coverage off*/
   input logic [31:4] core_id,
   /*pragma coverage on*/

   // Memory Export Interface
   el2_mem_if.veer_sram_src                el2_mem_export,

`ifdef RV_LOCKSTEP_ENABLE
   // Shadow Core trace
   output logic [31:0] shadow_core_trace_rv_i_insn_ip,
   output logic [31:0] shadow_core_trace_rv_i_address_ip,
   output logic shadow_core_trace_rv_i_valid_ip,
   output logic shadow_core_trace_rv_i_exception_ip,
   output logic [4:0] shadow_core_trace_rv_i_ecause_ip,
   output logic shadow_core_trace_rv_i_interrupt_ip,
   output logic [31:0] shadow_core_trace_rv_i_tval_ip,

   // Shadow Core control
   input el2_mubi_pkg::el2_mubi_t disable_corruption_detection_i,
   input el2_mubi_pkg::el2_mubi_t lockstep_err_injection_en_i,
   output el2_mubi_pkg::el2_mubi_t corruption_detected_o,
`endif

   // external MPC halt/run interface
   input logic                             mpc_debug_halt_req, // Async halt request
   input logic                             mpc_debug_run_req,  // Async run request
   input logic                             mpc_reset_run_req,  // Run/halt after reset
   output logic                            mpc_debug_halt_ack, // Halt ack
   output logic                            mpc_debug_run_ack,  // Run ack
   output logic                            debug_brkpt_status, // debug breakpoint

   input logic                             i_cpu_halt_req,      // Async halt req to CPU
   output logic                            o_cpu_halt_ack,      // core response to halt
   output logic                            o_cpu_halt_status,   // 1'b1 indicates core is halted
   output logic                            o_debug_mode_status, // Core to the PMU that core is in debug mode. When core is in debug mode, the PMU should refrain from sendng a halt or run request
   input logic                             i_cpu_run_req, // Async restart req to CPU
   output logic                            o_cpu_run_ack, // Core response to run req

   // Excluding scan_mode and mbist_mode from coverage as their usage is determined by the integrator of the VeeR core.
   /* pragma coverage off */
   input logic                             scan_mode,     // To enable scan mode
   input logic                             mbist_mode,    // to enable mbist

   // DMI port for uncore
   input logic                             dmi_core_enable,
   input logic                             dmi_uncore_enable,
   output logic                            dmi_uncore_en,
   output logic                            dmi_uncore_wr_en,
   output logic                     [ 6:0] dmi_uncore_addr,
   output logic                     [31:0] dmi_uncore_wdata,
   input logic                      [31:0] dmi_uncore_rdata,
   output logic                            dmi_active
   /* pragma coverage on */
);

  el2_veer_wrapper rvtop_synth (
    .clk(clk),
    .rst_l(rst_l),
    .dbg_rst_l(dbg_rst_l),
    .rst_vec(rst_vec),
    .nmi_int(nmi_int),
    .nmi_vec(nmi_vec),
    .jtag_id(jtag_id),
    .trace_rv_i_insn_ip(trace_rv_i_insn_ip),
    .trace_rv_i_address_ip(trace_rv_i_address_ip),
    .trace_rv_i_valid_ip(trace_rv_i_valid_ip),
    .trace_rv_i_exception_ip(trace_rv_i_exception_ip),
    .trace_rv_i_ecause_ip(trace_rv_i_ecause_ip),
    .trace_rv_i_interrupt_ip(trace_rv_i_interrupt_ip),
    .trace_rv_i_tval_ip(trace_rv_i_tval_ip),
`ifdef RV_BUILD_AXI4
    .lsu_axi_awvalid(lsu_axi_awvalid),
    .lsu_axi_awready(lsu_axi_awready),
    .lsu_axi_awid(lsu_axi_awid),
    .lsu_axi_awaddr(lsu_axi_awaddr),
    .lsu_axi_awregion(lsu_axi_awregion),
    .lsu_axi_awlen(lsu_axi_awlen),
    .lsu_axi_awsize(lsu_axi_awsize),
    .lsu_axi_awburst(lsu_axi_awburst),
    .lsu_axi_awlock(lsu_axi_awlock),
    .lsu_axi_awcache(lsu_axi_awcache),
    .lsu_axi_awprot(lsu_axi_awprot),
    .lsu_axi_awqos(lsu_axi_awqos),
    .lsu_axi_wvalid(lsu_axi_wvalid),
    .lsu_axi_wready(lsu_axi_wready),
    .lsu_axi_wdata(lsu_axi_wdata),
    .lsu_axi_wstrb(lsu_axi_wstrb),
    .lsu_axi_wlast(lsu_axi_wlast),
    .lsu_axi_bvalid(lsu_axi_bvalid),
    .lsu_axi_bready(lsu_axi_bready),
    .lsu_axi_bresp(lsu_axi_bresp),
    .lsu_axi_bid(lsu_axi_bid),
    .lsu_axi_arvalid(lsu_axi_arvalid),
    .lsu_axi_arready(lsu_axi_arready),
    .lsu_axi_arid(lsu_axi_arid),
    .lsu_axi_araddr(lsu_axi_araddr),
    .lsu_axi_arregion(lsu_axi_arregion),
    .lsu_axi_arlen(lsu_axi_arlen),
    .lsu_axi_arsize(lsu_axi_arsize),
    .lsu_axi_arburst(lsu_axi_arburst),
    .lsu_axi_arlock(lsu_axi_arlock),
    .lsu_axi_arcache(lsu_axi_arcache),
    .lsu_axi_arprot(lsu_axi_arprot),
    .lsu_axi_arqos(lsu_axi_arqos),
    .lsu_axi_rvalid(lsu_axi_rvalid),
    .lsu_axi_rready(lsu_axi_rready),
    .lsu_axi_rid(lsu_axi_rid),
    .lsu_axi_rdata(lsu_axi_rdata),
    .lsu_axi_rresp(lsu_axi_rresp),
    .lsu_axi_rlast(lsu_axi_rlast),
    .ifu_axi_awvalid(ifu_axi_awvalid),
    .ifu_axi_awready(ifu_axi_awready),
    .ifu_axi_awid(ifu_axi_awid),
    .ifu_axi_awaddr(ifu_axi_awaddr),
    .ifu_axi_awregion(ifu_axi_awregion),
    .ifu_axi_awlen(ifu_axi_awlen),
    .ifu_axi_awsize(ifu_axi_awsize),
    .ifu_axi_awburst(ifu_axi_awburst),
    .ifu_axi_awlock(ifu_axi_awlock),
    .ifu_axi_awcache(ifu_axi_awcache),
    .ifu_axi_awprot(ifu_axi_awprot),
    .ifu_axi_awqos(ifu_axi_awqos),
    .ifu_axi_wvalid(ifu_axi_wvalid),
    .ifu_axi_wready(ifu_axi_wready),
    .ifu_axi_wdata(ifu_axi_wdata),
    .ifu_axi_wstrb(ifu_axi_wstrb),
    .ifu_axi_wlast(ifu_axi_wlast),
    .ifu_axi_bvalid(ifu_axi_bvalid),
    .ifu_axi_bready(ifu_axi_bready),
    .ifu_axi_bresp(ifu_axi_bresp),
    .ifu_axi_bid(ifu_axi_bid),
    .ifu_axi_arvalid(ifu_axi_arvalid),
    .ifu_axi_arready(ifu_axi_arready),
    .ifu_axi_arid(ifu_axi_arid),
    .ifu_axi_araddr(ifu_axi_araddr),
    .ifu_axi_arregion(ifu_axi_arregion),
    .ifu_axi_arlen(ifu_axi_arlen),
    .ifu_axi_arsize(ifu_axi_arsize),
    .ifu_axi_arburst(ifu_axi_arburst),
    .ifu_axi_arlock(ifu_axi_arlock),
    .ifu_axi_arcache(ifu_axi_arcache),
    .ifu_axi_arprot(ifu_axi_arprot),
    .ifu_axi_arqos(ifu_axi_arqos),
    .ifu_axi_rvalid(ifu_axi_rvalid),
    .ifu_axi_rready(ifu_axi_rready),
    .ifu_axi_rid(ifu_axi_rid),
    .ifu_axi_rdata(ifu_axi_rdata),
    .ifu_axi_rresp(ifu_axi_rresp),
    .ifu_axi_rlast(ifu_axi_rlast),
    .sb_axi_awvalid(sb_axi_awvalid),
    .sb_axi_awready(sb_axi_awready),
    .sb_axi_awid(sb_axi_awid),
    .sb_axi_awaddr(sb_axi_awaddr),
    .sb_axi_awregion(sb_axi_awregion),
    .sb_axi_awlen(sb_axi_awlen),
    .sb_axi_awsize(sb_axi_awsize),
    .sb_axi_awburst(sb_axi_awburst),
    .sb_axi_awlock(sb_axi_awlock),
    .sb_axi_awcache(sb_axi_awcache),
    .sb_axi_awprot(sb_axi_awprot),
    .sb_axi_awqos(sb_axi_awqos),
    .sb_axi_wvalid(sb_axi_wvalid),
    .sb_axi_wready(sb_axi_wready),
    .sb_axi_wdata(sb_axi_wdata),
    .sb_axi_wstrb(sb_axi_wstrb),
    .sb_axi_wlast(sb_axi_wlast),
    .sb_axi_bvalid(sb_axi_bvalid),
    .sb_axi_bready(sb_axi_bready),
    .sb_axi_bresp(sb_axi_bresp),
    .sb_axi_bid(sb_axi_bid),
    .sb_axi_arvalid(sb_axi_arvalid),
    .sb_axi_arready(sb_axi_arready),
    .sb_axi_arid(sb_axi_arid),
    .sb_axi_araddr(sb_axi_araddr),
    .sb_axi_arregion(sb_axi_arregion),
    .sb_axi_arlen(sb_axi_arlen),
    .sb_axi_arsize(sb_axi_arsize),
    .sb_axi_arburst(sb_axi_arburst),
    .sb_axi_arlock(sb_axi_arlock),
    .sb_axi_arcache(sb_axi_arcache),
    .sb_axi_arprot(sb_axi_arprot),
    .sb_axi_arqos(sb_axi_arqos),
    .sb_axi_rvalid(sb_axi_rvalid),
    .sb_axi_rready(sb_axi_rready),
    .sb_axi_rid(sb_axi_rid),
    .sb_axi_rdata(sb_axi_rdata),
    .sb_axi_rresp(sb_axi_rresp),
    .sb_axi_rlast(sb_axi_rlast),
    .dma_axi_awvalid(dma_axi_awvalid),
    .dma_axi_awready(dma_axi_awready),
    .dma_axi_awid(dma_axi_awid),
    .dma_axi_awaddr(dma_axi_awaddr),
    .dma_axi_awsize(dma_axi_awsize),
    .dma_axi_awprot(dma_axi_awprot),
    .dma_axi_awlen(dma_axi_awlen),
    .dma_axi_awburst(dma_axi_awburst),
    .dma_axi_wvalid(dma_axi_wvalid),
    .dma_axi_wready(dma_axi_wready),
    .dma_axi_wdata(dma_axi_wdata),
    .dma_axi_wstrb(dma_axi_wstrb),
    .dma_axi_wlast(dma_axi_wlast),
    .dma_axi_bvalid(dma_axi_bvalid),
    .dma_axi_bready(dma_axi_bready),
    .dma_axi_bresp(dma_axi_bresp),
    .dma_axi_bid(dma_axi_bid),
    .dma_axi_arvalid(dma_axi_arvalid),
    .dma_axi_arready(dma_axi_arready),
    .dma_axi_arid(dma_axi_arid),
    .dma_axi_araddr(dma_axi_araddr),
    .dma_axi_arsize(dma_axi_arsize),
    .dma_axi_arprot(dma_axi_arprot),
    .dma_axi_arlen(dma_axi_arlen),
    .dma_axi_arburst(dma_axi_arburst),
    .dma_axi_rvalid(dma_axi_rvalid),
    .dma_axi_rready(dma_axi_rready),
    .dma_axi_rid(dma_axi_rid),
    .dma_axi_rdata(dma_axi_rdata),
    .dma_axi_rresp(dma_axi_rresp),
    .dma_axi_rlast(dma_axi_rlast),
`endif
`ifdef RV_BUILD_AHB_LITE
   .haddr(haddr),
   .hburst(hburst),
   .hmastlock(hmastlock),
   .hprot(hprot),
   .hsize(hsize),
   .htrans(htrans),
   .hwrite(hwrite),
   .hrdata(hrdata),
   .hready(hready),
   .hresp(hresp),
   .lsu_haddr(lsu_haddr),
   .lsu_hburst(lsu_hburst),
   .lsu_hmastlock(lsu_hmastlock),
   .lsu_hprot(lsu_hprot),
   .lsu_hsize(lsu_hsize),
   .lsu_htrans(lsu_htrans),
   .lsu_hwrite(lsu_hwrite),
   .lsu_hwdata(lsu_hwdata),
   .lsu_hrdata(lsu_hrdata),
   .lsu_hready(lsu_hready),
   .lsu_hresp(lsu_hresp),
   .sb_haddr(sb_haddr),
   .sb_hburst(sb_hburst),
   .sb_hmastlock(sb_hmastlock),
   .sb_hprot(sb_hprot),
   .sb_hsize(sb_hsize),
   .sb_htrans(sb_htrans),
   .sb_hwrite(sb_hwrite),
   .sb_hwdata(sb_hwdata),
   .sb_hrdata(sb_hrdata),
   .sb_hready(sb_hready),
   .sb_hresp(sb_hresp),
   .dma_hsel(dma_hsel),
   .dma_haddr(dma_haddr),
   .dma_hburst(dma_hburst),
   .dma_hmastlock(dma_hmastlock),
   .dma_hprot(dma_hprot),
   .dma_hsize(dma_hsize),
   .dma_htrans(dma_htrans),
   .dma_hwrite(dma_hwrite),
   .dma_hwdata(dma_hwdata),
   .dma_hreadyin(dma_hreadyin),
   .dma_hrdata(dma_hrdata),
   .dma_hreadyout(dma_hreadyout),
   .dma_hresp(dma_hresp),
`endif
    .lsu_bus_clk_en(lsu_bus_clk_en),
    .ifu_bus_clk_en(ifu_bus_clk_en),
    .dbg_bus_clk_en(dbg_bus_clk_en),
    .dma_bus_clk_en(dma_bus_clk_en),
    .iccm_ecc_single_error(iccm_ecc_single_error),
    .iccm_ecc_double_error(iccm_ecc_double_error),
    .dccm_ecc_single_error(dccm_ecc_single_error),
    .dccm_ecc_double_error(dccm_ecc_double_error),
    .dccm_write_readback_error(dccm_write_readback_error),
    .timer_int(timer_int),
    .soft_int(soft_int),
    .extintsrc_req(extintsrc_req),
    .dec_tlu_perfcnt0(dec_tlu_perfcnt0),
    .dec_tlu_perfcnt1(dec_tlu_perfcnt1),
    .dec_tlu_perfcnt2(dec_tlu_perfcnt2),
    .dec_tlu_perfcnt3(dec_tlu_perfcnt3),
    .jtag_tck(jtag_tck),
    .jtag_tms(jtag_tms),
    .jtag_tdi(jtag_tdi),
    .jtag_trst_n(jtag_trst_n),
    .jtag_tdo(jtag_tdo),
    .jtag_tdoEn(jtag_tdoEn),
    .core_id(core_id),
    .mpc_debug_halt_req(mpc_debug_halt_req),
    .mpc_debug_run_req(mpc_debug_run_req),
    .mpc_reset_run_req(mpc_reset_run_req),
    .mpc_debug_halt_ack(mpc_debug_halt_ack),
    .mpc_debug_run_ack(mpc_debug_run_ack),
    .debug_brkpt_status(debug_brkpt_status),
    .i_cpu_halt_req(i_cpu_halt_req),
    .o_cpu_halt_ack(o_cpu_halt_ack),
    .o_cpu_halt_status(o_cpu_halt_status),
    .o_debug_mode_status(o_debug_mode_status),
    .i_cpu_run_req(i_cpu_run_req),
    .o_cpu_run_ack(o_cpu_run_ack),
    .scan_mode(scan_mode),
    .mbist_mode(mbist_mode),
    .dmi_core_enable(dmi_core_enable),
    .dmi_uncore_enable(dmi_uncore_enable),
    .dmi_uncore_en(dmi_uncore_en),
    .dmi_uncore_wr_en(dmi_uncore_wr_en),
    .dmi_uncore_addr(dmi_uncore_addr),
    .dmi_uncore_wdata(dmi_uncore_wdata),
    .dmi_uncore_rdata(dmi_uncore_rdata),
    .dmi_active(dmi_active),

    .\el2_icache_export.ic_b_sb_wren                (el2_icache_export.ic_b_sb_wren),
    .\el2_icache_export.ic_b_sb_bit_en_vec          (el2_icache_export.ic_b_sb_bit_en_vec),
    .\el2_icache_export.ic_sb_wr_data               (el2_icache_export.ic_sb_wr_data),
    .\el2_icache_export.ic_rw_addr_bank_q           (el2_icache_export.ic_rw_addr_bank_q),
    .\el2_icache_export.ic_bank_way_clken_final     (el2_icache_export.ic_bank_way_clken_final),
    .\el2_icache_export.ic_bank_way_clken_final_up  (el2_icache_export.ic_bank_way_clken_final_up),
    .\el2_icache_export.wb_packeddout_pre           (el2_icache_export.wb_packeddout_pre),
    .\el2_icache_export.wb_dout_pre_up              (el2_icache_export.wb_dout_pre_up),
    .\el2_icache_export.ic_tag_clken_final          (el2_icache_export.ic_tag_clken_final),
    .\el2_icache_export.ic_tag_wren_q               (el2_icache_export.ic_tag_wren_q),
    .\el2_icache_export.ic_tag_wren_biten_vec       (el2_icache_export.ic_tag_wren_biten_vec),
    .\el2_icache_export.ic_tag_wr_data              (el2_icache_export.ic_tag_wr_data),
    .\el2_icache_export.ic_rw_addr_q                (el2_icache_export.ic_rw_addr_q),
    .\el2_icache_export.ic_tag_data_raw_packed_pre  (el2_icache_export.ic_tag_data_raw_packed_pre),
    .\el2_icache_export.ic_tag_data_raw_pre         (el2_icache_export.ic_tag_data_raw_pre),

    .\el2_mem_export.clk                (el2_mem_export.clk),
    .\el2_mem_export.iccm_clken         (el2_mem_export.iccm_clken),
    .\el2_mem_export.iccm_wren_bank     (el2_mem_export.iccm_wren_bank),
    .\el2_mem_export.iccm_addr_bank     (el2_mem_export.iccm_addr_bank),
    .\el2_mem_export.iccm_bank_wr_data  (el2_mem_export.iccm_bank_wr_data),
    .\el2_mem_export.iccm_bank_wr_ecc   (el2_mem_export.iccm_bank_wr_ecc),
    .\el2_mem_export.iccm_bank_dout     (el2_mem_export.iccm_bank_dout),
    .\el2_mem_export.iccm_bank_ecc      (el2_mem_export.iccm_bank_ecc),
    .\el2_mem_export.dccm_clken         (el2_mem_export.dccm_clken),
    .\el2_mem_export.dccm_wren_bank     (el2_mem_export.dccm_wren_bank),
    .\el2_mem_export.dccm_addr_bank     (el2_mem_export.dccm_addr_bank),
    .\el2_mem_export.dccm_wr_data_bank  (el2_mem_export.dccm_wr_data_bank),
    .\el2_mem_export.dccm_wr_ecc_bank   (el2_mem_export.dccm_wr_ecc_bank),
    .\el2_mem_export.dccm_bank_dout     (el2_mem_export.dccm_bank_dout),
    .\el2_mem_export.dccm_bank_ecc      (el2_mem_export.dccm_bank_ecc)
  );
endmodule
