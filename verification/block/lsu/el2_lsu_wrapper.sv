// Copyright (c) 2025 Antmicro
// SPDX-License-Identifier: Apache-2.0
module el2_lsu_wrapper
  import el2_pkg::*;
#(
    `include "el2_param.vh"
) (
    input logic                             clk_override,             // Override non-functional clock gating
    input logic                             dec_tlu_flush_lower_r,    // I0/I1 writeback flush. This is used to flush the old packets only
    input logic                             dec_tlu_i0_kill_writeb_r, // I0 is flushed, don't writeback any results to arch state
    input logic                             dec_tlu_force_halt,       // This will be high till TLU goes to debug halt

    // chicken signals
    input logic                             dec_tlu_external_ldfwd_disable,     // disable load to load forwarding for externals
    input logic                             dec_tlu_wb_coalescing_disable,     // disable the write buffer coalesce
    input logic                             dec_tlu_sideeffect_posted_disable, // disable the posted sideeffect load store to the bus
    input logic                             dec_tlu_core_ecc_disable,          // disable the generation of the ecc

    input logic [31:0]                      exu_lsu_rs1_d,        // address rs operand
    input logic [31:0]                      exu_lsu_rs2_d,        // store data
    input logic [11:0]                      dec_lsu_offset_d,     // address offset operand

    input                                   el2_lsu_pkt_t lsu_p,  // lsu control packet
    input logic                             dec_lsu_valid_raw_d,   // Raw valid for address computation
    input logic [31:0]                      dec_tlu_mrac_ff,       // CSR for memory region control

    output logic [31:0]                     lsu_result_m,          // lsu load data
    output logic [31:0]                     lsu_result_corr_r,     // This is the ECC corrected data going to RF
    output logic                            lsu_load_stall_any,    // This is for blocking loads in the decode
    output logic                            lsu_store_stall_any,   // This is for blocking stores in the decode
    output logic                            lsu_fastint_stall_any, // Stall the fastint in decode-1 stage
    output logic                            lsu_idle_any,          // lsu buffers are empty and no instruction in the pipeline. Doesn't include DMA
    output logic                            lsu_active,            // Used to turn off top level clk

    output logic [31:1]                     lsu_fir_addr,        // fast interrupt address
    output logic [1:0]                      lsu_fir_error,       // Error during fast interrupt lookup

    output logic                            lsu_single_ecc_error_incr,     // Increment the ecc counter
    output el2_lsu_error_pkt_t             lsu_error_pkt_r,               // lsu exception packet
    output logic                            lsu_imprecise_error_load_any,  // bus load imprecise error
    output logic                            lsu_imprecise_error_store_any, // bus store imprecise error
    output logic [31:0]                     lsu_imprecise_error_addr_any,  // bus store imprecise error address

    // Non-blocking loads
    output logic                               lsu_nonblock_load_valid_m,      // there is an external load -> put in the cam
    output logic [pt.LSU_NUM_NBLOAD_WIDTH-1:0] lsu_nonblock_load_tag_m,        // the tag of the external non block load
    output logic                               lsu_nonblock_load_inv_r,        // invalidate signal for the cam entry for non block loads
    output logic [pt.LSU_NUM_NBLOAD_WIDTH-1:0] lsu_nonblock_load_inv_tag_r,    // tag of the enrty which needs to be invalidated
    output logic                               lsu_nonblock_load_data_valid,   // the non block is valid - sending information back to the cam
    output logic                               lsu_nonblock_load_data_error,   // non block load has an error
    output logic [pt.LSU_NUM_NBLOAD_WIDTH-1:0] lsu_nonblock_load_data_tag,     // the tag of the non block load sending the data/error
    output logic [31:0]                        lsu_nonblock_load_data,         // Data of the non block load

    output logic                            lsu_pmu_load_external_m,        // PMU : Bus loads
    output logic                            lsu_pmu_store_external_m,       // PMU : Bus loads
    output logic                            lsu_pmu_misaligned_m,           // PMU : misaligned
    output logic                            lsu_pmu_bus_trxn,               // PMU : bus transaction
    output logic                            lsu_pmu_bus_misaligned,         // PMU : misaligned access going to the bus
    output logic                            lsu_pmu_bus_error,              // PMU : bus sending error back
    output logic                            lsu_pmu_bus_busy,               // PMU : bus is not ready

    // Trigger signals
    // input                                   el2_trigger_pkt_t [3:0] trigger_pkt_any, // Trigger info from the decode
    output logic [3:0]                      lsu_trigger_match_m,                      // lsu trigger hit (one bit per trigger)

    // DCCM ports
    output logic                            dccm_wren,       // DCCM write enable
    output logic                            dccm_rden,       // DCCM read enable
    output logic [pt.DCCM_BITS-1:0]         dccm_wr_addr_lo, // DCCM write address low bank
    output logic [pt.DCCM_BITS-1:0]         dccm_wr_addr_hi, // DCCM write address hi bank
    output logic [pt.DCCM_BITS-1:0]         dccm_rd_addr_lo, // DCCM read address low bank
    output logic [pt.DCCM_BITS-1:0]         dccm_rd_addr_hi, // DCCM read address hi bank (hi and low same if aligned read)
    output logic [pt.DCCM_FDATA_WIDTH-1:0]  dccm_wr_data_lo, // DCCM write data for lo bank
    output logic [pt.DCCM_FDATA_WIDTH-1:0]  dccm_wr_data_hi, // DCCM write data for hi bank

    input logic [pt.DCCM_FDATA_WIDTH-1:0]   dccm_rd_data_lo, // DCCM read data low bank
    input logic [pt.DCCM_FDATA_WIDTH-1:0]   dccm_rd_data_hi, // DCCM read data hi bank

    // PIC ports
    output logic                            picm_wren,    // PIC memory write enable
    output logic                            picm_rden,    // PIC memory read enable
    output logic                            picm_mken,    // Need to read the mask for stores to determine which bits to write/forward
    output logic [31:0]                     picm_rdaddr,  // address for pic read access
    output logic [31:0]                     picm_wraddr,  // address for pic write access
    output logic [31:0]                     picm_wr_data, // PIC memory write data
    input logic [31:0]                      picm_rd_data, // PIC memory read/mask data

    // AXI Write Channels
    output logic                            lsu_axi_awvalid,
    input  logic                            lsu_axi_awready,
    output logic [pt.LSU_BUS_TAG-1:0]       lsu_axi_awid,
    output logic [31:0]                     lsu_axi_awaddr,
    output logic [3:0]                      lsu_axi_awregion,
    output logic [7:0]                      lsu_axi_awlen,
    output logic [2:0]                      lsu_axi_awsize,
    output logic [1:0]                      lsu_axi_awburst,
    output logic                            lsu_axi_awlock,
    output logic [3:0]                      lsu_axi_awcache,
    output logic [2:0]                      lsu_axi_awprot,
    output logic [3:0]                      lsu_axi_awqos,

    output logic                            lsu_axi_wvalid,
    input  logic                            lsu_axi_wready,
    output logic [63:0]                     lsu_axi_wdata,
    output logic [7:0]                      lsu_axi_wstrb,
    output logic                            lsu_axi_wlast,

    input  logic                            lsu_axi_bvalid,
    output logic                            lsu_axi_bready,
    input  logic [1:0]                      lsu_axi_bresp,
    input  logic [pt.LSU_BUS_TAG-1:0]       lsu_axi_bid,

    // AXI Read Channels
    output logic                            lsu_axi_arvalid,
    input  logic                            lsu_axi_arready,
    output logic [pt.LSU_BUS_TAG-1:0]       lsu_axi_arid,
    output logic [31:0]                     lsu_axi_araddr,
    output logic [3:0]                      lsu_axi_arregion,
    output logic [7:0]                      lsu_axi_arlen,
    output logic [2:0]                      lsu_axi_arsize,
    output logic [1:0]                      lsu_axi_arburst,
    output logic                            lsu_axi_arlock,
    output logic [3:0]                      lsu_axi_arcache,
    output logic [2:0]                      lsu_axi_arprot,
    output logic [3:0]                      lsu_axi_arqos,

    input  logic                            lsu_axi_rvalid,
    output logic                            lsu_axi_rready,
    input  logic [pt.LSU_BUS_TAG-1:0]       lsu_axi_rid,
    input  logic [63:0]                     lsu_axi_rdata,
    input  logic [1:0]                      lsu_axi_rresp,
    input  logic                            lsu_axi_rlast,

    input logic                             lsu_bus_clk_en,    // external drives a clock_en to control bus ratio

    // DMA slave
    input logic                             dma_dccm_req,       // DMA read/write to dccm
    input logic [2:0]                       dma_mem_tag,        // DMA request tag
    input logic [31:0]                      dma_mem_addr,       // DMA address
    input logic [2:0]                       dma_mem_sz,         // DMA access size
    input logic                             dma_mem_write,      // DMA access is a write
    input logic [63:0]                      dma_mem_wdata,      // DMA write data

    output logic                            dccm_dma_rvalid,     // lsu data valid for DMA dccm read
    output logic                            dccm_dma_ecc_error,  // DMA load had ecc error
    output logic [2:0]                      dccm_dma_rtag,       // DMA request tag
    output logic [63:0]                     dccm_dma_rdata,      // lsu data for DMA dccm read
    output logic                            dccm_ready,          // lsu ready for DMA access

    // DCCM ECC status
    output logic                            lsu_dccm_rd_ecc_single_err,
    output logic                            lsu_dccm_rd_ecc_double_err,

    input logic                             scan_mode,           // scan mode
    input logic                             clk,                 // Clock only while core active.  Through one clock header.  For flops with    second clock header built in.  Connected to ACTIVE_L2CLK.
    input logic                             active_clk,          // Clock only while core active.  Through two clock headers. For flops without second clock header built in.
    input logic                             rst_l,               // reset, active low

    output logic [31:0] lsu_pmp_addr_start,
    output logic [31:0] lsu_pmp_addr_end,
    input  logic        lsu_pmp_error_start,
    input  logic        lsu_pmp_error_end,
    output logic        lsu_pmp_we,
    output logic        lsu_pmp_re,

    // Unpacked [3:0] trigger_pkt_t
    input logic [3:0] select,
    input logic [3:0] match,
    input logic [3:0] store,
    input logic [3:0] load,
    input logic [3:0] execute,
    input logic [3:0] m,

    input logic [31:0] tdata[4],

    input logic [31:0] lsu_addr_m,         // address
    input logic [31:0] store_data_m        // store data
);

  // Pack triggers
  el2_trigger_pkt_t [3:0] trigger_pkt_any;
  for (genvar i = 0; i < 4; i++) begin : g_trigger_assigns
    assign trigger_pkt_any[i].select  = select[i];
    assign trigger_pkt_any[i].match   = match[i];
    assign trigger_pkt_any[i].store   = store[i];
    assign trigger_pkt_any[i].load    = load[i];
    assign trigger_pkt_any[i].execute = execute[i];
    assign trigger_pkt_any[i].m       = m[i];
    assign trigger_pkt_any[i].tdata2  = tdata[i];
  end

  // The trigger unit
  el2_lsu lsu_inst (
      .*
  );

endmodule
