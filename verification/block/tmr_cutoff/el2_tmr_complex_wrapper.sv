// Copyright 2026 Antmicro <www.antmicro.com>
// //
// // SPDX-License-Identifier: Apache-2.0
//

module el2_tmr_complex_wrapper
  import el2_pkg::*;
  import el2_mubi_pkg::*;
#(
    `include "el2_param.svh"
) (
    input logic                  clk,
    input logic                  rst_l,
    input logic                  dbg_rst_l,
    // rst_vec is supposed to be connected to a constant in the top level
    /*pragma coverage off*/
    input logic [31:1]           rst_vec,
    /*pragma coverage on*/
    input logic                  nmi_int,
    // nmi_vec is supposed to be connected to a constant in the top level
    /*pragma coverage off*/
    input logic [31:1]           nmi_vec,
    /*pragma coverage on*/
    output logic                 core_rst_l,   // This is "rst_l | dbg_rst_l"

    output logic                 active_l2clk,
    output logic                 free_l2clk,

    output logic [31:0] trace_rv_i_insn_ip,
    output logic [31:0] trace_rv_i_address_ip,
    output logic        trace_rv_i_valid_ip,
    output logic        trace_rv_i_exception_ip,
    output logic [4:0]  trace_rv_i_ecause_ip,
    output logic        trace_rv_i_interrupt_ip,
    output logic [31:0] trace_rv_i_tval_ip,

    // external halt/run interface
    input logic  i_cpu_halt_req,    // Asynchronous Halt request to CPU
    input logic  i_cpu_run_req,     // Asynchronous Restart request to CPU
    output logic o_cpu_halt_ack,    // Core Acknowledge to Halt request
    output logic o_cpu_halt_status, // 1'b1 indicates processor is halted
    output logic o_cpu_run_ack,     // Core Acknowledge to run request
    output logic o_debug_mode_status, // Core to the PMU that core is in debug mode. When core is in debug mode, the PMU should refrain from sendng a halt or run request

    /*pragma coverage off*/
    input logic [31:4] core_id, // CORE ID
    /*pragma coverage on*/

    // ICCM/DCCM Memory Export Interface (flat)
    output logic                                                               mem_export_clk,

    output logic [pt.ICCM_NUM_BANKS-1:0]                                       mem_export_iccm_clken,
    output logic [pt.ICCM_NUM_BANKS-1:0]                                       mem_export_iccm_wren_bank,
    output logic [pt.ICCM_NUM_BANKS-1:0][pt.ICCM_BITS-1:pt.ICCM_BANK_INDEX_LO] mem_export_iccm_addr_bank,
    output logic [pt.ICCM_NUM_BANKS-1:0][                                31:0] mem_export_iccm_bank_wr_data,
    output logic [pt.ICCM_NUM_BANKS-1:0][               pt.ICCM_ECC_WIDTH-1:0] mem_export_iccm_bank_wr_ecc,
    input  logic [pt.ICCM_NUM_BANKS-1:0][                                31:0] mem_export_iccm_bank_dout,
    input  logic [pt.ICCM_NUM_BANKS-1:0][               pt.ICCM_ECC_WIDTH-1:0] mem_export_iccm_bank_ecc,

    output logic [pt.DCCM_NUM_BANKS-1:0]                                       mem_export_dccm_clken,
    output logic [pt.DCCM_NUM_BANKS-1:0]                                       mem_export_dccm_wren_bank,
    output logic [pt.DCCM_NUM_BANKS-1:0][pt.DCCM_BITS-1:(pt.DCCM_BANK_BITS+2)] mem_export_dccm_addr_bank,
    output logic [pt.DCCM_NUM_BANKS-1:0][              pt.DCCM_DATA_WIDTH-1:0] mem_export_dccm_wr_data_bank,
    output logic [pt.DCCM_NUM_BANKS-1:0][               pt.DCCM_ECC_WIDTH-1:0] mem_export_dccm_wr_ecc_bank,
    input  logic [pt.DCCM_NUM_BANKS-1:0][              pt.DCCM_DATA_WIDTH-1:0] mem_export_dccm_bank_dout,
    input  logic [pt.DCCM_NUM_BANKS-1:0][               pt.DCCM_ECC_WIDTH-1:0] mem_export_dccm_bank_ecc,

    // I-Cache memory export interface (flat)
    output logic                                                                         icache_export_clk,

    output logic [pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_NUM_WAYS-1:0]                       icache_export_ic_b_sb_wren,
    output logic [pt.ICACHE_BANKS_WAY-1:0][(71*pt.ICACHE_NUM_WAYS)-1:0]                  icache_export_ic_b_sb_bit_en_vec,
    input  logic [pt.ICACHE_BANKS_WAY-1:0][(71*pt.ICACHE_NUM_WAYS)-1:0]                  icache_export_wb_packeddout_pre,
    output logic [pt.ICACHE_BANKS_WAY-1:0][70:0]                                         icache_export_ic_sb_wr_data,
    output logic [pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_INDEX_HI : pt.ICACHE_DATA_INDEX_LO] icache_export_ic_rw_addr_bank_q,
    output logic [pt.ICACHE_BANKS_WAY-1:0]                                               icache_export_ic_bank_way_clken_final,
    output logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0]                       icache_export_ic_bank_way_clken_final_up,
    input  logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0][71-1:0]               icache_export_wb_dout_pre_up,

    output logic [pt.ICACHE_NUM_WAYS-1:0]                     icache_export_ic_tag_clken_final,
    output logic [pt.ICACHE_NUM_WAYS-1:0]                     icache_export_ic_tag_wren_q,
    output logic [(26*pt.ICACHE_NUM_WAYS)-1 :0]               icache_export_ic_tag_wren_biten_vec,
    input  logic [(26*pt.ICACHE_NUM_WAYS)-1 :0]               icache_export_ic_tag_data_raw_packed_pre,
    output logic [25:0]                                       icache_export_ic_tag_wr_data,
    output logic [pt.ICACHE_INDEX_HI: pt.ICACHE_TAG_INDEX_LO] icache_export_ic_rw_addr_q,
    input  logic [pt.ICACHE_NUM_WAYS-1:0] [25:0]              icache_export_ic_tag_data_raw_pre,

    // external MPC halt/run interface
    input logic mpc_debug_halt_req, // Async halt request
    input logic mpc_debug_run_req, // Async run request
    input logic mpc_reset_run_req, // Run/halt after reset
    output logic mpc_debug_halt_ack, // Halt ack
    output logic mpc_debug_run_ack, // Run ack
    output logic debug_brkpt_status, // debug breakpoint

    output logic dec_tlu_perfcnt0, // toggles when slot0 perf counter 0 has an event inc
    output logic dec_tlu_perfcnt1,
    output logic dec_tlu_perfcnt2,
    output logic dec_tlu_perfcnt3,

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
    input  logic                         dma_axi_awvalid,
    output logic                         dma_axi_awready,
    input  logic [pt.DMA_BUS_TAG-1:0]    dma_axi_awid,
    input  logic [31:0]                  dma_axi_awaddr,
    input  logic [2:0]                   dma_axi_awsize,
    input  logic [2:0]                   dma_axi_awprot,
    input  logic [7:0]                   dma_axi_awlen,
    input  logic [1:0]                   dma_axi_awburst,


    input  logic                         dma_axi_wvalid,
    output logic                         dma_axi_wready,
    input  logic [63:0]                  dma_axi_wdata,
    input  logic [7:0]                   dma_axi_wstrb,
    input  logic                         dma_axi_wlast,

    output logic                         dma_axi_bvalid,
    input  logic                         dma_axi_bready,
    output logic [1:0]                   dma_axi_bresp,
    output logic [pt.DMA_BUS_TAG-1:0]    dma_axi_bid,

    // AXI Read Channels
    input  logic                         dma_axi_arvalid,
    output logic                         dma_axi_arready,
    input  logic [pt.DMA_BUS_TAG-1:0]    dma_axi_arid,
    input  logic [31:0]                  dma_axi_araddr,
    input  logic [2:0]                   dma_axi_arsize,
    input  logic [2:0]                   dma_axi_arprot,
    input  logic [7:0]                   dma_axi_arlen,
    input  logic [1:0]                   dma_axi_arburst,

    output logic                         dma_axi_rvalid,
    input  logic                         dma_axi_rready,
    output logic [pt.DMA_BUS_TAG-1:0]    dma_axi_rid,
    output logic [63:0]                  dma_axi_rdata,
    output logic [1:0]                   dma_axi_rresp,
    output logic                         dma_axi_rlast,


  //// AHB LITE BUS
    output logic [31:0] haddr,
    /* exclude signals that are tied to constant value in axi4_to_ahb.sv */
    /*pragma coverage off*/
    output logic [2:0]  hburst,
    output logic        hmastlock,
    /*pragma coverage on*/
    output logic [3:0]  hprot,
    output logic [2:0]  hsize,
    output logic [1:0]  htrans,
    output logic        hwrite,

    input  logic [63:0] hrdata,
    input  logic        hready,
    input  logic        hresp,

    // LSU AHB Master
    output logic [31:0] lsu_haddr,
    /* exclude signals that are tied to constant value in axi4_to_ahb.sv */
    /*pragma coverage off*/
    output logic [2:0]  lsu_hburst,
    output logic        lsu_hmastlock,
    /*pragma coverage on*/
    output logic [3:0]  lsu_hprot,
    output logic [2:0]  lsu_hsize,
    output logic [1:0]  lsu_htrans,
    output logic        lsu_hwrite,
    output logic [63:0] lsu_hwdata,

    input  logic [63:0] lsu_hrdata,
    input  logic        lsu_hready,
    input  logic        lsu_hresp,

    //System Bus Debug Master
    output logic [31:0] sb_haddr,
    /* exclude signals that are tied to constant value in axi4_to_ahb.sv */
    /*pragma coverage off*/
    output logic [2:0]  sb_hburst,
    output logic        sb_hmastlock,
    /*pragma coverage on*/
    output logic [3:0]  sb_hprot,
    output logic [2:0]  sb_hsize,
    output logic [1:0]  sb_htrans,
    output logic        sb_hwrite,
    output logic [63:0] sb_hwdata,

    input  logic [63:0] sb_hrdata,
    input  logic        sb_hready,
    input  logic        sb_hresp,

    // DMA Slave
    input  logic        dma_hsel,
    input  logic [31:0] dma_haddr,
    input  logic [2:0]  dma_hburst,
    input  logic        dma_hmastlock,
    input  logic [3:0]  dma_hprot,
    input  logic [2:0]  dma_hsize,
    input  logic [1:0]  dma_htrans,
    input  logic        dma_hwrite,
    input  logic [63:0] dma_hwdata,
    input  logic        dma_hreadyin,

    output logic [63:0] dma_hrdata,
    output logic        dma_hreadyout,
    output logic        dma_hresp,

    input  logic        lsu_bus_clk_en,
    input  logic        ifu_bus_clk_en,
    input  logic        dbg_bus_clk_en,
    input  logic        dma_bus_clk_en,

    input  logic        dmi_reg_en,                // read or write
    input  logic [6:0]  dmi_reg_addr,              // address of DM register
    input  logic        dmi_reg_wr_en,             // write instruction
    input  logic [31:0] dmi_reg_wdata,             // write data
    output logic [31:0] dmi_reg_rdata,

    // Boot configuration
    input  el2_mubi_pkg::el2_mubi_t core_active_0,
    input  el2_mubi_pkg::el2_mubi_t core_active_1,
    input  el2_mubi_pkg::el2_mubi_t core_active_2,

    // ICCM/DCCM ECC status
    output logic                 iccm_ecc_single_error,
    output logic                 iccm_ecc_double_error,
    output logic                 dccm_ecc_single_error,
    output logic                 dccm_ecc_double_error,

    input logic [pt.PIC_TOTAL_INT:1]           extintsrc_req,
    input logic                   timer_int,
    input logic                   soft_int,

    // A fatal, unrecoverable fault has been detected. Once asserted it can only
    // be cleared by a hard reset via rst_l
    output el2_mubi_pkg::el2_mubi_t tmr_fatal,
    // A recoverable error has been detected and the recovery procedure is pending
    output el2_mubi_pkg::el2_mubi_t tmr_recovery_pending,
    // The recovery procedure has failed. Once asserted it can only be cleared
    // by a hard reset via rst_l
    output el2_mubi_pkg::el2_mubi_t tmr_recovery_fault,
    // Individual core fault status
    output el2_mubi_pkg::el2_mubi_t tmr_core_fault[3],

    // Excluding scan_mode from coverage as its usage is determined by the integrator of the VeeR core.
    /*pragma coverage off*/
    input logic                   scan_mode,
    /*pragma coverage on*/

    // cocotb signals
    input logic [7:0] force_address_select,
    input logic [1:0] force_core_id,
    input logic [63:0] force_data,
    input logic        force_release,
    input logic        force_update
);

    // Memory Export Interface
    el2_mem_if mem_export();
    el2_mem_if icache_export();

    assign mem_export_clk                           = mem_export.clk;

    assign mem_export_iccm_clken                    = mem_export.iccm_clken;
    assign mem_export_iccm_wren_bank                = mem_export.iccm_wren_bank;
    assign mem_export_iccm_addr_bank                = mem_export.iccm_addr_bank;
    assign mem_export_iccm_bank_wr_data             = mem_export.iccm_bank_wr_data;
    assign mem_export_iccm_bank_wr_ecc              = mem_export.iccm_bank_wr_ecc;
    assign mem_export.iccm_bank_dout                = mem_export_iccm_bank_dout;
    assign mem_export.iccm_bank_ecc                 = mem_export_iccm_bank_ecc;

    assign mem_export_dccm_clken                    = mem_export.dccm_clken;
    assign mem_export_dccm_wren_bank                = mem_export.dccm_wren_bank;
    assign mem_export_dccm_addr_bank                = mem_export.dccm_addr_bank;
    assign mem_export_dccm_wr_data_bank             = mem_export.dccm_wr_data_bank;
    assign mem_export_dccm_wr_ecc_bank              = mem_export.dccm_wr_ecc_bank;
    assign mem_export.dccm_bank_dout                = mem_export_dccm_bank_dout;
    assign mem_export.dccm_bank_ecc                 = mem_export_dccm_bank_ecc;

    assign icache_export_clk                        = icache_export.clk;

    assign icache_export_ic_b_sb_wren               = icache_export.ic_b_sb_wren;
    assign icache_export_ic_b_sb_bit_en_vec         = icache_export.ic_b_sb_bit_en_vec;
    assign icache_export.wb_packeddout_pre          = icache_export_wb_packeddout_pre;
    assign icache_export_ic_sb_wr_data              = icache_export.ic_sb_wr_data;
    assign icache_export_ic_rw_addr_bank_q          = icache_export.ic_rw_addr_bank_q;
    assign icache_export_ic_bank_way_clken_final    = icache_export.ic_bank_way_clken_final;
    assign icache_export_ic_bank_way_clken_final_up = icache_export.ic_bank_way_clken_final_up;
    assign icache_export.wb_dout_pre_up             = icache_export_wb_dout_pre_up;

    assign icache_export_ic_tag_clken_final         = icache_export.ic_tag_clken_final;
    assign icache_export_ic_tag_wren_q              = icache_export.ic_tag_wren_q;
    assign icache_export_ic_tag_wren_biten_vec      = icache_export.ic_tag_wren_biten_vec;
    assign icache_export.ic_tag_data_raw_packed_pre = icache_export_ic_tag_data_raw_packed_pre;
    assign icache_export_ic_tag_wr_data             = icache_export.ic_tag_wr_data;
    assign icache_export_ic_rw_addr_q               = icache_export.ic_rw_addr_q;
    assign icache_export.ic_tag_data_raw_pre        = icache_export_ic_tag_data_raw_pre;

    always @(posedge force_update) begin
      if(force_release) begin
        case(force_core_id)
          2'd0:
            case(force_address_select)
              8'd0: force el2_tmr_complex.cores[0].veer.trace_rv_i_address_ip = force_data;
              8'd1: force el2_tmr_complex.cores[0].veer.trace_rv_i_valid_ip = force_data;
              8'd2: force el2_tmr_complex.cores[0].veer.trace_rv_i_exception_ip = force_data;
              8'd3: force el2_tmr_complex.cores[0].veer.trace_rv_i_ecause_ip = force_data;
              8'd4: force el2_tmr_complex.cores[0].veer.trace_rv_i_interrupt_ip = force_data;
              8'd5: force el2_tmr_complex.cores[0].veer.trace_rv_i_tval_ip = force_data;
              8'd6: force el2_tmr_complex.cores[0].veer.o_debug_mode_status = force_data;
              8'd7: force el2_tmr_complex.cores[0].veer.o_cpu_halt_ack = force_data;
              8'd8: force el2_tmr_complex.cores[0].veer.o_cpu_halt_status = force_data;
              8'd9: force el2_tmr_complex.cores[0].veer.o_cpu_run_ack = force_data;
              8'd10: force el2_tmr_complex.cores[0].veer.mpc_debug_halt_ack = force_data;
              8'd11: force el2_tmr_complex.cores[0].veer.mpc_debug_run_ack = force_data;
              8'd12: force el2_tmr_complex.cores[0].veer.debug_brkpt_status = force_data;
              8'd13: force el2_tmr_complex.cores[0].veer.dec_tlu_perfcnt0 = force_data;
              8'd14: force el2_tmr_complex.cores[0].veer.dec_tlu_perfcnt1 = force_data;
              8'd15: force el2_tmr_complex.cores[0].veer.dec_tlu_perfcnt2 = force_data;
              8'd16: force el2_tmr_complex.cores[0].veer.dec_tlu_perfcnt3 = force_data;
              8'd17: force el2_tmr_complex.cores[0].veer.lsu_axi_awvalid = force_data;
              8'd18: force el2_tmr_complex.cores[0].veer.lsu_axi_awid = force_data;
              8'd19: force el2_tmr_complex.cores[0].veer.lsu_axi_awaddr = force_data;
              8'd20: force el2_tmr_complex.cores[0].veer.lsu_axi_awregion = force_data;
              8'd21: force el2_tmr_complex.cores[0].veer.lsu_axi_awlen = force_data;
              8'd22: force el2_tmr_complex.cores[0].veer.lsu_axi_awsize = force_data;
              8'd23: force el2_tmr_complex.cores[0].veer.lsu_axi_awburst = force_data;
              8'd24: force el2_tmr_complex.cores[0].veer.lsu_axi_awlock = force_data;
              8'd25: force el2_tmr_complex.cores[0].veer.lsu_axi_awcache = force_data;
              8'd26: force el2_tmr_complex.cores[0].veer.lsu_axi_awprot = force_data;
              8'd27: force el2_tmr_complex.cores[0].veer.lsu_axi_awqos = force_data;
              8'd28: force el2_tmr_complex.cores[0].veer.lsu_axi_wvalid = force_data;
              8'd29: force el2_tmr_complex.cores[0].veer.lsu_axi_wdata = force_data;
              8'd30: force el2_tmr_complex.cores[0].veer.lsu_axi_wstrb = force_data;
              8'd31: force el2_tmr_complex.cores[0].veer.lsu_axi_wlast = force_data;
              8'd32: force el2_tmr_complex.cores[0].veer.lsu_axi_bready = force_data;
              8'd33: force el2_tmr_complex.cores[0].veer.lsu_axi_arvalid = force_data;
              8'd34: force el2_tmr_complex.cores[0].veer.lsu_axi_arid = force_data;
              8'd35: force el2_tmr_complex.cores[0].veer.lsu_axi_araddr = force_data;
              8'd36: force el2_tmr_complex.cores[0].veer.lsu_axi_arregion = force_data;
              8'd37: force el2_tmr_complex.cores[0].veer.lsu_axi_arlen = force_data;
              8'd38: force el2_tmr_complex.cores[0].veer.lsu_axi_arsize = force_data;
              8'd39: force el2_tmr_complex.cores[0].veer.lsu_axi_arburst = force_data;
              8'd40: force el2_tmr_complex.cores[0].veer.lsu_axi_arlock = force_data;
              8'd41: force el2_tmr_complex.cores[0].veer.lsu_axi_arcache = force_data;
              8'd42: force el2_tmr_complex.cores[0].veer.lsu_axi_arprot = force_data;
              8'd43: force el2_tmr_complex.cores[0].veer.lsu_axi_arqos = force_data;
              8'd44: force el2_tmr_complex.cores[0].veer.lsu_axi_rready = force_data;
              8'd45: force el2_tmr_complex.cores[0].veer.ifu_axi_awvalid = force_data;
              8'd46: force el2_tmr_complex.cores[0].veer.ifu_axi_awid = force_data;
              8'd47: force el2_tmr_complex.cores[0].veer.ifu_axi_awaddr = force_data;
              8'd48: force el2_tmr_complex.cores[0].veer.ifu_axi_awregion = force_data;
              8'd49: force el2_tmr_complex.cores[0].veer.ifu_axi_awlen = force_data;
              8'd50: force el2_tmr_complex.cores[0].veer.ifu_axi_awsize = force_data;
              8'd51: force el2_tmr_complex.cores[0].veer.ifu_axi_awburst = force_data;
              8'd52: force el2_tmr_complex.cores[0].veer.ifu_axi_awlock = force_data;
              8'd53: force el2_tmr_complex.cores[0].veer.ifu_axi_awcache = force_data;
              8'd54: force el2_tmr_complex.cores[0].veer.ifu_axi_awprot = force_data;
              8'd55: force el2_tmr_complex.cores[0].veer.ifu_axi_awqos = force_data;
              8'd56: force el2_tmr_complex.cores[0].veer.ifu_axi_wvalid = force_data;
              8'd57: force el2_tmr_complex.cores[0].veer.ifu_axi_wdata = force_data;
              8'd58: force el2_tmr_complex.cores[0].veer.ifu_axi_wstrb = force_data;
              8'd59: force el2_tmr_complex.cores[0].veer.ifu_axi_wlast = force_data;
              8'd60: force el2_tmr_complex.cores[0].veer.ifu_axi_bready = force_data;
              8'd61: force el2_tmr_complex.cores[0].veer.ifu_axi_arvalid = force_data;
              8'd62: force el2_tmr_complex.cores[0].veer.ifu_axi_arid = force_data;
              8'd63: force el2_tmr_complex.cores[0].veer.ifu_axi_araddr = force_data;
              8'd64: force el2_tmr_complex.cores[0].veer.ifu_axi_arregion = force_data;
              8'd65: force el2_tmr_complex.cores[0].veer.ifu_axi_arlen = force_data;
              8'd66: force el2_tmr_complex.cores[0].veer.ifu_axi_arsize = force_data;
              8'd67: force el2_tmr_complex.cores[0].veer.ifu_axi_arburst = force_data;
              8'd68: force el2_tmr_complex.cores[0].veer.ifu_axi_arlock = force_data;
              8'd69: force el2_tmr_complex.cores[0].veer.ifu_axi_arcache = force_data;
              8'd70: force el2_tmr_complex.cores[0].veer.ifu_axi_arprot = force_data;
              8'd71: force el2_tmr_complex.cores[0].veer.ifu_axi_arqos = force_data;
              8'd72: force el2_tmr_complex.cores[0].veer.ifu_axi_rready = force_data;
              8'd73: force el2_tmr_complex.cores[0].veer.sb_axi_awvalid = force_data;
              8'd74: force el2_tmr_complex.cores[0].veer.sb_axi_awid = force_data;
              8'd75: force el2_tmr_complex.cores[0].veer.sb_axi_awaddr = force_data;
              8'd76: force el2_tmr_complex.cores[0].veer.sb_axi_awregion = force_data;
              8'd77: force el2_tmr_complex.cores[0].veer.sb_axi_awlen = force_data;
              8'd78: force el2_tmr_complex.cores[0].veer.sb_axi_awsize = force_data;
              8'd79: force el2_tmr_complex.cores[0].veer.sb_axi_awburst = force_data;
              8'd80: force el2_tmr_complex.cores[0].veer.sb_axi_awlock = force_data;
              8'd81: force el2_tmr_complex.cores[0].veer.sb_axi_awcache = force_data;
              8'd82: force el2_tmr_complex.cores[0].veer.sb_axi_awprot = force_data;
              8'd83: force el2_tmr_complex.cores[0].veer.sb_axi_awqos = force_data;
              8'd84: force el2_tmr_complex.cores[0].veer.sb_axi_wvalid = force_data;
              8'd85: force el2_tmr_complex.cores[0].veer.sb_axi_wdata = force_data;
              8'd86: force el2_tmr_complex.cores[0].veer.sb_axi_wstrb = force_data;
              8'd87: force el2_tmr_complex.cores[0].veer.sb_axi_wlast = force_data;
              8'd88: force el2_tmr_complex.cores[0].veer.sb_axi_bready = force_data;
              8'd89: force el2_tmr_complex.cores[0].veer.sb_axi_arvalid = force_data;
              8'd90: force el2_tmr_complex.cores[0].veer.sb_axi_arid = force_data;
              8'd91: force el2_tmr_complex.cores[0].veer.sb_axi_araddr = force_data;
              8'd92: force el2_tmr_complex.cores[0].veer.sb_axi_arregion = force_data;
              8'd93: force el2_tmr_complex.cores[0].veer.sb_axi_arlen = force_data;
              8'd94: force el2_tmr_complex.cores[0].veer.sb_axi_arsize = force_data;
              8'd95: force el2_tmr_complex.cores[0].veer.sb_axi_arburst = force_data;
              8'd96: force el2_tmr_complex.cores[0].veer.sb_axi_arlock = force_data;
              8'd97: force el2_tmr_complex.cores[0].veer.sb_axi_arcache = force_data;
              8'd98: force el2_tmr_complex.cores[0].veer.sb_axi_arprot = force_data;
              8'd99: force el2_tmr_complex.cores[0].veer.sb_axi_arqos = force_data;
              8'd100: force el2_tmr_complex.cores[0].veer.sb_axi_rready = force_data;
              8'd101: force el2_tmr_complex.cores[0].veer.dma_axi_awready = force_data;
              8'd102: force el2_tmr_complex.cores[0].veer.dma_axi_wready = force_data;
              8'd103: force el2_tmr_complex.cores[0].veer.dma_axi_bvalid = force_data;
              8'd104: force el2_tmr_complex.cores[0].veer.dma_axi_bresp = force_data;
              8'd105: force el2_tmr_complex.cores[0].veer.dma_axi_bid = force_data;
              8'd106: force el2_tmr_complex.cores[0].veer.dma_axi_arready = force_data;
              8'd107: force el2_tmr_complex.cores[0].veer.dma_axi_rvalid = force_data;
              8'd108: force el2_tmr_complex.cores[0].veer.dma_axi_rid = force_data;
              8'd109: force el2_tmr_complex.cores[0].veer.dma_axi_rdata = force_data;
              8'd110: force el2_tmr_complex.cores[0].veer.dma_axi_rresp = force_data;
              8'd111: force el2_tmr_complex.cores[0].veer.dma_axi_rlast = force_data;
              8'd112: force el2_tmr_complex.cores[0].veer.iccm_ecc_single_error = force_data;
              8'd113: force el2_tmr_complex.cores[0].veer.iccm_ecc_double_error = force_data;
              8'd114: force el2_tmr_complex.cores[0].veer.dccm_ecc_single_error = force_data;
              8'd115: force el2_tmr_complex.cores[0].veer.dccm_ecc_double_error = force_data;
              default: begin end
            endcase
          2'd1:
            case(force_address_select)
              8'd0: force el2_tmr_complex.cores[1].veer.trace_rv_i_address_ip = force_data;
              8'd1: force el2_tmr_complex.cores[1].veer.trace_rv_i_valid_ip = force_data;
              8'd2: force el2_tmr_complex.cores[1].veer.trace_rv_i_exception_ip = force_data;
              8'd3: force el2_tmr_complex.cores[1].veer.trace_rv_i_ecause_ip = force_data;
              8'd4: force el2_tmr_complex.cores[1].veer.trace_rv_i_interrupt_ip = force_data;
              8'd5: force el2_tmr_complex.cores[1].veer.trace_rv_i_tval_ip = force_data;
              8'd6: force el2_tmr_complex.cores[1].veer.o_debug_mode_status = force_data;
              8'd7: force el2_tmr_complex.cores[1].veer.o_cpu_halt_ack = force_data;
              8'd8: force el2_tmr_complex.cores[1].veer.o_cpu_halt_status = force_data;
              8'd9: force el2_tmr_complex.cores[1].veer.o_cpu_run_ack = force_data;
              8'd10: force el2_tmr_complex.cores[1].veer.mpc_debug_halt_ack = force_data;
              8'd11: force el2_tmr_complex.cores[1].veer.mpc_debug_run_ack = force_data;
              8'd12: force el2_tmr_complex.cores[1].veer.debug_brkpt_status = force_data;
              8'd13: force el2_tmr_complex.cores[1].veer.dec_tlu_perfcnt0 = force_data;
              8'd14: force el2_tmr_complex.cores[1].veer.dec_tlu_perfcnt1 = force_data;
              8'd15: force el2_tmr_complex.cores[1].veer.dec_tlu_perfcnt2 = force_data;
              8'd16: force el2_tmr_complex.cores[1].veer.dec_tlu_perfcnt3 = force_data;
              8'd17: force el2_tmr_complex.cores[1].veer.lsu_axi_awvalid = force_data;
              8'd18: force el2_tmr_complex.cores[1].veer.lsu_axi_awid = force_data;
              8'd19: force el2_tmr_complex.cores[1].veer.lsu_axi_awaddr = force_data;
              8'd20: force el2_tmr_complex.cores[1].veer.lsu_axi_awregion = force_data;
              8'd21: force el2_tmr_complex.cores[1].veer.lsu_axi_awlen = force_data;
              8'd22: force el2_tmr_complex.cores[1].veer.lsu_axi_awsize = force_data;
              8'd23: force el2_tmr_complex.cores[1].veer.lsu_axi_awburst = force_data;
              8'd24: force el2_tmr_complex.cores[1].veer.lsu_axi_awlock = force_data;
              8'd25: force el2_tmr_complex.cores[1].veer.lsu_axi_awcache = force_data;
              8'd26: force el2_tmr_complex.cores[1].veer.lsu_axi_awprot = force_data;
              8'd27: force el2_tmr_complex.cores[1].veer.lsu_axi_awqos = force_data;
              8'd28: force el2_tmr_complex.cores[1].veer.lsu_axi_wvalid = force_data;
              8'd29: force el2_tmr_complex.cores[1].veer.lsu_axi_wdata = force_data;
              8'd30: force el2_tmr_complex.cores[1].veer.lsu_axi_wstrb = force_data;
              8'd31: force el2_tmr_complex.cores[1].veer.lsu_axi_wlast = force_data;
              8'd32: force el2_tmr_complex.cores[1].veer.lsu_axi_bready = force_data;
              8'd33: force el2_tmr_complex.cores[1].veer.lsu_axi_arvalid = force_data;
              8'd34: force el2_tmr_complex.cores[1].veer.lsu_axi_arid = force_data;
              8'd35: force el2_tmr_complex.cores[1].veer.lsu_axi_araddr = force_data;
              8'd36: force el2_tmr_complex.cores[1].veer.lsu_axi_arregion = force_data;
              8'd37: force el2_tmr_complex.cores[1].veer.lsu_axi_arlen = force_data;
              8'd38: force el2_tmr_complex.cores[1].veer.lsu_axi_arsize = force_data;
              8'd39: force el2_tmr_complex.cores[1].veer.lsu_axi_arburst = force_data;
              8'd40: force el2_tmr_complex.cores[1].veer.lsu_axi_arlock = force_data;
              8'd41: force el2_tmr_complex.cores[1].veer.lsu_axi_arcache = force_data;
              8'd42: force el2_tmr_complex.cores[1].veer.lsu_axi_arprot = force_data;
              8'd43: force el2_tmr_complex.cores[1].veer.lsu_axi_arqos = force_data;
              8'd44: force el2_tmr_complex.cores[1].veer.lsu_axi_rready = force_data;
              8'd45: force el2_tmr_complex.cores[1].veer.ifu_axi_awvalid = force_data;
              8'd46: force el2_tmr_complex.cores[1].veer.ifu_axi_awid = force_data;
              8'd47: force el2_tmr_complex.cores[1].veer.ifu_axi_awaddr = force_data;
              8'd48: force el2_tmr_complex.cores[1].veer.ifu_axi_awregion = force_data;
              8'd49: force el2_tmr_complex.cores[1].veer.ifu_axi_awlen = force_data;
              8'd50: force el2_tmr_complex.cores[1].veer.ifu_axi_awsize = force_data;
              8'd51: force el2_tmr_complex.cores[1].veer.ifu_axi_awburst = force_data;
              8'd52: force el2_tmr_complex.cores[1].veer.ifu_axi_awlock = force_data;
              8'd53: force el2_tmr_complex.cores[1].veer.ifu_axi_awcache = force_data;
              8'd54: force el2_tmr_complex.cores[1].veer.ifu_axi_awprot = force_data;
              8'd55: force el2_tmr_complex.cores[1].veer.ifu_axi_awqos = force_data;
              8'd56: force el2_tmr_complex.cores[1].veer.ifu_axi_wvalid = force_data;
              8'd57: force el2_tmr_complex.cores[1].veer.ifu_axi_wdata = force_data;
              8'd58: force el2_tmr_complex.cores[1].veer.ifu_axi_wstrb = force_data;
              8'd59: force el2_tmr_complex.cores[1].veer.ifu_axi_wlast = force_data;
              8'd60: force el2_tmr_complex.cores[1].veer.ifu_axi_bready = force_data;
              8'd61: force el2_tmr_complex.cores[1].veer.ifu_axi_arvalid = force_data;
              8'd62: force el2_tmr_complex.cores[1].veer.ifu_axi_arid = force_data;
              8'd63: force el2_tmr_complex.cores[1].veer.ifu_axi_araddr = force_data;
              8'd64: force el2_tmr_complex.cores[1].veer.ifu_axi_arregion = force_data;
              8'd65: force el2_tmr_complex.cores[1].veer.ifu_axi_arlen = force_data;
              8'd66: force el2_tmr_complex.cores[1].veer.ifu_axi_arsize = force_data;
              8'd67: force el2_tmr_complex.cores[1].veer.ifu_axi_arburst = force_data;
              8'd68: force el2_tmr_complex.cores[1].veer.ifu_axi_arlock = force_data;
              8'd69: force el2_tmr_complex.cores[1].veer.ifu_axi_arcache = force_data;
              8'd70: force el2_tmr_complex.cores[1].veer.ifu_axi_arprot = force_data;
              8'd71: force el2_tmr_complex.cores[1].veer.ifu_axi_arqos = force_data;
              8'd72: force el2_tmr_complex.cores[1].veer.ifu_axi_rready = force_data;
              8'd73: force el2_tmr_complex.cores[1].veer.sb_axi_awvalid = force_data;
              8'd74: force el2_tmr_complex.cores[1].veer.sb_axi_awid = force_data;
              8'd75: force el2_tmr_complex.cores[1].veer.sb_axi_awaddr = force_data;
              8'd76: force el2_tmr_complex.cores[1].veer.sb_axi_awregion = force_data;
              8'd77: force el2_tmr_complex.cores[1].veer.sb_axi_awlen = force_data;
              8'd78: force el2_tmr_complex.cores[1].veer.sb_axi_awsize = force_data;
              8'd79: force el2_tmr_complex.cores[1].veer.sb_axi_awburst = force_data;
              8'd80: force el2_tmr_complex.cores[1].veer.sb_axi_awlock = force_data;
              8'd81: force el2_tmr_complex.cores[1].veer.sb_axi_awcache = force_data;
              8'd82: force el2_tmr_complex.cores[1].veer.sb_axi_awprot = force_data;
              8'd83: force el2_tmr_complex.cores[1].veer.sb_axi_awqos = force_data;
              8'd84: force el2_tmr_complex.cores[1].veer.sb_axi_wvalid = force_data;
              8'd85: force el2_tmr_complex.cores[1].veer.sb_axi_wdata = force_data;
              8'd86: force el2_tmr_complex.cores[1].veer.sb_axi_wstrb = force_data;
              8'd87: force el2_tmr_complex.cores[1].veer.sb_axi_wlast = force_data;
              8'd88: force el2_tmr_complex.cores[1].veer.sb_axi_bready = force_data;
              8'd89: force el2_tmr_complex.cores[1].veer.sb_axi_arvalid = force_data;
              8'd90: force el2_tmr_complex.cores[1].veer.sb_axi_arid = force_data;
              8'd91: force el2_tmr_complex.cores[1].veer.sb_axi_araddr = force_data;
              8'd92: force el2_tmr_complex.cores[1].veer.sb_axi_arregion = force_data;
              8'd93: force el2_tmr_complex.cores[1].veer.sb_axi_arlen = force_data;
              8'd94: force el2_tmr_complex.cores[1].veer.sb_axi_arsize = force_data;
              8'd95: force el2_tmr_complex.cores[1].veer.sb_axi_arburst = force_data;
              8'd96: force el2_tmr_complex.cores[1].veer.sb_axi_arlock = force_data;
              8'd97: force el2_tmr_complex.cores[1].veer.sb_axi_arcache = force_data;
              8'd98: force el2_tmr_complex.cores[1].veer.sb_axi_arprot = force_data;
              8'd99: force el2_tmr_complex.cores[1].veer.sb_axi_arqos = force_data;
              8'd100: force el2_tmr_complex.cores[1].veer.sb_axi_rready = force_data;
              8'd101: force el2_tmr_complex.cores[1].veer.dma_axi_awready = force_data;
              8'd102: force el2_tmr_complex.cores[1].veer.dma_axi_wready = force_data;
              8'd103: force el2_tmr_complex.cores[1].veer.dma_axi_bvalid = force_data;
              8'd104: force el2_tmr_complex.cores[1].veer.dma_axi_bresp = force_data;
              8'd105: force el2_tmr_complex.cores[1].veer.dma_axi_bid = force_data;
              8'd106: force el2_tmr_complex.cores[1].veer.dma_axi_arready = force_data;
              8'd107: force el2_tmr_complex.cores[1].veer.dma_axi_rvalid = force_data;
              8'd108: force el2_tmr_complex.cores[1].veer.dma_axi_rid = force_data;
              8'd109: force el2_tmr_complex.cores[1].veer.dma_axi_rdata = force_data;
              8'd110: force el2_tmr_complex.cores[1].veer.dma_axi_rresp = force_data;
              8'd111: force el2_tmr_complex.cores[1].veer.dma_axi_rlast = force_data;
              8'd112: force el2_tmr_complex.cores[1].veer.iccm_ecc_single_error = force_data;
              8'd113: force el2_tmr_complex.cores[1].veer.iccm_ecc_double_error = force_data;
              8'd114: force el2_tmr_complex.cores[1].veer.dccm_ecc_single_error = force_data;
              8'd115: force el2_tmr_complex.cores[1].veer.dccm_ecc_double_error = force_data;
              default: begin end
            endcase
          2'd2:
            case(force_address_select)
              8'd0: force el2_tmr_complex.cores[2].veer.trace_rv_i_address_ip = force_data;
              8'd1: force el2_tmr_complex.cores[2].veer.trace_rv_i_valid_ip = force_data;
              8'd2: force el2_tmr_complex.cores[2].veer.trace_rv_i_exception_ip = force_data;
              8'd3: force el2_tmr_complex.cores[2].veer.trace_rv_i_ecause_ip = force_data;
              8'd4: force el2_tmr_complex.cores[2].veer.trace_rv_i_interrupt_ip = force_data;
              8'd5: force el2_tmr_complex.cores[2].veer.trace_rv_i_tval_ip = force_data;
              8'd6: force el2_tmr_complex.cores[2].veer.o_debug_mode_status = force_data;
              8'd7: force el2_tmr_complex.cores[2].veer.o_cpu_halt_ack = force_data;
              8'd8: force el2_tmr_complex.cores[2].veer.o_cpu_halt_status = force_data;
              8'd9: force el2_tmr_complex.cores[2].veer.o_cpu_run_ack = force_data;
              8'd10: force el2_tmr_complex.cores[2].veer.mpc_debug_halt_ack = force_data;
              8'd11: force el2_tmr_complex.cores[2].veer.mpc_debug_run_ack = force_data;
              8'd12: force el2_tmr_complex.cores[2].veer.debug_brkpt_status = force_data;
              8'd13: force el2_tmr_complex.cores[2].veer.dec_tlu_perfcnt0 = force_data;
              8'd14: force el2_tmr_complex.cores[2].veer.dec_tlu_perfcnt1 = force_data;
              8'd15: force el2_tmr_complex.cores[2].veer.dec_tlu_perfcnt2 = force_data;
              8'd16: force el2_tmr_complex.cores[2].veer.dec_tlu_perfcnt3 = force_data;
              8'd17: force el2_tmr_complex.cores[2].veer.lsu_axi_awvalid = force_data;
              8'd18: force el2_tmr_complex.cores[2].veer.lsu_axi_awid = force_data;
              8'd19: force el2_tmr_complex.cores[2].veer.lsu_axi_awaddr = force_data;
              8'd20: force el2_tmr_complex.cores[2].veer.lsu_axi_awregion = force_data;
              8'd21: force el2_tmr_complex.cores[2].veer.lsu_axi_awlen = force_data;
              8'd22: force el2_tmr_complex.cores[2].veer.lsu_axi_awsize = force_data;
              8'd23: force el2_tmr_complex.cores[2].veer.lsu_axi_awburst = force_data;
              8'd24: force el2_tmr_complex.cores[2].veer.lsu_axi_awlock = force_data;
              8'd25: force el2_tmr_complex.cores[2].veer.lsu_axi_awcache = force_data;
              8'd26: force el2_tmr_complex.cores[2].veer.lsu_axi_awprot = force_data;
              8'd27: force el2_tmr_complex.cores[2].veer.lsu_axi_awqos = force_data;
              8'd28: force el2_tmr_complex.cores[2].veer.lsu_axi_wvalid = force_data;
              8'd29: force el2_tmr_complex.cores[2].veer.lsu_axi_wdata = force_data;
              8'd30: force el2_tmr_complex.cores[2].veer.lsu_axi_wstrb = force_data;
              8'd31: force el2_tmr_complex.cores[2].veer.lsu_axi_wlast = force_data;
              8'd32: force el2_tmr_complex.cores[2].veer.lsu_axi_bready = force_data;
              8'd33: force el2_tmr_complex.cores[2].veer.lsu_axi_arvalid = force_data;
              8'd34: force el2_tmr_complex.cores[2].veer.lsu_axi_arid = force_data;
              8'd35: force el2_tmr_complex.cores[2].veer.lsu_axi_araddr = force_data;
              8'd36: force el2_tmr_complex.cores[2].veer.lsu_axi_arregion = force_data;
              8'd37: force el2_tmr_complex.cores[2].veer.lsu_axi_arlen = force_data;
              8'd38: force el2_tmr_complex.cores[2].veer.lsu_axi_arsize = force_data;
              8'd39: force el2_tmr_complex.cores[2].veer.lsu_axi_arburst = force_data;
              8'd40: force el2_tmr_complex.cores[2].veer.lsu_axi_arlock = force_data;
              8'd41: force el2_tmr_complex.cores[2].veer.lsu_axi_arcache = force_data;
              8'd42: force el2_tmr_complex.cores[2].veer.lsu_axi_arprot = force_data;
              8'd43: force el2_tmr_complex.cores[2].veer.lsu_axi_arqos = force_data;
              8'd44: force el2_tmr_complex.cores[2].veer.lsu_axi_rready = force_data;
              8'd45: force el2_tmr_complex.cores[2].veer.ifu_axi_awvalid = force_data;
              8'd46: force el2_tmr_complex.cores[2].veer.ifu_axi_awid = force_data;
              8'd47: force el2_tmr_complex.cores[2].veer.ifu_axi_awaddr = force_data;
              8'd48: force el2_tmr_complex.cores[2].veer.ifu_axi_awregion = force_data;
              8'd49: force el2_tmr_complex.cores[2].veer.ifu_axi_awlen = force_data;
              8'd50: force el2_tmr_complex.cores[2].veer.ifu_axi_awsize = force_data;
              8'd51: force el2_tmr_complex.cores[2].veer.ifu_axi_awburst = force_data;
              8'd52: force el2_tmr_complex.cores[2].veer.ifu_axi_awlock = force_data;
              8'd53: force el2_tmr_complex.cores[2].veer.ifu_axi_awcache = force_data;
              8'd54: force el2_tmr_complex.cores[2].veer.ifu_axi_awprot = force_data;
              8'd55: force el2_tmr_complex.cores[2].veer.ifu_axi_awqos = force_data;
              8'd56: force el2_tmr_complex.cores[2].veer.ifu_axi_wvalid = force_data;
              8'd57: force el2_tmr_complex.cores[2].veer.ifu_axi_wdata = force_data;
              8'd58: force el2_tmr_complex.cores[2].veer.ifu_axi_wstrb = force_data;
              8'd59: force el2_tmr_complex.cores[2].veer.ifu_axi_wlast = force_data;
              8'd60: force el2_tmr_complex.cores[2].veer.ifu_axi_bready = force_data;
              8'd61: force el2_tmr_complex.cores[2].veer.ifu_axi_arvalid = force_data;
              8'd62: force el2_tmr_complex.cores[2].veer.ifu_axi_arid = force_data;
              8'd63: force el2_tmr_complex.cores[2].veer.ifu_axi_araddr = force_data;
              8'd64: force el2_tmr_complex.cores[2].veer.ifu_axi_arregion = force_data;
              8'd65: force el2_tmr_complex.cores[2].veer.ifu_axi_arlen = force_data;
              8'd66: force el2_tmr_complex.cores[2].veer.ifu_axi_arsize = force_data;
              8'd67: force el2_tmr_complex.cores[2].veer.ifu_axi_arburst = force_data;
              8'd68: force el2_tmr_complex.cores[2].veer.ifu_axi_arlock = force_data;
              8'd69: force el2_tmr_complex.cores[2].veer.ifu_axi_arcache = force_data;
              8'd70: force el2_tmr_complex.cores[2].veer.ifu_axi_arprot = force_data;
              8'd71: force el2_tmr_complex.cores[2].veer.ifu_axi_arqos = force_data;
              8'd72: force el2_tmr_complex.cores[2].veer.ifu_axi_rready = force_data;
              8'd73: force el2_tmr_complex.cores[2].veer.sb_axi_awvalid = force_data;
              8'd74: force el2_tmr_complex.cores[2].veer.sb_axi_awid = force_data;
              8'd75: force el2_tmr_complex.cores[2].veer.sb_axi_awaddr = force_data;
              8'd76: force el2_tmr_complex.cores[2].veer.sb_axi_awregion = force_data;
              8'd77: force el2_tmr_complex.cores[2].veer.sb_axi_awlen = force_data;
              8'd78: force el2_tmr_complex.cores[2].veer.sb_axi_awsize = force_data;
              8'd79: force el2_tmr_complex.cores[2].veer.sb_axi_awburst = force_data;
              8'd80: force el2_tmr_complex.cores[2].veer.sb_axi_awlock = force_data;
              8'd81: force el2_tmr_complex.cores[2].veer.sb_axi_awcache = force_data;
              8'd82: force el2_tmr_complex.cores[2].veer.sb_axi_awprot = force_data;
              8'd83: force el2_tmr_complex.cores[2].veer.sb_axi_awqos = force_data;
              8'd84: force el2_tmr_complex.cores[2].veer.sb_axi_wvalid = force_data;
              8'd85: force el2_tmr_complex.cores[2].veer.sb_axi_wdata = force_data;
              8'd86: force el2_tmr_complex.cores[2].veer.sb_axi_wstrb = force_data;
              8'd87: force el2_tmr_complex.cores[2].veer.sb_axi_wlast = force_data;
              8'd88: force el2_tmr_complex.cores[2].veer.sb_axi_bready = force_data;
              8'd89: force el2_tmr_complex.cores[2].veer.sb_axi_arvalid = force_data;
              8'd90: force el2_tmr_complex.cores[2].veer.sb_axi_arid = force_data;
              8'd91: force el2_tmr_complex.cores[2].veer.sb_axi_araddr = force_data;
              8'd92: force el2_tmr_complex.cores[2].veer.sb_axi_arregion = force_data;
              8'd93: force el2_tmr_complex.cores[2].veer.sb_axi_arlen = force_data;
              8'd94: force el2_tmr_complex.cores[2].veer.sb_axi_arsize = force_data;
              8'd95: force el2_tmr_complex.cores[2].veer.sb_axi_arburst = force_data;
              8'd96: force el2_tmr_complex.cores[2].veer.sb_axi_arlock = force_data;
              8'd97: force el2_tmr_complex.cores[2].veer.sb_axi_arcache = force_data;
              8'd98: force el2_tmr_complex.cores[2].veer.sb_axi_arprot = force_data;
              8'd99: force el2_tmr_complex.cores[2].veer.sb_axi_arqos = force_data;
              8'd100: force el2_tmr_complex.cores[2].veer.sb_axi_rready = force_data;
              8'd101: force el2_tmr_complex.cores[2].veer.dma_axi_awready = force_data;
              8'd102: force el2_tmr_complex.cores[2].veer.dma_axi_wready = force_data;
              8'd103: force el2_tmr_complex.cores[2].veer.dma_axi_bvalid = force_data;
              8'd104: force el2_tmr_complex.cores[2].veer.dma_axi_bresp = force_data;
              8'd105: force el2_tmr_complex.cores[2].veer.dma_axi_bid = force_data;
              8'd106: force el2_tmr_complex.cores[2].veer.dma_axi_arready = force_data;
              8'd107: force el2_tmr_complex.cores[2].veer.dma_axi_rvalid = force_data;
              8'd108: force el2_tmr_complex.cores[2].veer.dma_axi_rid = force_data;
              8'd109: force el2_tmr_complex.cores[2].veer.dma_axi_rdata = force_data;
              8'd110: force el2_tmr_complex.cores[2].veer.dma_axi_rresp = force_data;
              8'd111: force el2_tmr_complex.cores[2].veer.dma_axi_rlast = force_data;
              8'd112: force el2_tmr_complex.cores[2].veer.iccm_ecc_single_error = force_data;
              8'd113: force el2_tmr_complex.cores[2].veer.iccm_ecc_double_error = force_data;
              8'd114: force el2_tmr_complex.cores[2].veer.dccm_ecc_single_error = force_data;
              8'd115: force el2_tmr_complex.cores[2].veer.dccm_ecc_double_error = force_data;
              default: begin end
            endcase
          2'd3: force el2_tmr_complex.tmr_output_inhibit = force_data;
          default: begin end
        endcase
      end else begin
        case(force_core_id)
          2'd0:
            case(force_address_select)
              8'd0: release el2_tmr_complex.cores[0].veer.trace_rv_i_address_ip;
              8'd1: release el2_tmr_complex.cores[0].veer.trace_rv_i_valid_ip;
              8'd2: release el2_tmr_complex.cores[0].veer.trace_rv_i_exception_ip;
              8'd3: release el2_tmr_complex.cores[0].veer.trace_rv_i_ecause_ip;
              8'd4: release el2_tmr_complex.cores[0].veer.trace_rv_i_interrupt_ip;
              8'd5: release el2_tmr_complex.cores[0].veer.trace_rv_i_tval_ip;
              8'd6: release el2_tmr_complex.cores[0].veer.o_debug_mode_status;
              8'd7: release el2_tmr_complex.cores[0].veer.o_cpu_halt_ack;
              8'd8: release el2_tmr_complex.cores[0].veer.o_cpu_halt_status;
              8'd9: release el2_tmr_complex.cores[0].veer.o_cpu_run_ack;
              8'd10: release el2_tmr_complex.cores[0].veer.mpc_debug_halt_ack;
              8'd11: release el2_tmr_complex.cores[0].veer.mpc_debug_run_ack;
              8'd12: release el2_tmr_complex.cores[0].veer.debug_brkpt_status;
              8'd13: release el2_tmr_complex.cores[0].veer.dec_tlu_perfcnt0;
              8'd14: release el2_tmr_complex.cores[0].veer.dec_tlu_perfcnt1;
              8'd15: release el2_tmr_complex.cores[0].veer.dec_tlu_perfcnt2;
              8'd16: release el2_tmr_complex.cores[0].veer.dec_tlu_perfcnt3;
              8'd17: release el2_tmr_complex.cores[0].veer.lsu_axi_awvalid;
              8'd18: release el2_tmr_complex.cores[0].veer.lsu_axi_awid;
              8'd19: release el2_tmr_complex.cores[0].veer.lsu_axi_awaddr;
              8'd20: release el2_tmr_complex.cores[0].veer.lsu_axi_awregion;
              8'd21: release el2_tmr_complex.cores[0].veer.lsu_axi_awlen;
              8'd22: release el2_tmr_complex.cores[0].veer.lsu_axi_awsize;
              8'd23: release el2_tmr_complex.cores[0].veer.lsu_axi_awburst;
              8'd24: release el2_tmr_complex.cores[0].veer.lsu_axi_awlock;
              8'd25: release el2_tmr_complex.cores[0].veer.lsu_axi_awcache;
              8'd26: release el2_tmr_complex.cores[0].veer.lsu_axi_awprot;
              8'd27: release el2_tmr_complex.cores[0].veer.lsu_axi_awqos;
              8'd28: release el2_tmr_complex.cores[0].veer.lsu_axi_wvalid;
              8'd29: release el2_tmr_complex.cores[0].veer.lsu_axi_wdata;
              8'd30: release el2_tmr_complex.cores[0].veer.lsu_axi_wstrb;
              8'd31: release el2_tmr_complex.cores[0].veer.lsu_axi_wlast;
              8'd32: release el2_tmr_complex.cores[0].veer.lsu_axi_bready;
              8'd33: release el2_tmr_complex.cores[0].veer.lsu_axi_arvalid;
              8'd34: release el2_tmr_complex.cores[0].veer.lsu_axi_arid;
              8'd35: release el2_tmr_complex.cores[0].veer.lsu_axi_araddr;
              8'd36: release el2_tmr_complex.cores[0].veer.lsu_axi_arregion;
              8'd37: release el2_tmr_complex.cores[0].veer.lsu_axi_arlen;
              8'd38: release el2_tmr_complex.cores[0].veer.lsu_axi_arsize;
              8'd39: release el2_tmr_complex.cores[0].veer.lsu_axi_arburst;
              8'd40: release el2_tmr_complex.cores[0].veer.lsu_axi_arlock;
              8'd41: release el2_tmr_complex.cores[0].veer.lsu_axi_arcache;
              8'd42: release el2_tmr_complex.cores[0].veer.lsu_axi_arprot;
              8'd43: release el2_tmr_complex.cores[0].veer.lsu_axi_arqos;
              8'd44: release el2_tmr_complex.cores[0].veer.lsu_axi_rready;
              8'd45: release el2_tmr_complex.cores[0].veer.ifu_axi_awvalid;
              8'd46: release el2_tmr_complex.cores[0].veer.ifu_axi_awid;
              8'd47: release el2_tmr_complex.cores[0].veer.ifu_axi_awaddr;
              8'd48: release el2_tmr_complex.cores[0].veer.ifu_axi_awregion;
              8'd49: release el2_tmr_complex.cores[0].veer.ifu_axi_awlen;
              8'd50: release el2_tmr_complex.cores[0].veer.ifu_axi_awsize;
              8'd51: release el2_tmr_complex.cores[0].veer.ifu_axi_awburst;
              8'd52: release el2_tmr_complex.cores[0].veer.ifu_axi_awlock;
              8'd53: release el2_tmr_complex.cores[0].veer.ifu_axi_awcache;
              8'd54: release el2_tmr_complex.cores[0].veer.ifu_axi_awprot;
              8'd55: release el2_tmr_complex.cores[0].veer.ifu_axi_awqos;
              8'd56: release el2_tmr_complex.cores[0].veer.ifu_axi_wvalid;
              8'd57: release el2_tmr_complex.cores[0].veer.ifu_axi_wdata;
              8'd58: release el2_tmr_complex.cores[0].veer.ifu_axi_wstrb;
              8'd59: release el2_tmr_complex.cores[0].veer.ifu_axi_wlast;
              8'd60: release el2_tmr_complex.cores[0].veer.ifu_axi_bready;
              8'd61: release el2_tmr_complex.cores[0].veer.ifu_axi_arvalid;
              8'd62: release el2_tmr_complex.cores[0].veer.ifu_axi_arid;
              8'd63: release el2_tmr_complex.cores[0].veer.ifu_axi_araddr;
              8'd64: release el2_tmr_complex.cores[0].veer.ifu_axi_arregion;
              8'd65: release el2_tmr_complex.cores[0].veer.ifu_axi_arlen;
              8'd66: release el2_tmr_complex.cores[0].veer.ifu_axi_arsize;
              8'd67: release el2_tmr_complex.cores[0].veer.ifu_axi_arburst;
              8'd68: release el2_tmr_complex.cores[0].veer.ifu_axi_arlock;
              8'd69: release el2_tmr_complex.cores[0].veer.ifu_axi_arcache;
              8'd70: release el2_tmr_complex.cores[0].veer.ifu_axi_arprot;
              8'd71: release el2_tmr_complex.cores[0].veer.ifu_axi_arqos;
              8'd72: release el2_tmr_complex.cores[0].veer.ifu_axi_rready;
              8'd73: release el2_tmr_complex.cores[0].veer.sb_axi_awvalid;
              8'd74: release el2_tmr_complex.cores[0].veer.sb_axi_awid;
              8'd75: release el2_tmr_complex.cores[0].veer.sb_axi_awaddr;
              8'd76: release el2_tmr_complex.cores[0].veer.sb_axi_awregion;
              8'd77: release el2_tmr_complex.cores[0].veer.sb_axi_awlen;
              8'd78: release el2_tmr_complex.cores[0].veer.sb_axi_awsize;
              8'd79: release el2_tmr_complex.cores[0].veer.sb_axi_awburst;
              8'd80: release el2_tmr_complex.cores[0].veer.sb_axi_awlock;
              8'd81: release el2_tmr_complex.cores[0].veer.sb_axi_awcache;
              8'd82: release el2_tmr_complex.cores[0].veer.sb_axi_awprot;
              8'd83: release el2_tmr_complex.cores[0].veer.sb_axi_awqos;
              8'd84: release el2_tmr_complex.cores[0].veer.sb_axi_wvalid;
              8'd85: release el2_tmr_complex.cores[0].veer.sb_axi_wdata;
              8'd86: release el2_tmr_complex.cores[0].veer.sb_axi_wstrb;
              8'd87: release el2_tmr_complex.cores[0].veer.sb_axi_wlast;
              8'd88: release el2_tmr_complex.cores[0].veer.sb_axi_bready;
              8'd89: release el2_tmr_complex.cores[0].veer.sb_axi_arvalid;
              8'd90: release el2_tmr_complex.cores[0].veer.sb_axi_arid;
              8'd91: release el2_tmr_complex.cores[0].veer.sb_axi_araddr;
              8'd92: release el2_tmr_complex.cores[0].veer.sb_axi_arregion;
              8'd93: release el2_tmr_complex.cores[0].veer.sb_axi_arlen;
              8'd94: release el2_tmr_complex.cores[0].veer.sb_axi_arsize;
              8'd95: release el2_tmr_complex.cores[0].veer.sb_axi_arburst;
              8'd96: release el2_tmr_complex.cores[0].veer.sb_axi_arlock;
              8'd97: release el2_tmr_complex.cores[0].veer.sb_axi_arcache;
              8'd98: release el2_tmr_complex.cores[0].veer.sb_axi_arprot;
              8'd99: release el2_tmr_complex.cores[0].veer.sb_axi_arqos;
              8'd100: release el2_tmr_complex.cores[0].veer.sb_axi_rready;
              8'd101: release el2_tmr_complex.cores[0].veer.dma_axi_awready;
              8'd102: release el2_tmr_complex.cores[0].veer.dma_axi_wready;
              8'd103: release el2_tmr_complex.cores[0].veer.dma_axi_bvalid;
              8'd104: release el2_tmr_complex.cores[0].veer.dma_axi_bresp;
              8'd105: release el2_tmr_complex.cores[0].veer.dma_axi_bid;
              8'd106: release el2_tmr_complex.cores[0].veer.dma_axi_arready;
              8'd107: release el2_tmr_complex.cores[0].veer.dma_axi_rvalid;
              8'd108: release el2_tmr_complex.cores[0].veer.dma_axi_rid;
              8'd109: release el2_tmr_complex.cores[0].veer.dma_axi_rdata;
              8'd110: release el2_tmr_complex.cores[0].veer.dma_axi_rresp;
              8'd111: release el2_tmr_complex.cores[0].veer.dma_axi_rlast;
              8'd112: release el2_tmr_complex.cores[0].veer.iccm_ecc_single_error;
              8'd113: release el2_tmr_complex.cores[0].veer.iccm_ecc_double_error;
              8'd114: release el2_tmr_complex.cores[0].veer.dccm_ecc_single_error;
              8'd115: release el2_tmr_complex.cores[0].veer.dccm_ecc_double_error;
              default: begin end
            endcase
          2'd1:
            case(force_address_select)
              8'd0: release el2_tmr_complex.cores[1].veer.trace_rv_i_address_ip;
              8'd1: release el2_tmr_complex.cores[1].veer.trace_rv_i_valid_ip;
              8'd2: release el2_tmr_complex.cores[1].veer.trace_rv_i_exception_ip;
              8'd3: release el2_tmr_complex.cores[1].veer.trace_rv_i_ecause_ip;
              8'd4: release el2_tmr_complex.cores[1].veer.trace_rv_i_interrupt_ip;
              8'd5: release el2_tmr_complex.cores[1].veer.trace_rv_i_tval_ip;
              8'd6: release el2_tmr_complex.cores[1].veer.o_debug_mode_status;
              8'd7: release el2_tmr_complex.cores[1].veer.o_cpu_halt_ack;
              8'd8: release el2_tmr_complex.cores[1].veer.o_cpu_halt_status;
              8'd9: release el2_tmr_complex.cores[1].veer.o_cpu_run_ack;
              8'd10: release el2_tmr_complex.cores[1].veer.mpc_debug_halt_ack;
              8'd11: release el2_tmr_complex.cores[1].veer.mpc_debug_run_ack;
              8'd12: release el2_tmr_complex.cores[1].veer.debug_brkpt_status;
              8'd13: release el2_tmr_complex.cores[1].veer.dec_tlu_perfcnt0;
              8'd14: release el2_tmr_complex.cores[1].veer.dec_tlu_perfcnt1;
              8'd15: release el2_tmr_complex.cores[1].veer.dec_tlu_perfcnt2;
              8'd16: release el2_tmr_complex.cores[1].veer.dec_tlu_perfcnt3;
              8'd17: release el2_tmr_complex.cores[1].veer.lsu_axi_awvalid;
              8'd18: release el2_tmr_complex.cores[1].veer.lsu_axi_awid;
              8'd19: release el2_tmr_complex.cores[1].veer.lsu_axi_awaddr;
              8'd20: release el2_tmr_complex.cores[1].veer.lsu_axi_awregion;
              8'd21: release el2_tmr_complex.cores[1].veer.lsu_axi_awlen;
              8'd22: release el2_tmr_complex.cores[1].veer.lsu_axi_awsize;
              8'd23: release el2_tmr_complex.cores[1].veer.lsu_axi_awburst;
              8'd24: release el2_tmr_complex.cores[1].veer.lsu_axi_awlock;
              8'd25: release el2_tmr_complex.cores[1].veer.lsu_axi_awcache;
              8'd26: release el2_tmr_complex.cores[1].veer.lsu_axi_awprot;
              8'd27: release el2_tmr_complex.cores[1].veer.lsu_axi_awqos;
              8'd28: release el2_tmr_complex.cores[1].veer.lsu_axi_wvalid;
              8'd29: release el2_tmr_complex.cores[1].veer.lsu_axi_wdata;
              8'd30: release el2_tmr_complex.cores[1].veer.lsu_axi_wstrb;
              8'd31: release el2_tmr_complex.cores[1].veer.lsu_axi_wlast;
              8'd32: release el2_tmr_complex.cores[1].veer.lsu_axi_bready;
              8'd33: release el2_tmr_complex.cores[1].veer.lsu_axi_arvalid;
              8'd34: release el2_tmr_complex.cores[1].veer.lsu_axi_arid;
              8'd35: release el2_tmr_complex.cores[1].veer.lsu_axi_araddr;
              8'd36: release el2_tmr_complex.cores[1].veer.lsu_axi_arregion;
              8'd37: release el2_tmr_complex.cores[1].veer.lsu_axi_arlen;
              8'd38: release el2_tmr_complex.cores[1].veer.lsu_axi_arsize;
              8'd39: release el2_tmr_complex.cores[1].veer.lsu_axi_arburst;
              8'd40: release el2_tmr_complex.cores[1].veer.lsu_axi_arlock;
              8'd41: release el2_tmr_complex.cores[1].veer.lsu_axi_arcache;
              8'd42: release el2_tmr_complex.cores[1].veer.lsu_axi_arprot;
              8'd43: release el2_tmr_complex.cores[1].veer.lsu_axi_arqos;
              8'd44: release el2_tmr_complex.cores[1].veer.lsu_axi_rready;
              8'd45: release el2_tmr_complex.cores[1].veer.ifu_axi_awvalid;
              8'd46: release el2_tmr_complex.cores[1].veer.ifu_axi_awid;
              8'd47: release el2_tmr_complex.cores[1].veer.ifu_axi_awaddr;
              8'd48: release el2_tmr_complex.cores[1].veer.ifu_axi_awregion;
              8'd49: release el2_tmr_complex.cores[1].veer.ifu_axi_awlen;
              8'd50: release el2_tmr_complex.cores[1].veer.ifu_axi_awsize;
              8'd51: release el2_tmr_complex.cores[1].veer.ifu_axi_awburst;
              8'd52: release el2_tmr_complex.cores[1].veer.ifu_axi_awlock;
              8'd53: release el2_tmr_complex.cores[1].veer.ifu_axi_awcache;
              8'd54: release el2_tmr_complex.cores[1].veer.ifu_axi_awprot;
              8'd55: release el2_tmr_complex.cores[1].veer.ifu_axi_awqos;
              8'd56: release el2_tmr_complex.cores[1].veer.ifu_axi_wvalid;
              8'd57: release el2_tmr_complex.cores[1].veer.ifu_axi_wdata;
              8'd58: release el2_tmr_complex.cores[1].veer.ifu_axi_wstrb;
              8'd59: release el2_tmr_complex.cores[1].veer.ifu_axi_wlast;
              8'd60: release el2_tmr_complex.cores[1].veer.ifu_axi_bready;
              8'd61: release el2_tmr_complex.cores[1].veer.ifu_axi_arvalid;
              8'd62: release el2_tmr_complex.cores[1].veer.ifu_axi_arid;
              8'd63: release el2_tmr_complex.cores[1].veer.ifu_axi_araddr;
              8'd64: release el2_tmr_complex.cores[1].veer.ifu_axi_arregion;
              8'd65: release el2_tmr_complex.cores[1].veer.ifu_axi_arlen;
              8'd66: release el2_tmr_complex.cores[1].veer.ifu_axi_arsize;
              8'd67: release el2_tmr_complex.cores[1].veer.ifu_axi_arburst;
              8'd68: release el2_tmr_complex.cores[1].veer.ifu_axi_arlock;
              8'd69: release el2_tmr_complex.cores[1].veer.ifu_axi_arcache;
              8'd70: release el2_tmr_complex.cores[1].veer.ifu_axi_arprot;
              8'd71: release el2_tmr_complex.cores[1].veer.ifu_axi_arqos;
              8'd72: release el2_tmr_complex.cores[1].veer.ifu_axi_rready;
              8'd73: release el2_tmr_complex.cores[1].veer.sb_axi_awvalid;
              8'd74: release el2_tmr_complex.cores[1].veer.sb_axi_awid;
              8'd75: release el2_tmr_complex.cores[1].veer.sb_axi_awaddr;
              8'd76: release el2_tmr_complex.cores[1].veer.sb_axi_awregion;
              8'd77: release el2_tmr_complex.cores[1].veer.sb_axi_awlen;
              8'd78: release el2_tmr_complex.cores[1].veer.sb_axi_awsize;
              8'd79: release el2_tmr_complex.cores[1].veer.sb_axi_awburst;
              8'd80: release el2_tmr_complex.cores[1].veer.sb_axi_awlock;
              8'd81: release el2_tmr_complex.cores[1].veer.sb_axi_awcache;
              8'd82: release el2_tmr_complex.cores[1].veer.sb_axi_awprot;
              8'd83: release el2_tmr_complex.cores[1].veer.sb_axi_awqos;
              8'd84: release el2_tmr_complex.cores[1].veer.sb_axi_wvalid;
              8'd85: release el2_tmr_complex.cores[1].veer.sb_axi_wdata;
              8'd86: release el2_tmr_complex.cores[1].veer.sb_axi_wstrb;
              8'd87: release el2_tmr_complex.cores[1].veer.sb_axi_wlast;
              8'd88: release el2_tmr_complex.cores[1].veer.sb_axi_bready;
              8'd89: release el2_tmr_complex.cores[1].veer.sb_axi_arvalid;
              8'd90: release el2_tmr_complex.cores[1].veer.sb_axi_arid;
              8'd91: release el2_tmr_complex.cores[1].veer.sb_axi_araddr;
              8'd92: release el2_tmr_complex.cores[1].veer.sb_axi_arregion;
              8'd93: release el2_tmr_complex.cores[1].veer.sb_axi_arlen;
              8'd94: release el2_tmr_complex.cores[1].veer.sb_axi_arsize;
              8'd95: release el2_tmr_complex.cores[1].veer.sb_axi_arburst;
              8'd96: release el2_tmr_complex.cores[1].veer.sb_axi_arlock;
              8'd97: release el2_tmr_complex.cores[1].veer.sb_axi_arcache;
              8'd98: release el2_tmr_complex.cores[1].veer.sb_axi_arprot;
              8'd99: release el2_tmr_complex.cores[1].veer.sb_axi_arqos;
              8'd100: release el2_tmr_complex.cores[1].veer.sb_axi_rready;
              8'd101: release el2_tmr_complex.cores[1].veer.dma_axi_awready;
              8'd102: release el2_tmr_complex.cores[1].veer.dma_axi_wready;
              8'd103: release el2_tmr_complex.cores[1].veer.dma_axi_bvalid;
              8'd104: release el2_tmr_complex.cores[1].veer.dma_axi_bresp;
              8'd105: release el2_tmr_complex.cores[1].veer.dma_axi_bid;
              8'd106: release el2_tmr_complex.cores[1].veer.dma_axi_arready;
              8'd107: release el2_tmr_complex.cores[1].veer.dma_axi_rvalid;
              8'd108: release el2_tmr_complex.cores[1].veer.dma_axi_rid;
              8'd109: release el2_tmr_complex.cores[1].veer.dma_axi_rdata;
              8'd110: release el2_tmr_complex.cores[1].veer.dma_axi_rresp;
              8'd111: release el2_tmr_complex.cores[1].veer.dma_axi_rlast;
              8'd112: release el2_tmr_complex.cores[1].veer.iccm_ecc_single_error;
              8'd113: release el2_tmr_complex.cores[1].veer.iccm_ecc_double_error;
              8'd114: release el2_tmr_complex.cores[1].veer.dccm_ecc_single_error;
              8'd115: release el2_tmr_complex.cores[1].veer.dccm_ecc_double_error;
              default: begin end
            endcase
          2'd2:
            case(force_address_select)
              8'd0: release el2_tmr_complex.cores[2].veer.trace_rv_i_address_ip;
              8'd1: release el2_tmr_complex.cores[2].veer.trace_rv_i_valid_ip;
              8'd2: release el2_tmr_complex.cores[2].veer.trace_rv_i_exception_ip;
              8'd3: release el2_tmr_complex.cores[2].veer.trace_rv_i_ecause_ip;
              8'd4: release el2_tmr_complex.cores[2].veer.trace_rv_i_interrupt_ip;
              8'd5: release el2_tmr_complex.cores[2].veer.trace_rv_i_tval_ip;
              8'd6: release el2_tmr_complex.cores[2].veer.o_debug_mode_status;
              8'd7: release el2_tmr_complex.cores[2].veer.o_cpu_halt_ack;
              8'd8: release el2_tmr_complex.cores[2].veer.o_cpu_halt_status;
              8'd9: release el2_tmr_complex.cores[2].veer.o_cpu_run_ack;
              8'd10: release el2_tmr_complex.cores[2].veer.mpc_debug_halt_ack;
              8'd11: release el2_tmr_complex.cores[2].veer.mpc_debug_run_ack;
              8'd12: release el2_tmr_complex.cores[2].veer.debug_brkpt_status;
              8'd13: release el2_tmr_complex.cores[2].veer.dec_tlu_perfcnt0;
              8'd14: release el2_tmr_complex.cores[2].veer.dec_tlu_perfcnt1;
              8'd15: release el2_tmr_complex.cores[2].veer.dec_tlu_perfcnt2;
              8'd16: release el2_tmr_complex.cores[2].veer.dec_tlu_perfcnt3;
              8'd17: release el2_tmr_complex.cores[2].veer.lsu_axi_awvalid;
              8'd18: release el2_tmr_complex.cores[2].veer.lsu_axi_awid;
              8'd19: release el2_tmr_complex.cores[2].veer.lsu_axi_awaddr;
              8'd20: release el2_tmr_complex.cores[2].veer.lsu_axi_awregion;
              8'd21: release el2_tmr_complex.cores[2].veer.lsu_axi_awlen;
              8'd22: release el2_tmr_complex.cores[2].veer.lsu_axi_awsize;
              8'd23: release el2_tmr_complex.cores[2].veer.lsu_axi_awburst;
              8'd24: release el2_tmr_complex.cores[2].veer.lsu_axi_awlock;
              8'd25: release el2_tmr_complex.cores[2].veer.lsu_axi_awcache;
              8'd26: release el2_tmr_complex.cores[2].veer.lsu_axi_awprot;
              8'd27: release el2_tmr_complex.cores[2].veer.lsu_axi_awqos;
              8'd28: release el2_tmr_complex.cores[2].veer.lsu_axi_wvalid;
              8'd29: release el2_tmr_complex.cores[2].veer.lsu_axi_wdata;
              8'd30: release el2_tmr_complex.cores[2].veer.lsu_axi_wstrb;
              8'd31: release el2_tmr_complex.cores[2].veer.lsu_axi_wlast;
              8'd32: release el2_tmr_complex.cores[2].veer.lsu_axi_bready;
              8'd33: release el2_tmr_complex.cores[2].veer.lsu_axi_arvalid;
              8'd34: release el2_tmr_complex.cores[2].veer.lsu_axi_arid;
              8'd35: release el2_tmr_complex.cores[2].veer.lsu_axi_araddr;
              8'd36: release el2_tmr_complex.cores[2].veer.lsu_axi_arregion;
              8'd37: release el2_tmr_complex.cores[2].veer.lsu_axi_arlen;
              8'd38: release el2_tmr_complex.cores[2].veer.lsu_axi_arsize;
              8'd39: release el2_tmr_complex.cores[2].veer.lsu_axi_arburst;
              8'd40: release el2_tmr_complex.cores[2].veer.lsu_axi_arlock;
              8'd41: release el2_tmr_complex.cores[2].veer.lsu_axi_arcache;
              8'd42: release el2_tmr_complex.cores[2].veer.lsu_axi_arprot;
              8'd43: release el2_tmr_complex.cores[2].veer.lsu_axi_arqos;
              8'd44: release el2_tmr_complex.cores[2].veer.lsu_axi_rready;
              8'd45: release el2_tmr_complex.cores[2].veer.ifu_axi_awvalid;
              8'd46: release el2_tmr_complex.cores[2].veer.ifu_axi_awid;
              8'd47: release el2_tmr_complex.cores[2].veer.ifu_axi_awaddr;
              8'd48: release el2_tmr_complex.cores[2].veer.ifu_axi_awregion;
              8'd49: release el2_tmr_complex.cores[2].veer.ifu_axi_awlen;
              8'd50: release el2_tmr_complex.cores[2].veer.ifu_axi_awsize;
              8'd51: release el2_tmr_complex.cores[2].veer.ifu_axi_awburst;
              8'd52: release el2_tmr_complex.cores[2].veer.ifu_axi_awlock;
              8'd53: release el2_tmr_complex.cores[2].veer.ifu_axi_awcache;
              8'd54: release el2_tmr_complex.cores[2].veer.ifu_axi_awprot;
              8'd55: release el2_tmr_complex.cores[2].veer.ifu_axi_awqos;
              8'd56: release el2_tmr_complex.cores[2].veer.ifu_axi_wvalid;
              8'd57: release el2_tmr_complex.cores[2].veer.ifu_axi_wdata;
              8'd58: release el2_tmr_complex.cores[2].veer.ifu_axi_wstrb;
              8'd59: release el2_tmr_complex.cores[2].veer.ifu_axi_wlast;
              8'd60: release el2_tmr_complex.cores[2].veer.ifu_axi_bready;
              8'd61: release el2_tmr_complex.cores[2].veer.ifu_axi_arvalid;
              8'd62: release el2_tmr_complex.cores[2].veer.ifu_axi_arid;
              8'd63: release el2_tmr_complex.cores[2].veer.ifu_axi_araddr;
              8'd64: release el2_tmr_complex.cores[2].veer.ifu_axi_arregion;
              8'd65: release el2_tmr_complex.cores[2].veer.ifu_axi_arlen;
              8'd66: release el2_tmr_complex.cores[2].veer.ifu_axi_arsize;
              8'd67: release el2_tmr_complex.cores[2].veer.ifu_axi_arburst;
              8'd68: release el2_tmr_complex.cores[2].veer.ifu_axi_arlock;
              8'd69: release el2_tmr_complex.cores[2].veer.ifu_axi_arcache;
              8'd70: release el2_tmr_complex.cores[2].veer.ifu_axi_arprot;
              8'd71: release el2_tmr_complex.cores[2].veer.ifu_axi_arqos;
              8'd72: release el2_tmr_complex.cores[2].veer.ifu_axi_rready;
              8'd73: release el2_tmr_complex.cores[2].veer.sb_axi_awvalid;
              8'd74: release el2_tmr_complex.cores[2].veer.sb_axi_awid;
              8'd75: release el2_tmr_complex.cores[2].veer.sb_axi_awaddr;
              8'd76: release el2_tmr_complex.cores[2].veer.sb_axi_awregion;
              8'd77: release el2_tmr_complex.cores[2].veer.sb_axi_awlen;
              8'd78: release el2_tmr_complex.cores[2].veer.sb_axi_awsize;
              8'd79: release el2_tmr_complex.cores[2].veer.sb_axi_awburst;
              8'd80: release el2_tmr_complex.cores[2].veer.sb_axi_awlock;
              8'd81: release el2_tmr_complex.cores[2].veer.sb_axi_awcache;
              8'd82: release el2_tmr_complex.cores[2].veer.sb_axi_awprot;
              8'd83: release el2_tmr_complex.cores[2].veer.sb_axi_awqos;
              8'd84: release el2_tmr_complex.cores[2].veer.sb_axi_wvalid;
              8'd85: release el2_tmr_complex.cores[2].veer.sb_axi_wdata;
              8'd86: release el2_tmr_complex.cores[2].veer.sb_axi_wstrb;
              8'd87: release el2_tmr_complex.cores[2].veer.sb_axi_wlast;
              8'd88: release el2_tmr_complex.cores[2].veer.sb_axi_bready;
              8'd89: release el2_tmr_complex.cores[2].veer.sb_axi_arvalid;
              8'd90: release el2_tmr_complex.cores[2].veer.sb_axi_arid;
              8'd91: release el2_tmr_complex.cores[2].veer.sb_axi_araddr;
              8'd92: release el2_tmr_complex.cores[2].veer.sb_axi_arregion;
              8'd93: release el2_tmr_complex.cores[2].veer.sb_axi_arlen;
              8'd94: release el2_tmr_complex.cores[2].veer.sb_axi_arsize;
              8'd95: release el2_tmr_complex.cores[2].veer.sb_axi_arburst;
              8'd96: release el2_tmr_complex.cores[2].veer.sb_axi_arlock;
              8'd97: release el2_tmr_complex.cores[2].veer.sb_axi_arcache;
              8'd98: release el2_tmr_complex.cores[2].veer.sb_axi_arprot;
              8'd99: release el2_tmr_complex.cores[2].veer.sb_axi_arqos;
              8'd100: release el2_tmr_complex.cores[2].veer.sb_axi_rready;
              8'd101: release el2_tmr_complex.cores[2].veer.dma_axi_awready;
              8'd102: release el2_tmr_complex.cores[2].veer.dma_axi_wready;
              8'd103: release el2_tmr_complex.cores[2].veer.dma_axi_bvalid;
              8'd104: release el2_tmr_complex.cores[2].veer.dma_axi_bresp;
              8'd105: release el2_tmr_complex.cores[2].veer.dma_axi_bid;
              8'd106: release el2_tmr_complex.cores[2].veer.dma_axi_arready;
              8'd107: release el2_tmr_complex.cores[2].veer.dma_axi_rvalid;
              8'd108: release el2_tmr_complex.cores[2].veer.dma_axi_rid;
              8'd109: release el2_tmr_complex.cores[2].veer.dma_axi_rdata;
              8'd110: release el2_tmr_complex.cores[2].veer.dma_axi_rresp;
              8'd111: release el2_tmr_complex.cores[2].veer.dma_axi_rlast;
              8'd112: release el2_tmr_complex.cores[2].veer.iccm_ecc_single_error;
              8'd113: release el2_tmr_complex.cores[2].veer.iccm_ecc_double_error;
              8'd114: release el2_tmr_complex.cores[2].veer.dccm_ecc_single_error;
              8'd115: release el2_tmr_complex.cores[2].veer.dccm_ecc_double_error;
              default: begin end
            endcase
          2'd3: release el2_tmr_complex.tmr_output_inhibit;
          default: begin end
        endcase
      end
    end

    // TMR complex
    el2_tmr_complex #(.pt(pt)) el2_tmr_complex (
      .*,
      .mem_export    (mem_export.veer_sram_src),
      .icache_export (icache_export.veer_icache_src)
    );

endmodule
