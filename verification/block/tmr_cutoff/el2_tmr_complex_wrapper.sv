// Copyright 2026 Antmicro <www.antmicro.com>
// //
// // SPDX-License-Identifier: Apache-2.0
//

module el2_tmr_complex_wrapper
  import el2_pkg::*;
  import el2_mubi_pkg::*;
#(
    `include "el2_param.vh"
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
    output logic [pt.DCCM_NUM_BANKS-1:0][              pt.DCCM_DATA_WIDTH-1:0] mem_export_dccm_bank_dout,
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

    // ICCM/DCCM ECC status
    output logic                 iccm_ecc_single_error,
    output logic                 iccm_ecc_double_error,
    output logic                 dccm_ecc_single_error,
    output logic                 dccm_ecc_double_error,

    input logic [pt.PIC_TOTAL_INT:1]           extintsrc_req,
    input logic                   timer_int,
    input logic                   soft_int,
    // Excluding scan_mode from coverage as its usage is determined by the integrator of the VeeR core.
    /*pragma coverage off*/
    input logic                   scan_mode
    /*pragma coverage on*/
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
    assign mem_export_dccm_bank_dout                = mem_export.dccm_bank_dout;
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

    // TMR complex
    el2_tmr_complex #(.pt(pt)) el2_tmr_complex (
      .*,
      .mem_export    (mem_export.veer_sram_src),
      .icache_export (icache_export.veer_icache_src)
    );

endmodule
