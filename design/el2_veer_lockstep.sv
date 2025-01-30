// Copyright 2024 Antmicro <www.antmicro.com>
//
// SPDX-License-Identifier: Apache-2.0

module el2_veer_lockstep
  import el2_pkg::*;
#(
    `include "el2_param.vh"
) (
`ifdef RV_LOCKSTEP_REGFILE_ENABLE
    el2_regfile_if.veer_rf_sink main_core_regfile,
`endif

    input logic        clk,
    input logic        rst_l,
    input logic        dbg_rst_l,
    input logic [31:1] rst_vec,
    input logic        nmi_int,
    input logic [31:1] nmi_vec,
    input logic        core_rst_l, // This is "rst_l | dbg_rst_l"

    input logic active_l2clk,
    input logic free_l2clk,

    input logic [31:0] trace_rv_i_insn_ip,
    input logic [31:0] trace_rv_i_address_ip,
    input logic trace_rv_i_valid_ip,
    input logic trace_rv_i_exception_ip,
    input logic [4:0] trace_rv_i_ecause_ip,
    input logic trace_rv_i_interrupt_ip,
    input logic [31:0] trace_rv_i_tval_ip,


    input logic dccm_clk_override,
    input logic icm_clk_override,
    input logic dec_tlu_core_ecc_disable,

    // external halt/run interface
    input logic i_cpu_halt_req,  // Asynchronous Halt request to CPU
    input logic i_cpu_run_req,  // Asynchronous Restart request to CPU
    input logic o_cpu_halt_ack,  // Core Acknowledge to Halt request
    input logic o_cpu_halt_status,  // 1'b1 indicates processor is halted
    input logic o_cpu_run_ack,  // Core Acknowledge to run request
    input logic o_debug_mode_status, // Core to the PMU that core is in debug mode. When core is in debug mode, the PMU should refrain from sendng a halt or run request

    input logic [31:4] core_id,  // CORE ID

    // external MPC halt/run interface
    input logic mpc_debug_halt_req,  // Async halt request
    input logic mpc_debug_run_req,   // Async run request
    input logic mpc_reset_run_req,   // Run/halt after reset
    input logic mpc_debug_halt_ack,  // Halt ack
    input logic mpc_debug_run_ack,   // Run ack
    input logic debug_brkpt_status,  // debug breakpoint

    input logic dec_tlu_perfcnt0,  // toggles when slot0 perf counter 0 has an event inc
    input logic dec_tlu_perfcnt1,
    input logic dec_tlu_perfcnt2,
    input logic dec_tlu_perfcnt3,

    // DCCM ports
    input logic                           dccm_wren,
    input logic                           dccm_rden,
    input logic [       pt.DCCM_BITS-1:0] dccm_wr_addr_lo,
    input logic [       pt.DCCM_BITS-1:0] dccm_wr_addr_hi,
    input logic [       pt.DCCM_BITS-1:0] dccm_rd_addr_lo,
    input logic [       pt.DCCM_BITS-1:0] dccm_rd_addr_hi,
    input logic [pt.DCCM_FDATA_WIDTH-1:0] dccm_wr_data_lo,
    input logic [pt.DCCM_FDATA_WIDTH-1:0] dccm_wr_data_hi,

    input logic [pt.DCCM_FDATA_WIDTH-1:0] dccm_rd_data_lo,
    input logic [pt.DCCM_FDATA_WIDTH-1:0] dccm_rd_data_hi,

    // ICCM ports
    input logic [pt.ICCM_BITS-1:1] iccm_rw_addr,
    input logic                    iccm_wren,
    input logic                    iccm_rden,
    input logic [             2:0] iccm_wr_size,
    input logic [            77:0] iccm_wr_data,
    input logic                    iccm_buf_correct_ecc,
    input logic                    iccm_correction_state,

    input logic [63:0] iccm_rd_data,
    input logic [77:0] iccm_rd_data_ecc,

    // ICache , ITAG  ports
    input logic [                  31:1] ic_rw_addr,
    input logic [pt.ICACHE_NUM_WAYS-1:0] ic_tag_valid,
    input logic [pt.ICACHE_NUM_WAYS-1:0] ic_wr_en,
    input logic                          ic_rd_en,

    input logic [pt.ICACHE_BANKS_WAY-1:0][70:0] ic_wr_data,  // Data to fill to the Icache. With ECC
    input  logic [63:0]               ic_rd_data ,        // Data read from Icache. 2x64bits + parity bits. F2 stage. With ECC
    input  logic [70:0]               ic_debug_rd_data ,        // Data read from Icache. 2x64bits + parity bits. F2 stage. With ECC
    input logic [25:0] ictag_debug_rd_data,  // Debug icache tag.
    input logic [70:0] ic_debug_wr_data,  // Debug wr cache.

    input logic [pt.ICACHE_BANKS_WAY-1:0] ic_eccerr,
    input logic [pt.ICACHE_BANKS_WAY-1:0] ic_parerr,
    input logic [63:0] ic_premux_data,  // Premux data to be muxed with each way of the Icache.
    input logic ic_sel_premux_data,  // Select premux data


    input logic [  pt.ICACHE_INDEX_HI:3] ic_debug_addr,       // Read/Write addresss to the Icache.
    input logic                          ic_debug_rd_en,      // Icache debug rd
    input logic                          ic_debug_wr_en,      // Icache debug wr
    input logic                          ic_debug_tag_array,  // Debug tag array
    input logic [pt.ICACHE_NUM_WAYS-1:0] ic_debug_way,        // Debug way. Rd or Wr.


    input logic [pt.ICACHE_NUM_WAYS-1:0] ic_rd_hit,
    input logic                          ic_tag_perr, // Icache Tag parity error

    //-------------------------- LSU AXI signals--------------------------
    // AXI Write Channels
    input logic                      lsu_axi_awvalid,
    input logic                      lsu_axi_awready,
    input logic [pt.LSU_BUS_TAG-1:0] lsu_axi_awid,
    input logic [              31:0] lsu_axi_awaddr,
    input logic [               3:0] lsu_axi_awregion,
    input logic [               7:0] lsu_axi_awlen,
    input logic [               2:0] lsu_axi_awsize,
    input logic [               1:0] lsu_axi_awburst,
    input logic                      lsu_axi_awlock,
    input logic [               3:0] lsu_axi_awcache,
    input logic [               2:0] lsu_axi_awprot,
    input logic [               3:0] lsu_axi_awqos,

    input logic        lsu_axi_wvalid,
    input logic        lsu_axi_wready,
    input logic [63:0] lsu_axi_wdata,
    input logic [ 7:0] lsu_axi_wstrb,
    input logic        lsu_axi_wlast,

    input logic                      lsu_axi_bvalid,
    input logic                      lsu_axi_bready,
    input logic [               1:0] lsu_axi_bresp,
    input logic [pt.LSU_BUS_TAG-1:0] lsu_axi_bid,

    // AXI Read Channels
    input logic                      lsu_axi_arvalid,
    input logic                      lsu_axi_arready,
    input logic [pt.LSU_BUS_TAG-1:0] lsu_axi_arid,
    input logic [              31:0] lsu_axi_araddr,
    input logic [               3:0] lsu_axi_arregion,
    input logic [               7:0] lsu_axi_arlen,
    input logic [               2:0] lsu_axi_arsize,
    input logic [               1:0] lsu_axi_arburst,
    input logic                      lsu_axi_arlock,
    input logic [               3:0] lsu_axi_arcache,
    input logic [               2:0] lsu_axi_arprot,
    input logic [               3:0] lsu_axi_arqos,

    input logic                      lsu_axi_rvalid,
    input logic                      lsu_axi_rready,
    input logic [pt.LSU_BUS_TAG-1:0] lsu_axi_rid,
    input logic [              63:0] lsu_axi_rdata,
    input logic [               1:0] lsu_axi_rresp,
    input logic                      lsu_axi_rlast,

    //-------------------------- IFU AXI signals--------------------------
    // AXI Write Channels
    input logic                      ifu_axi_awvalid,
    input logic                      ifu_axi_awready,
    input logic [pt.IFU_BUS_TAG-1:0] ifu_axi_awid,
    input logic [              31:0] ifu_axi_awaddr,
    input logic [               3:0] ifu_axi_awregion,
    input logic [               7:0] ifu_axi_awlen,
    input logic [               2:0] ifu_axi_awsize,
    input logic [               1:0] ifu_axi_awburst,
    input logic                      ifu_axi_awlock,
    input logic [               3:0] ifu_axi_awcache,
    input logic [               2:0] ifu_axi_awprot,
    input logic [               3:0] ifu_axi_awqos,

    input logic        ifu_axi_wvalid,
    input logic        ifu_axi_wready,
    input logic [63:0] ifu_axi_wdata,
    input logic [ 7:0] ifu_axi_wstrb,
    input logic        ifu_axi_wlast,

    input logic                      ifu_axi_bvalid,
    input logic                      ifu_axi_bready,
    input logic [               1:0] ifu_axi_bresp,
    input logic [pt.IFU_BUS_TAG-1:0] ifu_axi_bid,

    // AXI Read Channels
    input logic                      ifu_axi_arvalid,
    input logic                      ifu_axi_arready,
    input logic [pt.IFU_BUS_TAG-1:0] ifu_axi_arid,
    input logic [              31:0] ifu_axi_araddr,
    input logic [               3:0] ifu_axi_arregion,
    input logic [               7:0] ifu_axi_arlen,
    input logic [               2:0] ifu_axi_arsize,
    input logic [               1:0] ifu_axi_arburst,
    input logic                      ifu_axi_arlock,
    input logic [               3:0] ifu_axi_arcache,
    input logic [               2:0] ifu_axi_arprot,
    input logic [               3:0] ifu_axi_arqos,

    input logic                      ifu_axi_rvalid,
    input logic                      ifu_axi_rready,
    input logic [pt.IFU_BUS_TAG-1:0] ifu_axi_rid,
    input logic [              63:0] ifu_axi_rdata,
    input logic [               1:0] ifu_axi_rresp,
    input logic                      ifu_axi_rlast,

    //-------------------------- SB AXI signals--------------------------
    // AXI Write Channels
    input logic                     sb_axi_awvalid,
    input logic                     sb_axi_awready,
    input logic [pt.SB_BUS_TAG-1:0] sb_axi_awid,
    input logic [             31:0] sb_axi_awaddr,
    input logic [              3:0] sb_axi_awregion,
    input logic [              7:0] sb_axi_awlen,
    input logic [              2:0] sb_axi_awsize,
    input logic [              1:0] sb_axi_awburst,
    input logic                     sb_axi_awlock,
    input logic [              3:0] sb_axi_awcache,
    input logic [              2:0] sb_axi_awprot,
    input logic [              3:0] sb_axi_awqos,

    input logic        sb_axi_wvalid,
    input logic        sb_axi_wready,
    input logic [63:0] sb_axi_wdata,
    input logic [ 7:0] sb_axi_wstrb,
    input logic        sb_axi_wlast,

    input logic                     sb_axi_bvalid,
    input logic                     sb_axi_bready,
    input logic [              1:0] sb_axi_bresp,
    input logic [pt.SB_BUS_TAG-1:0] sb_axi_bid,

    // AXI Read Channels
    input logic                     sb_axi_arvalid,
    input logic                     sb_axi_arready,
    input logic [pt.SB_BUS_TAG-1:0] sb_axi_arid,
    input logic [             31:0] sb_axi_araddr,
    input logic [              3:0] sb_axi_arregion,
    input logic [              7:0] sb_axi_arlen,
    input logic [              2:0] sb_axi_arsize,
    input logic [              1:0] sb_axi_arburst,
    input logic                     sb_axi_arlock,
    input logic [              3:0] sb_axi_arcache,
    input logic [              2:0] sb_axi_arprot,
    input logic [              3:0] sb_axi_arqos,

    input logic                     sb_axi_rvalid,
    input logic                     sb_axi_rready,
    input logic [pt.SB_BUS_TAG-1:0] sb_axi_rid,
    input logic [             63:0] sb_axi_rdata,
    input logic [              1:0] sb_axi_rresp,
    input logic                     sb_axi_rlast,

    //-------------------------- DMA AXI signals--------------------------
    // AXI Write Channels
    input logic                      dma_axi_awvalid,
    input logic                      dma_axi_awready,
    input logic [pt.DMA_BUS_TAG-1:0] dma_axi_awid,
    input logic [              31:0] dma_axi_awaddr,
    input logic [               2:0] dma_axi_awsize,
    input logic [               2:0] dma_axi_awprot,
    input logic [               7:0] dma_axi_awlen,
    input logic [               1:0] dma_axi_awburst,


    input logic        dma_axi_wvalid,
    input logic        dma_axi_wready,
    input logic [63:0] dma_axi_wdata,
    input logic [ 7:0] dma_axi_wstrb,
    input logic        dma_axi_wlast,

    input logic                      dma_axi_bvalid,
    input logic                      dma_axi_bready,
    input logic [               1:0] dma_axi_bresp,
    input logic [pt.DMA_BUS_TAG-1:0] dma_axi_bid,

    // AXI Read Channels
    input logic                      dma_axi_arvalid,
    input logic                      dma_axi_arready,
    input logic [pt.DMA_BUS_TAG-1:0] dma_axi_arid,
    input logic [              31:0] dma_axi_araddr,
    input logic [               2:0] dma_axi_arsize,
    input logic [               2:0] dma_axi_arprot,
    input logic [               7:0] dma_axi_arlen,
    input logic [               1:0] dma_axi_arburst,

    input logic                      dma_axi_rvalid,
    input logic                      dma_axi_rready,
    input logic [pt.DMA_BUS_TAG-1:0] dma_axi_rid,
    input logic [              63:0] dma_axi_rdata,
    input logic [               1:0] dma_axi_rresp,
    input logic                      dma_axi_rlast,


    //// AHB LITE BUS
    input logic [31:0] haddr,
    input logic [ 2:0] hburst,
    input logic        hmastlock,
    input logic [ 3:0] hprot,
    input logic [ 2:0] hsize,
    input logic [ 1:0] htrans,
    input logic        hwrite,

    input logic [63:0] hrdata,
    input logic        hready,
    input logic        hresp,

    // LSU AHB Master
    input logic [31:0] lsu_haddr,
    input logic [ 2:0] lsu_hburst,
    input logic        lsu_hmastlock,
    input logic [ 3:0] lsu_hprot,
    input logic [ 2:0] lsu_hsize,
    input logic [ 1:0] lsu_htrans,
    input logic        lsu_hwrite,
    input logic [63:0] lsu_hwdata,

    input logic [63:0] lsu_hrdata,
    input logic        lsu_hready,
    input logic        lsu_hresp,

    //System Bus Debug Master
    input logic [31:0] sb_haddr,
    input logic [ 2:0] sb_hburst,
    input logic        sb_hmastlock,
    input logic [ 3:0] sb_hprot,
    input logic [ 2:0] sb_hsize,
    input logic [ 1:0] sb_htrans,
    input logic        sb_hwrite,
    input logic [63:0] sb_hwdata,

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

    input logic [63:0] dma_hrdata,
    input logic        dma_hreadyout,
    input logic        dma_hresp,

    input logic lsu_bus_clk_en,
    input logic ifu_bus_clk_en,
    input logic dbg_bus_clk_en,
    input logic dma_bus_clk_en,

    input logic        dmi_reg_en,     // read or write
    input logic [ 6:0] dmi_reg_addr,   // address of DM register
    input logic        dmi_reg_wr_en,  // write instruction
    input logic [31:0] dmi_reg_wdata,  // write data
    input logic [31:0] dmi_reg_rdata,

    // ICCM/DCCM ECC status
    input logic iccm_ecc_single_error,
    input logic iccm_ecc_double_error,
    input logic dccm_ecc_single_error,
    input logic dccm_ecc_double_error,

    input logic [pt.PIC_TOTAL_INT:1] extintsrc_req,
    input logic                      timer_int,
    input logic                      soft_int,
    input logic                      scan_mode,

    // Shadow Core control
    input logic disable_corruption_detection_i,
    input logic lockstep_err_injection_en_i,

    // Equivalency Checker output
    output logic corruption_detected_o
);

  localparam int unsigned LockstepDelay = pt.LOCKSTEP_DELAY;  // Delay I/O; in clock cycles

  // Outputs
  typedef struct packed {
    logic                                 core_rst_l;
    logic [31:0]                          trace_rv_i_insn_ip;
    logic [31:0]                          trace_rv_i_address_ip;
    logic                                 trace_rv_i_valid_ip;
    logic                                 trace_rv_i_exception_ip;
    logic [4:0]                           trace_rv_i_ecause_ip;
    logic                                 trace_rv_i_interrupt_ip;
    logic [31:0]                          trace_rv_i_tval_ip;
    logic                                 dccm_clk_override;
    logic                                 icm_clk_override;
    logic                                 dec_tlu_core_ecc_disable;
    logic                                 o_cpu_halt_ack;
    logic                                 o_cpu_halt_status;
    logic                                 o_cpu_run_ack;
    logic                                 o_debug_mode_status;
    logic                                 mpc_debug_halt_ack;
    logic                                 mpc_debug_run_ack;
    logic                                 debug_brkpt_status;
    logic                                 dec_tlu_perfcnt0;
    logic                                 dec_tlu_perfcnt1;
    logic                                 dec_tlu_perfcnt2;
    logic                                 dec_tlu_perfcnt3;
    logic                                 dccm_wren;
    logic                                 dccm_rden;
    logic [pt.DCCM_BITS-1:0]              dccm_wr_addr_lo;
    logic [pt.DCCM_BITS-1:0]              dccm_wr_addr_hi;
    logic [pt.DCCM_BITS-1:0]              dccm_rd_addr_lo;
    logic [pt.DCCM_BITS-1:0]              dccm_rd_addr_hi;
    logic [pt.DCCM_FDATA_WIDTH-1:0]       dccm_wr_data_lo;
    logic [pt.DCCM_FDATA_WIDTH-1:0]       dccm_wr_data_hi;
    logic [pt.ICCM_BITS-1:1]              iccm_rw_addr;
    logic                                 iccm_wren;
    logic                                 iccm_rden;
    logic [2:0]                           iccm_wr_size;
    logic [77:0]                          iccm_wr_data;
    logic                                 iccm_buf_correct_ecc;
    logic                                 iccm_correction_state;
    logic [31:1]                          ic_rw_addr;
    logic [pt.ICACHE_NUM_WAYS-1:0]        ic_tag_valid;
    logic [pt.ICACHE_NUM_WAYS-1:0]        ic_wr_en;
    logic                                 ic_rd_en;
    logic [pt.ICACHE_BANKS_WAY-1:0][70:0] ic_wr_data;
    logic [70:0]                          ic_debug_wr_data;
    logic [63:0]                          ic_premux_data;
    logic                                 ic_sel_premux_data;
    logic [pt.ICACHE_INDEX_HI:3]          ic_debug_addr;
    logic                                 ic_debug_rd_en;
    logic                                 ic_debug_wr_en;
    logic                                 ic_debug_tag_array;
    logic [pt.ICACHE_NUM_WAYS-1:0]        ic_debug_way;
    logic                                 lsu_axi_awvalid;
    logic [pt.LSU_BUS_TAG-1:0]            lsu_axi_awid;
    logic [31:0]                          lsu_axi_awaddr;
    logic [3:0]                           lsu_axi_awregion;
    logic [7:0]                           lsu_axi_awlen;
    logic [2:0]                           lsu_axi_awsize;
    logic [1:0]                           lsu_axi_awburst;
    logic                                 lsu_axi_awlock;
    logic [3:0]                           lsu_axi_awcache;
    logic [2:0]                           lsu_axi_awprot;
    logic [3:0]                           lsu_axi_awqos;
    logic                                 lsu_axi_wvalid;
    logic [63:0]                          lsu_axi_wdata;
    logic [7:0]                           lsu_axi_wstrb;
    logic                                 lsu_axi_wlast;
    logic                                 lsu_axi_bready;
    logic                                 lsu_axi_arvalid;
    logic [pt.LSU_BUS_TAG-1:0]            lsu_axi_arid;
    logic [31:0]                          lsu_axi_araddr;
    logic [3:0]                           lsu_axi_arregion;
    logic [7:0]                           lsu_axi_arlen;
    logic [2:0]                           lsu_axi_arsize;
    logic [1:0]                           lsu_axi_arburst;
    logic                                 lsu_axi_arlock;
    logic [3:0]                           lsu_axi_arcache;
    logic [2:0]                           lsu_axi_arprot;
    logic [3:0]                           lsu_axi_arqos;
    logic                                 lsu_axi_rready;
    logic                                 ifu_axi_awvalid;
    logic [pt.IFU_BUS_TAG-1:0]            ifu_axi_awid;
    logic [31:0]                          ifu_axi_awaddr;
    logic [3:0]                           ifu_axi_awregion;
    logic [7:0]                           ifu_axi_awlen;
    logic [2:0]                           ifu_axi_awsize;
    logic [1:0]                           ifu_axi_awburst;
    logic                                 ifu_axi_awlock;
    logic [3:0]                           ifu_axi_awcache;
    logic [2:0]                           ifu_axi_awprot;
    logic [3:0]                           ifu_axi_awqos;
    logic                                 ifu_axi_wvalid;
    logic [63:0]                          ifu_axi_wdata;
    logic [7:0]                           ifu_axi_wstrb;
    logic                                 ifu_axi_wlast;
    logic                                 ifu_axi_bready;
    logic                                 ifu_axi_arvalid;
    logic [pt.IFU_BUS_TAG-1:0]            ifu_axi_arid;
    logic [31:0]                          ifu_axi_araddr;
    logic [3:0]                           ifu_axi_arregion;
    logic [7:0]                           ifu_axi_arlen;
    logic [2:0]                           ifu_axi_arsize;
    logic [1:0]                           ifu_axi_arburst;
    logic                                 ifu_axi_arlock;
    logic [3:0]                           ifu_axi_arcache;
    logic [2:0]                           ifu_axi_arprot;
    logic [3:0]                           ifu_axi_arqos;
    logic                                 ifu_axi_rready;
    logic                                 sb_axi_awvalid;
    logic [pt.SB_BUS_TAG-1:0]             sb_axi_awid;
    logic [31:0]                          sb_axi_awaddr;
    logic [3:0]                           sb_axi_awregion;
    logic [7:0]                           sb_axi_awlen;
    logic [2:0]                           sb_axi_awsize;
    logic [1:0]                           sb_axi_awburst;
    logic                                 sb_axi_awlock;
    logic [3:0]                           sb_axi_awcache;
    logic [2:0]                           sb_axi_awprot;
    logic [3:0]                           sb_axi_awqos;
    logic                                 sb_axi_wvalid;
    logic [63:0]                          sb_axi_wdata;
    logic [7:0]                           sb_axi_wstrb;
    logic                                 sb_axi_wlast;
    logic                                 sb_axi_bready;
    logic                                 sb_axi_arvalid;
    logic [pt.SB_BUS_TAG-1:0]             sb_axi_arid;
    logic [31:0]                          sb_axi_araddr;
    logic [3:0]                           sb_axi_arregion;
    logic [7:0]                           sb_axi_arlen;
    logic [2:0]                           sb_axi_arsize;
    logic [1:0]                           sb_axi_arburst;
    logic                                 sb_axi_arlock;
    logic [3:0]                           sb_axi_arcache;
    logic [2:0]                           sb_axi_arprot;
    logic [3:0]                           sb_axi_arqos;
    logic                                 sb_axi_rready;
    logic                                 dma_axi_awready;
    logic                                 dma_axi_wready;
    logic                                 dma_axi_bvalid;
    logic [1:0]                           dma_axi_bresp;
    logic [pt.DMA_BUS_TAG-1:0]            dma_axi_bid;
    logic                                 dma_axi_arready;
    logic                                 dma_axi_rvalid;
    logic [pt.DMA_BUS_TAG-1:0]            dma_axi_rid;
    logic [63:0]                          dma_axi_rdata;
    logic [1:0]                           dma_axi_rresp;
    logic                                 dma_axi_rlast;
    logic [31:0]                          haddr;
    logic [2:0]                           hburst;
    logic                                 hmastlock;
    logic [3:0]                           hprot;
    logic [2:0]                           hsize;
    logic [1:0]                           htrans;
    logic                                 hwrite;
    logic [31:0]                          lsu_haddr;
    logic [2:0]                           lsu_hburst;
    logic                                 lsu_hmastlock;
    logic [3:0]                           lsu_hprot;
    logic [2:0]                           lsu_hsize;
    logic [1:0]                           lsu_htrans;
    logic                                 lsu_hwrite;
    logic [63:0]                          lsu_hwdata;
    logic [31:0]                          sb_haddr;
    logic [2:0]                           sb_hburst;
    logic                                 sb_hmastlock;
    logic [3:0]                           sb_hprot;
    logic [2:0]                           sb_hsize;
    logic [1:0]                           sb_htrans;
    logic                                 sb_hwrite;
    logic [63:0]                          sb_hwdata;
    logic [63:0]                          dma_hrdata;
    logic                                 dma_hreadyout;
    logic                                 dma_hresp;
    logic [31:0]                          dmi_reg_rdata;
    logic                                 iccm_ecc_single_error;
    logic                                 iccm_ecc_double_error;
    logic                                 dccm_ecc_single_error;
    logic                                 dccm_ecc_double_error;
  } veer_outputs_t;

  // Inputs
  typedef struct packed {
    logic [31:1]                    rst_vec;
    logic                           nmi_int;
    logic [31:1]                    nmi_vec;
    logic                           i_cpu_halt_req;
    logic                           i_cpu_run_req;
    logic [31:4]                    core_id;
    logic                           mpc_debug_halt_req;
    logic                           mpc_debug_run_req;
    logic                           mpc_reset_run_req;
    logic [pt.DCCM_FDATA_WIDTH-1:0] dccm_rd_data_lo;
    logic [pt.DCCM_FDATA_WIDTH-1:0] dccm_rd_data_hi;
    logic [63:0]                    iccm_rd_data;
    logic [77:0]                    iccm_rd_data_ecc;
    logic [63:0]                    ic_rd_data;
    logic [70:0]                    ic_debug_rd_data;
    logic [25:0]                    ictag_debug_rd_data;
    logic [pt.ICACHE_BANKS_WAY-1:0] ic_eccerr;
    logic [pt.ICACHE_BANKS_WAY-1:0] ic_parerr;
    logic [pt.ICACHE_NUM_WAYS-1:0]  ic_rd_hit;
    logic                           ic_tag_perr;
    logic                           lsu_axi_awready;
    logic                           lsu_axi_wready;
    logic                           lsu_axi_bvalid;
    logic [1:0]                     lsu_axi_bresp;
    logic [pt.LSU_BUS_TAG-1:0]      lsu_axi_bid;
    logic                           lsu_axi_arready;
    logic                           lsu_axi_rvalid;
    logic [pt.LSU_BUS_TAG-1:0]      lsu_axi_rid;
    logic [63:0]                    lsu_axi_rdata;
    logic [1:0]                     lsu_axi_rresp;
    logic                           lsu_axi_rlast;
    logic                           ifu_axi_awready;
    logic                           ifu_axi_wready;
    logic                           ifu_axi_bvalid;
    logic [1:0]                     ifu_axi_bresp;
    logic [pt.IFU_BUS_TAG-1:0]      ifu_axi_bid;
    logic                           ifu_axi_arready;
    logic                           ifu_axi_rvalid;
    logic [pt.IFU_BUS_TAG-1:0]      ifu_axi_rid;
    logic [63:0]                    ifu_axi_rdata;
    logic [1:0]                     ifu_axi_rresp;
    logic                           ifu_axi_rlast;
    logic                           sb_axi_awready;
    logic                           sb_axi_wready;
    logic                           sb_axi_bvalid;
    logic [1:0]                     sb_axi_bresp;
    logic [pt.SB_BUS_TAG-1:0]       sb_axi_bid;
    logic                           sb_axi_arready;
    logic                           sb_axi_rvalid;
    logic [pt.SB_BUS_TAG-1:0]       sb_axi_rid;
    logic [63:0]                    sb_axi_rdata;
    logic [1:0]                     sb_axi_rresp;
    logic                           sb_axi_rlast;
    logic                           dma_axi_awvalid;
    logic [pt.DMA_BUS_TAG-1:0]      dma_axi_awid;
    logic [31:0]                    dma_axi_awaddr;
    logic [2:0]                     dma_axi_awsize;
    logic [2:0]                     dma_axi_awprot;
    logic [7:0]                     dma_axi_awlen;
    logic [1:0]                     dma_axi_awburst;
    logic                           dma_axi_wvalid;
    logic [63:0]                    dma_axi_wdata;
    logic [7:0]                     dma_axi_wstrb;
    logic                           dma_axi_wlast;
    logic                           dma_axi_bready;
    logic                           dma_axi_arvalid;
    logic [pt.DMA_BUS_TAG-1:0]      dma_axi_arid;
    logic [31:0]                    dma_axi_araddr;
    logic [2:0]                     dma_axi_arsize;
    logic [2:0]                     dma_axi_arprot;
    logic [7:0]                     dma_axi_arlen;
    logic [1:0]                     dma_axi_arburst;
    logic                           dma_axi_rready;
    logic [63:0]                    hrdata;
    logic                           hready;
    logic                           hresp;
    logic [63:0]                    lsu_hrdata;
    logic                           lsu_hready;
    logic                           lsu_hresp;
    logic [63:0]                    sb_hrdata;
    logic                           sb_hready;
    logic                           sb_hresp;
    logic                           dma_hsel;
    logic [31:0]                    dma_haddr;
    logic [2:0]                     dma_hburst;
    logic                           dma_hmastlock;
    logic [3:0]                     dma_hprot;
    logic [2:0]                     dma_hsize;
    logic [1:0]                     dma_htrans;
    logic                           dma_hwrite;
    logic [63:0]                    dma_hwdata;
    logic                           dma_hreadyin;
    logic                           lsu_bus_clk_en;
    logic                           ifu_bus_clk_en;
    logic                           dbg_bus_clk_en;
    logic                           dma_bus_clk_en;
    logic                           dmi_reg_en;
    logic [6:0]                     dmi_reg_addr;
    logic                           dmi_reg_wr_en;
    logic [31:0]                    dmi_reg_wdata;
    logic [pt.PIC_TOTAL_INT:1]      extintsrc_req;
    logic                           timer_int;
    logic                           soft_int;
    logic                           scan_mode;
  } veer_inputs_t;

  veer_inputs_t main_core_inputs;
  veer_inputs_t [LockstepDelay:0] delay_input_d;
  veer_inputs_t shadow_core_inputs;

  veer_outputs_t main_core_outputs;
  veer_outputs_t [LockstepDelay:0] delay_output_d;
  veer_outputs_t delayed_main_core_outputs;
  veer_outputs_t shadow_core_outputs;

  assign shadow_core_inputs = delay_input_d[LockstepDelay];
  assign delayed_main_core_outputs = delay_output_d[LockstepDelay];

  // Capture input
  assign main_core_inputs.rst_vec = rst_vec;
  assign main_core_inputs.nmi_int = nmi_int;
  assign main_core_inputs.nmi_vec = nmi_vec;
  assign main_core_inputs.i_cpu_halt_req = i_cpu_halt_req;
  assign main_core_inputs.i_cpu_run_req = i_cpu_run_req;
  assign main_core_inputs.core_id = core_id;
  assign main_core_inputs.mpc_debug_halt_req = mpc_debug_halt_req;
  assign main_core_inputs.mpc_debug_run_req = mpc_debug_run_req;
  assign main_core_inputs.mpc_reset_run_req = mpc_reset_run_req;
  assign main_core_inputs.dccm_rd_data_lo = dccm_rd_data_lo;
  assign main_core_inputs.dccm_rd_data_hi = dccm_rd_data_hi;
  assign main_core_inputs.iccm_rd_data = iccm_rd_data;
  assign main_core_inputs.iccm_rd_data_ecc = iccm_rd_data_ecc;
  assign main_core_inputs.ic_rd_data = ic_rd_data;
  assign main_core_inputs.ic_debug_rd_data = ic_debug_rd_data;
  assign main_core_inputs.ictag_debug_rd_data = ictag_debug_rd_data;
  assign main_core_inputs.ic_eccerr = ic_eccerr;
  assign main_core_inputs.ic_parerr = ic_parerr;
  assign main_core_inputs.ic_rd_hit = ic_rd_hit;
  assign main_core_inputs.ic_tag_perr = ic_tag_perr;
  assign main_core_inputs.lsu_axi_awready = lsu_axi_awready;
  assign main_core_inputs.lsu_axi_wready = lsu_axi_wready;
  assign main_core_inputs.lsu_axi_bvalid = lsu_axi_bvalid;
  assign main_core_inputs.lsu_axi_bresp = lsu_axi_bresp;
  assign main_core_inputs.lsu_axi_bid = lsu_axi_bid;
  assign main_core_inputs.lsu_axi_arready = lsu_axi_arready;
  assign main_core_inputs.lsu_axi_rvalid = lsu_axi_rvalid;
  assign main_core_inputs.lsu_axi_rid = lsu_axi_rid;
  assign main_core_inputs.lsu_axi_rdata = lsu_axi_rdata;
  assign main_core_inputs.lsu_axi_rresp = lsu_axi_rresp;
  assign main_core_inputs.lsu_axi_rlast = lsu_axi_rlast;
  assign main_core_inputs.ifu_axi_awready = ifu_axi_awready;
  assign main_core_inputs.ifu_axi_wready = ifu_axi_wready;
  assign main_core_inputs.ifu_axi_bvalid = ifu_axi_bvalid;
  assign main_core_inputs.ifu_axi_bresp = ifu_axi_bresp;
  assign main_core_inputs.ifu_axi_bid = ifu_axi_bid;
  assign main_core_inputs.ifu_axi_arready = ifu_axi_arready;
  assign main_core_inputs.ifu_axi_rvalid = ifu_axi_rvalid;
  assign main_core_inputs.ifu_axi_rid = ifu_axi_rid;
  assign main_core_inputs.ifu_axi_rdata = ifu_axi_rdata;
  assign main_core_inputs.ifu_axi_rresp = ifu_axi_rresp;
  assign main_core_inputs.ifu_axi_rlast = ifu_axi_rlast;
  assign main_core_inputs.sb_axi_awready = sb_axi_awready;
  assign main_core_inputs.sb_axi_wready = sb_axi_wready;
  assign main_core_inputs.sb_axi_bvalid = sb_axi_bvalid;
  assign main_core_inputs.sb_axi_bresp = sb_axi_bresp;
  assign main_core_inputs.sb_axi_bid = sb_axi_bid;
  assign main_core_inputs.sb_axi_arready = sb_axi_arready;
  assign main_core_inputs.sb_axi_rvalid = sb_axi_rvalid;
  assign main_core_inputs.sb_axi_rid = sb_axi_rid;
  assign main_core_inputs.sb_axi_rdata = sb_axi_rdata;
  assign main_core_inputs.sb_axi_rresp = sb_axi_rresp;
  assign main_core_inputs.sb_axi_rlast = sb_axi_rlast;
  assign main_core_inputs.dma_axi_awvalid = dma_axi_awvalid;
  assign main_core_inputs.dma_axi_awid = dma_axi_awid;
  assign main_core_inputs.dma_axi_awaddr = dma_axi_awaddr;
  assign main_core_inputs.dma_axi_awsize = dma_axi_awsize;
  assign main_core_inputs.dma_axi_awprot = dma_axi_awprot;
  assign main_core_inputs.dma_axi_awlen = dma_axi_awlen;
  assign main_core_inputs.dma_axi_awburst = dma_axi_awburst;
  assign main_core_inputs.dma_axi_wvalid = dma_axi_wvalid;
  assign main_core_inputs.dma_axi_wdata = dma_axi_wdata;
  assign main_core_inputs.dma_axi_wstrb = dma_axi_wstrb;
  assign main_core_inputs.dma_axi_wlast = dma_axi_wlast;
  assign main_core_inputs.dma_axi_bready = dma_axi_bready;
  assign main_core_inputs.dma_axi_arvalid = dma_axi_arvalid;
  assign main_core_inputs.dma_axi_arid = dma_axi_arid;
  assign main_core_inputs.dma_axi_araddr = dma_axi_araddr;
  assign main_core_inputs.dma_axi_arsize = dma_axi_arsize;
  assign main_core_inputs.dma_axi_arprot = dma_axi_arprot;
  assign main_core_inputs.dma_axi_arlen = dma_axi_arlen;
  assign main_core_inputs.dma_axi_arburst = dma_axi_arburst;
  assign main_core_inputs.dma_axi_rready = dma_axi_rready;
  assign main_core_inputs.hrdata = hrdata;
  assign main_core_inputs.hready = hready;
  assign main_core_inputs.hresp = hresp;
  assign main_core_inputs.lsu_hrdata = lsu_hrdata;
  assign main_core_inputs.lsu_hready = lsu_hready;
  assign main_core_inputs.lsu_hresp = lsu_hresp;
  assign main_core_inputs.sb_hrdata = sb_hrdata;
  assign main_core_inputs.sb_hready = sb_hready;
  assign main_core_inputs.sb_hresp = sb_hresp;
  assign main_core_inputs.dma_hsel = dma_hsel;
  assign main_core_inputs.dma_haddr = dma_haddr;
  assign main_core_inputs.dma_hburst = dma_hburst;
  assign main_core_inputs.dma_hmastlock = dma_hmastlock;
  assign main_core_inputs.dma_hprot = dma_hprot;
  assign main_core_inputs.dma_hsize = dma_hsize;
  assign main_core_inputs.dma_htrans = dma_htrans;
  assign main_core_inputs.dma_hwrite = dma_hwrite;
  assign main_core_inputs.dma_hwdata = dma_hwdata;
  assign main_core_inputs.dma_hreadyin = dma_hreadyin;
  assign main_core_inputs.lsu_bus_clk_en = lsu_bus_clk_en;
  assign main_core_inputs.ifu_bus_clk_en = ifu_bus_clk_en;
  assign main_core_inputs.dbg_bus_clk_en = dbg_bus_clk_en;
  assign main_core_inputs.dma_bus_clk_en = dma_bus_clk_en;
  assign main_core_inputs.dmi_reg_en = dmi_reg_en;
  assign main_core_inputs.dmi_reg_addr = dmi_reg_addr;
  assign main_core_inputs.dmi_reg_wr_en = dmi_reg_wr_en;
  assign main_core_inputs.dmi_reg_wdata = dmi_reg_wdata;
  assign main_core_inputs.extintsrc_req = extintsrc_req;
  assign main_core_inputs.timer_int = timer_int;
  assign main_core_inputs.soft_int = soft_int;
  assign main_core_inputs.scan_mode = scan_mode;

  // Capture output
  assign main_core_outputs.core_rst_l = core_rst_l;
  assign main_core_outputs.trace_rv_i_insn_ip = trace_rv_i_insn_ip;
  assign main_core_outputs.trace_rv_i_address_ip = trace_rv_i_address_ip;
  assign main_core_outputs.trace_rv_i_valid_ip = trace_rv_i_valid_ip;
  assign main_core_outputs.trace_rv_i_exception_ip = trace_rv_i_exception_ip;
  assign main_core_outputs.trace_rv_i_ecause_ip = trace_rv_i_ecause_ip;
  assign main_core_outputs.trace_rv_i_interrupt_ip = trace_rv_i_interrupt_ip;
  assign main_core_outputs.trace_rv_i_tval_ip = trace_rv_i_tval_ip;
  assign main_core_outputs.dccm_clk_override = dccm_clk_override;
  assign main_core_outputs.icm_clk_override = icm_clk_override;
  assign main_core_outputs.dec_tlu_core_ecc_disable = dec_tlu_core_ecc_disable;
  assign main_core_outputs.o_cpu_halt_ack = o_cpu_halt_ack;
  assign main_core_outputs.o_cpu_halt_status = o_cpu_halt_status;
  assign main_core_outputs.o_cpu_run_ack = o_cpu_run_ack;
  assign main_core_outputs.o_debug_mode_status = o_debug_mode_status;
  assign main_core_outputs.mpc_debug_halt_ack = mpc_debug_halt_ack;
  assign main_core_outputs.mpc_debug_run_ack = mpc_debug_run_ack;
  assign main_core_outputs.debug_brkpt_status = debug_brkpt_status;
  assign main_core_outputs.dec_tlu_perfcnt0 = dec_tlu_perfcnt0;
  assign main_core_outputs.dec_tlu_perfcnt1 = dec_tlu_perfcnt1;
  assign main_core_outputs.dec_tlu_perfcnt2 = dec_tlu_perfcnt2;
  assign main_core_outputs.dec_tlu_perfcnt3 = dec_tlu_perfcnt3;
  assign main_core_outputs.dccm_wren = dccm_wren;
  assign main_core_outputs.dccm_rden = dccm_rden;
  assign main_core_outputs.dccm_wr_addr_lo = dccm_wr_addr_lo;
  assign main_core_outputs.dccm_wr_addr_hi = dccm_wr_addr_hi;
  assign main_core_outputs.dccm_rd_addr_lo = dccm_rd_addr_lo;
  assign main_core_outputs.dccm_rd_addr_hi = dccm_rd_addr_hi;
  assign main_core_outputs.dccm_wr_data_lo = dccm_wr_data_lo;
  assign main_core_outputs.dccm_wr_data_hi = dccm_wr_data_hi;
  assign main_core_outputs.iccm_rw_addr = iccm_rw_addr;
  assign main_core_outputs.iccm_wren = iccm_wren;
  assign main_core_outputs.iccm_rden = iccm_rden;
  assign main_core_outputs.iccm_wr_size = iccm_wr_size;
  assign main_core_outputs.iccm_wr_data = iccm_wr_data;
  assign main_core_outputs.iccm_buf_correct_ecc = iccm_buf_correct_ecc;
  assign main_core_outputs.iccm_correction_state = iccm_correction_state;
  assign main_core_outputs.ic_rw_addr = ic_rw_addr;
  assign main_core_outputs.ic_tag_valid = ic_tag_valid;
  assign main_core_outputs.ic_wr_en = ic_wr_en;
  assign main_core_outputs.ic_rd_en = ic_rd_en;
  assign main_core_outputs.ic_wr_data = ic_wr_data;
  assign main_core_outputs.ic_debug_wr_data = ic_debug_wr_data;
  assign main_core_outputs.ic_premux_data = ic_premux_data;
  assign main_core_outputs.ic_sel_premux_data = ic_sel_premux_data;
  assign main_core_outputs.ic_debug_addr = ic_debug_addr;
  assign main_core_outputs.ic_debug_rd_en = ic_debug_rd_en;
  assign main_core_outputs.ic_debug_wr_en = ic_debug_wr_en;
  assign main_core_outputs.ic_debug_tag_array = ic_debug_tag_array;
  assign main_core_outputs.ic_debug_way = ic_debug_way;
  assign main_core_outputs.lsu_axi_awvalid = lsu_axi_awvalid;
  assign main_core_outputs.lsu_axi_awid = lsu_axi_awid;
  assign main_core_outputs.lsu_axi_awaddr = lsu_axi_awaddr;
  assign main_core_outputs.lsu_axi_awregion = lsu_axi_awregion;
  assign main_core_outputs.lsu_axi_awlen = lsu_axi_awlen;
  assign main_core_outputs.lsu_axi_awsize = lsu_axi_awsize;
  assign main_core_outputs.lsu_axi_awburst = lsu_axi_awburst;
  assign main_core_outputs.lsu_axi_awlock = lsu_axi_awlock;
  assign main_core_outputs.lsu_axi_awcache = lsu_axi_awcache;
  assign main_core_outputs.lsu_axi_awprot = lsu_axi_awprot;
  assign main_core_outputs.lsu_axi_awqos = lsu_axi_awqos;
  assign main_core_outputs.lsu_axi_wvalid = lsu_axi_wvalid;
  assign main_core_outputs.lsu_axi_wdata = lsu_axi_wdata;
  assign main_core_outputs.lsu_axi_wstrb = lsu_axi_wstrb;
  assign main_core_outputs.lsu_axi_wlast = lsu_axi_wlast;
  assign main_core_outputs.lsu_axi_bready = lsu_axi_bready;
  assign main_core_outputs.lsu_axi_arvalid = lsu_axi_arvalid;
  assign main_core_outputs.lsu_axi_arid = lsu_axi_arid;
  assign main_core_outputs.lsu_axi_araddr = lsu_axi_araddr;
  assign main_core_outputs.lsu_axi_arregion = lsu_axi_arregion;
  assign main_core_outputs.lsu_axi_arlen = lsu_axi_arlen;
  assign main_core_outputs.lsu_axi_arsize = lsu_axi_arsize;
  assign main_core_outputs.lsu_axi_arburst = lsu_axi_arburst;
  assign main_core_outputs.lsu_axi_arlock = lsu_axi_arlock;
  assign main_core_outputs.lsu_axi_arcache = lsu_axi_arcache;
  assign main_core_outputs.lsu_axi_arprot = lsu_axi_arprot;
  assign main_core_outputs.lsu_axi_arqos = lsu_axi_arqos;
  assign main_core_outputs.lsu_axi_rready = lsu_axi_rready;
  assign main_core_outputs.ifu_axi_awvalid = ifu_axi_awvalid;
  assign main_core_outputs.ifu_axi_awid = ifu_axi_awid;
  assign main_core_outputs.ifu_axi_awaddr = ifu_axi_awaddr;
  assign main_core_outputs.ifu_axi_awregion = ifu_axi_awregion;
  assign main_core_outputs.ifu_axi_awlen = ifu_axi_awlen;
  assign main_core_outputs.ifu_axi_awsize = ifu_axi_awsize;
  assign main_core_outputs.ifu_axi_awburst = ifu_axi_awburst;
  assign main_core_outputs.ifu_axi_awlock = ifu_axi_awlock;
  assign main_core_outputs.ifu_axi_awcache = ifu_axi_awcache;
  assign main_core_outputs.ifu_axi_awprot = ifu_axi_awprot;
  assign main_core_outputs.ifu_axi_awqos = ifu_axi_awqos;
  assign main_core_outputs.ifu_axi_wvalid = ifu_axi_wvalid;
  assign main_core_outputs.ifu_axi_wdata = ifu_axi_wdata;
  assign main_core_outputs.ifu_axi_wstrb = ifu_axi_wstrb;
  assign main_core_outputs.ifu_axi_wlast = ifu_axi_wlast;
  assign main_core_outputs.ifu_axi_bready = ifu_axi_bready;
  assign main_core_outputs.ifu_axi_arvalid = ifu_axi_arvalid;
  assign main_core_outputs.ifu_axi_arid = ifu_axi_arid;
  assign main_core_outputs.ifu_axi_araddr = ifu_axi_araddr;
  assign main_core_outputs.ifu_axi_arregion = ifu_axi_arregion;
  assign main_core_outputs.ifu_axi_arlen = ifu_axi_arlen;
  assign main_core_outputs.ifu_axi_arsize = ifu_axi_arsize;
  assign main_core_outputs.ifu_axi_arburst = ifu_axi_arburst;
  assign main_core_outputs.ifu_axi_arlock = ifu_axi_arlock;
  assign main_core_outputs.ifu_axi_arcache = ifu_axi_arcache;
  assign main_core_outputs.ifu_axi_arprot = ifu_axi_arprot;
  assign main_core_outputs.ifu_axi_arqos = ifu_axi_arqos;
  assign main_core_outputs.ifu_axi_rready = ifu_axi_rready;
  assign main_core_outputs.sb_axi_awvalid = sb_axi_awvalid;
  assign main_core_outputs.sb_axi_awid = sb_axi_awid;
  assign main_core_outputs.sb_axi_awaddr = sb_axi_awaddr;
  assign main_core_outputs.sb_axi_awregion = sb_axi_awregion;
  assign main_core_outputs.sb_axi_awlen = sb_axi_awlen;
  assign main_core_outputs.sb_axi_awsize = sb_axi_awsize;
  assign main_core_outputs.sb_axi_awburst = sb_axi_awburst;
  assign main_core_outputs.sb_axi_awlock = sb_axi_awlock;
  assign main_core_outputs.sb_axi_awcache = sb_axi_awcache;
  assign main_core_outputs.sb_axi_awprot = sb_axi_awprot;
  assign main_core_outputs.sb_axi_awqos = sb_axi_awqos;
  assign main_core_outputs.sb_axi_wvalid = sb_axi_wvalid;
  assign main_core_outputs.sb_axi_wdata = sb_axi_wdata;
  assign main_core_outputs.sb_axi_wstrb = sb_axi_wstrb;
  assign main_core_outputs.sb_axi_wlast = sb_axi_wlast;
  assign main_core_outputs.sb_axi_bready = sb_axi_bready;
  assign main_core_outputs.sb_axi_arvalid = sb_axi_arvalid;
  assign main_core_outputs.sb_axi_arid = sb_axi_arid;
  assign main_core_outputs.sb_axi_araddr = sb_axi_araddr;
  assign main_core_outputs.sb_axi_arregion = sb_axi_arregion;
  assign main_core_outputs.sb_axi_arlen = sb_axi_arlen;
  assign main_core_outputs.sb_axi_arsize = sb_axi_arsize;
  assign main_core_outputs.sb_axi_arburst = sb_axi_arburst;
  assign main_core_outputs.sb_axi_arlock = sb_axi_arlock;
  assign main_core_outputs.sb_axi_arcache = sb_axi_arcache;
  assign main_core_outputs.sb_axi_arprot = sb_axi_arprot;
  assign main_core_outputs.sb_axi_arqos = sb_axi_arqos;
  assign main_core_outputs.sb_axi_rready = sb_axi_rready;
  assign main_core_outputs.dma_axi_awready = dma_axi_awready;
  assign main_core_outputs.dma_axi_wready = dma_axi_wready;
  assign main_core_outputs.dma_axi_bvalid = dma_axi_bvalid;
  assign main_core_outputs.dma_axi_bresp = dma_axi_bresp;
  assign main_core_outputs.dma_axi_bid = dma_axi_bid;
  assign main_core_outputs.dma_axi_arready = dma_axi_arready;
  assign main_core_outputs.dma_axi_rvalid = dma_axi_rvalid;
  assign main_core_outputs.dma_axi_rid = dma_axi_rid;
  assign main_core_outputs.dma_axi_rdata = dma_axi_rdata;
  assign main_core_outputs.dma_axi_rresp = dma_axi_rresp;
  assign main_core_outputs.dma_axi_rlast = dma_axi_rlast;
  assign main_core_outputs.haddr = haddr;
  assign main_core_outputs.hburst = hburst;
  assign main_core_outputs.hmastlock = hmastlock;
  assign main_core_outputs.hprot = hprot;
  assign main_core_outputs.hsize = hsize;
  assign main_core_outputs.htrans = htrans;
  assign main_core_outputs.hwrite = hwrite;
  assign main_core_outputs.lsu_haddr = lsu_haddr;
  assign main_core_outputs.lsu_hburst = lsu_hburst;
  assign main_core_outputs.lsu_hmastlock = lsu_hmastlock;
  assign main_core_outputs.lsu_hprot = lsu_hprot;
  assign main_core_outputs.lsu_hsize = lsu_hsize;
  assign main_core_outputs.lsu_htrans = lsu_htrans;
  assign main_core_outputs.lsu_hwrite = lsu_hwrite;
  assign main_core_outputs.lsu_hwdata = lsu_hwdata;
  assign main_core_outputs.sb_haddr = sb_haddr;
  assign main_core_outputs.sb_hburst = sb_hburst;
  assign main_core_outputs.sb_hmastlock = sb_hmastlock;
  assign main_core_outputs.sb_hprot = sb_hprot;
  assign main_core_outputs.sb_hsize = sb_hsize;
  assign main_core_outputs.sb_htrans = sb_htrans;
  assign main_core_outputs.sb_hwrite = sb_hwrite;
  assign main_core_outputs.sb_hwdata = sb_hwdata;
  assign main_core_outputs.dma_hrdata = dma_hrdata;
  assign main_core_outputs.dma_hreadyout = dma_hreadyout;
  assign main_core_outputs.dma_hresp = dma_hresp;
  assign main_core_outputs.dmi_reg_rdata = dmi_reg_rdata;
  assign main_core_outputs.iccm_ecc_single_error = iccm_ecc_single_error;
  assign main_core_outputs.iccm_ecc_double_error = iccm_ecc_double_error;
  assign main_core_outputs.dccm_ecc_single_error = dccm_ecc_single_error;
  assign main_core_outputs.dccm_ecc_double_error = dccm_ecc_double_error;

  // Shadow core enters reset immediately with main core but gets out of reset
  // after the delay
  logic [LockstepDelay:0] rst_shadow_sr, rst_dbg_shadow_sr;
  logic rst_shadow, rst_dbg_shadow;
  assign rst_shadow = &rst_shadow_sr;
  assign rst_dbg_shadow = &rst_dbg_shadow_sr;

  always_ff @(posedge clk or negedge rst_l) begin
    if (!rst_l) begin
      rst_shadow_sr <= '0;
    end else begin
      rst_shadow_sr <= (rst_shadow_sr << 1) + 1;
    end
  end

  always_ff @(posedge clk or negedge dbg_rst_l) begin
    if (!dbg_rst_l) begin
      rst_dbg_shadow_sr <= '0;
    end else begin
      rst_dbg_shadow_sr <= (rst_dbg_shadow_sr << 1) + 1;
    end
  end

  // Delay the inputs and outputs
  always_ff @(posedge clk or negedge rst_l) begin
      if (~rst_l) begin
        delay_input_d[0]  <= veer_inputs_t'(0);
        delay_output_d[0] <= veer_outputs_t'(0);
      end else begin
        delay_input_d[0]  <= main_core_inputs;
        delay_output_d[0] <= main_core_outputs;
      end
    end
  for (genvar i = 0; i < LockstepDelay; i++) begin
    always_ff @(posedge clk or negedge rst_l) begin
      if (!rst_l) begin
          delay_input_d[i+1]  <= veer_inputs_t'(0);
          delay_output_d[i+1] <= veer_outputs_t'(0);
      end else begin
        delay_input_d[i+1]  <= delay_input_d[i];
        delay_output_d[i+1] <= delay_output_d[i];
      end
    end
  end

`ifdef RV_LOCKSTEP_REGFILE_ENABLE
  el2_regfile_if shadow_core_regfile ();

  el2_regfile_if delayed_main_core_regfile[LockstepDelay:0] ();

  always_ff @(posedge clk or negedge rst_l) begin
    if (!rst_l) begin
      delayed_main_core_regfile[0].gpr <= '0;
      delayed_main_core_regfile[0].tlu <= '0;
    end else begin
      delayed_main_core_regfile[0].gpr <= main_core_regfile.gpr;
      delayed_main_core_regfile[0].tlu <= main_core_regfile.tlu;
    end
  end
  for (genvar i = 0; i < LockstepDelay; i++) begin
    always_ff @(posedge clk or negedge rst_l) begin
      if (!rst_l) begin
          delayed_main_core_regfile[i+1].gpr <= '0;
          delayed_main_core_regfile[i+1].tlu <= '0;
      end else begin
        delayed_main_core_regfile[i+1].gpr <= delayed_main_core_regfile[i].gpr;
        delayed_main_core_regfile[i+1].tlu <= delayed_main_core_regfile[i].tlu;
      end
    end
  end
`endif

  // Instantiate the el2_veer core
  el2_veer #(
      .pt(pt)
  ) xshadow_core (
`ifdef RV_LOCKSTEP_REGFILE_ENABLE
      .regfile(shadow_core_regfile.veer_rf_src),
`endif
      .clk(clk),
      .rst_l(rst_shadow),
      .dbg_rst_l(rst_dbg_shadow),
      .rst_vec(shadow_core_inputs.rst_vec),
      .nmi_int(shadow_core_inputs.nmi_int),
      .nmi_vec(shadow_core_inputs.nmi_vec),
      .core_rst_l(shadow_core_outputs.core_rst_l),

      // we use those clocks from main core
      .active_l2clk(),
      .free_l2clk  (),

      .trace_rv_i_insn_ip(shadow_core_outputs.trace_rv_i_insn_ip),
      .trace_rv_i_address_ip(shadow_core_outputs.trace_rv_i_address_ip),
      .trace_rv_i_valid_ip(shadow_core_outputs.trace_rv_i_valid_ip),
      .trace_rv_i_exception_ip(shadow_core_outputs.trace_rv_i_exception_ip),
      .trace_rv_i_ecause_ip(shadow_core_outputs.trace_rv_i_ecause_ip),
      .trace_rv_i_interrupt_ip(shadow_core_outputs.trace_rv_i_interrupt_ip),
      .trace_rv_i_tval_ip(shadow_core_outputs.trace_rv_i_tval_ip),

      .dccm_clk_override(shadow_core_outputs.dccm_clk_override),
      .icm_clk_override(shadow_core_outputs.icm_clk_override),
      .dec_tlu_core_ecc_disable(shadow_core_outputs.dec_tlu_core_ecc_disable),

      .i_cpu_halt_req(shadow_core_inputs.i_cpu_halt_req),
      .i_cpu_run_req(shadow_core_inputs.i_cpu_run_req),
      .o_cpu_halt_ack(shadow_core_outputs.o_cpu_halt_ack),
      .o_cpu_halt_status(shadow_core_outputs.o_cpu_halt_status),
      .o_cpu_run_ack(shadow_core_outputs.o_cpu_run_ack),
      .o_debug_mode_status(shadow_core_outputs.o_debug_mode_status),

      .core_id(core_id),

      .mpc_debug_halt_req(shadow_core_inputs.mpc_debug_halt_req),
      .mpc_debug_run_req (shadow_core_inputs.mpc_debug_run_req),
      .mpc_reset_run_req (shadow_core_inputs.mpc_reset_run_req),
      .mpc_debug_halt_ack(shadow_core_outputs.mpc_debug_halt_ack),
      .mpc_debug_run_ack (shadow_core_outputs.mpc_debug_run_ack),
      .debug_brkpt_status(shadow_core_outputs.debug_brkpt_status),

      .dec_tlu_perfcnt0(shadow_core_outputs.dec_tlu_perfcnt0),
      .dec_tlu_perfcnt1(shadow_core_outputs.dec_tlu_perfcnt1),
      .dec_tlu_perfcnt2(shadow_core_outputs.dec_tlu_perfcnt2),
      .dec_tlu_perfcnt3(shadow_core_outputs.dec_tlu_perfcnt3),

      .dccm_wren(shadow_core_outputs.dccm_wren),
      .dccm_rden(shadow_core_outputs.dccm_rden),
      .dccm_wr_addr_lo(shadow_core_outputs.dccm_wr_addr_lo),
      .dccm_wr_addr_hi(shadow_core_outputs.dccm_wr_addr_hi),
      .dccm_rd_addr_lo(shadow_core_outputs.dccm_rd_addr_lo),
      .dccm_rd_addr_hi(shadow_core_outputs.dccm_rd_addr_hi),
      .dccm_wr_data_lo(shadow_core_outputs.dccm_wr_data_lo),
      .dccm_wr_data_hi(shadow_core_outputs.dccm_wr_data_hi),
      .dccm_rd_data_lo(shadow_core_inputs.dccm_rd_data_lo),
      .dccm_rd_data_hi(shadow_core_inputs.dccm_rd_data_hi),

      .iccm_rw_addr(shadow_core_outputs.iccm_rw_addr),
      .iccm_wren(shadow_core_outputs.iccm_wren),
      .iccm_rden(shadow_core_outputs.iccm_rden),
      .iccm_wr_size(shadow_core_outputs.iccm_wr_size),
      .iccm_wr_data(shadow_core_outputs.iccm_wr_data),
      .iccm_buf_correct_ecc(shadow_core_outputs.iccm_buf_correct_ecc),
      .iccm_correction_state(shadow_core_outputs.iccm_correction_state),
      .iccm_rd_data(shadow_core_inputs.iccm_rd_data),
      .iccm_rd_data_ecc(shadow_core_inputs.iccm_rd_data_ecc),

      .ic_rw_addr(shadow_core_outputs.ic_rw_addr),
      .ic_tag_valid(shadow_core_outputs.ic_tag_valid),
      .ic_wr_en(shadow_core_outputs.ic_wr_en),
      .ic_rd_en(shadow_core_outputs.ic_rd_en),

      .ic_wr_data(shadow_core_outputs.ic_wr_data),
      .ic_rd_data(shadow_core_inputs.ic_rd_data),
      .ic_debug_rd_data(shadow_core_inputs.ic_debug_rd_data),
      .ictag_debug_rd_data(shadow_core_inputs.ictag_debug_rd_data),
      .ic_debug_wr_data(shadow_core_outputs.ic_debug_wr_data),

      .ic_eccerr(shadow_core_inputs.ic_eccerr),
      .ic_parerr(shadow_core_inputs.ic_parerr),
      .ic_premux_data(shadow_core_outputs.ic_premux_data),
      .ic_sel_premux_data(shadow_core_outputs.ic_sel_premux_data),

      .ic_debug_addr(shadow_core_outputs.ic_debug_addr),
      .ic_debug_rd_en(shadow_core_outputs.ic_debug_rd_en),
      .ic_debug_wr_en(shadow_core_outputs.ic_debug_wr_en),
      .ic_debug_tag_array(shadow_core_outputs.ic_debug_tag_array),
      .ic_debug_way(shadow_core_outputs.ic_debug_way),

      .ic_rd_hit  (shadow_core_inputs.ic_rd_hit),
      .ic_tag_perr(shadow_core_inputs.ic_tag_perr),

      .lsu_axi_awvalid(shadow_core_outputs.lsu_axi_awvalid),
      .lsu_axi_awready(shadow_core_inputs.lsu_axi_awready),
      .lsu_axi_awid(shadow_core_outputs.lsu_axi_awid),
      .lsu_axi_awaddr(shadow_core_outputs.lsu_axi_awaddr),
      .lsu_axi_awregion(shadow_core_outputs.lsu_axi_awregion),
      .lsu_axi_awlen(shadow_core_outputs.lsu_axi_awlen),
      .lsu_axi_awsize(shadow_core_outputs.lsu_axi_awsize),
      .lsu_axi_awburst(shadow_core_outputs.lsu_axi_awburst),
      .lsu_axi_awlock(shadow_core_outputs.lsu_axi_awlock),
      .lsu_axi_awcache(shadow_core_outputs.lsu_axi_awcache),
      .lsu_axi_awprot(shadow_core_outputs.lsu_axi_awprot),
      .lsu_axi_awqos(shadow_core_outputs.lsu_axi_awqos),
      .lsu_axi_wvalid(shadow_core_outputs.lsu_axi_wvalid),
      .lsu_axi_wready(shadow_core_inputs.lsu_axi_wready),
      .lsu_axi_wdata(shadow_core_outputs.lsu_axi_wdata),
      .lsu_axi_wstrb(shadow_core_outputs.lsu_axi_wstrb),
      .lsu_axi_wlast(shadow_core_outputs.lsu_axi_wlast),
      .lsu_axi_bvalid(shadow_core_inputs.lsu_axi_bvalid),
      .lsu_axi_bready(shadow_core_outputs.lsu_axi_bready),
      .lsu_axi_bresp(shadow_core_inputs.lsu_axi_bresp),
      .lsu_axi_bid(shadow_core_inputs.lsu_axi_bid),
      .lsu_axi_arvalid(shadow_core_outputs.lsu_axi_arvalid),
      .lsu_axi_arready(shadow_core_inputs.lsu_axi_arready),
      .lsu_axi_arid(shadow_core_outputs.lsu_axi_arid),
      .lsu_axi_araddr(shadow_core_outputs.lsu_axi_araddr),
      .lsu_axi_arregion(shadow_core_outputs.lsu_axi_arregion),
      .lsu_axi_arlen(shadow_core_outputs.lsu_axi_arlen),
      .lsu_axi_arsize(shadow_core_outputs.lsu_axi_arsize),
      .lsu_axi_arburst(shadow_core_outputs.lsu_axi_arburst),
      .lsu_axi_arlock(shadow_core_outputs.lsu_axi_arlock),
      .lsu_axi_arcache(shadow_core_outputs.lsu_axi_arcache),
      .lsu_axi_arprot(shadow_core_outputs.lsu_axi_arprot),
      .lsu_axi_arqos(shadow_core_outputs.lsu_axi_arqos),
      .lsu_axi_rvalid(shadow_core_inputs.lsu_axi_rvalid),
      .lsu_axi_rready(shadow_core_outputs.lsu_axi_rready),
      .lsu_axi_rid(shadow_core_inputs.lsu_axi_rid),
      .lsu_axi_rdata(shadow_core_inputs.lsu_axi_rdata),
      .lsu_axi_rresp(shadow_core_inputs.lsu_axi_rresp),
      .lsu_axi_rlast(shadow_core_inputs.lsu_axi_rlast),

      .ifu_axi_awvalid(shadow_core_outputs.ifu_axi_awvalid),
      .ifu_axi_awready(shadow_core_inputs.ifu_axi_awready),
      .ifu_axi_awid(shadow_core_outputs.ifu_axi_awid),
      .ifu_axi_awaddr(shadow_core_outputs.ifu_axi_awaddr),
      .ifu_axi_awregion(shadow_core_outputs.ifu_axi_awregion),
      .ifu_axi_awlen(shadow_core_outputs.ifu_axi_awlen),
      .ifu_axi_awsize(shadow_core_outputs.ifu_axi_awsize),
      .ifu_axi_awburst(shadow_core_outputs.ifu_axi_awburst),
      .ifu_axi_awlock(shadow_core_outputs.ifu_axi_awlock),
      .ifu_axi_awcache(shadow_core_outputs.ifu_axi_awcache),
      .ifu_axi_awprot(shadow_core_outputs.ifu_axi_awprot),
      .ifu_axi_awqos(shadow_core_outputs.ifu_axi_awqos),
      .ifu_axi_wvalid(shadow_core_outputs.ifu_axi_wvalid),
      .ifu_axi_wready(shadow_core_inputs.ifu_axi_wready),
      .ifu_axi_wdata(shadow_core_outputs.ifu_axi_wdata),
      .ifu_axi_wstrb(shadow_core_outputs.ifu_axi_wstrb),
      .ifu_axi_wlast(shadow_core_outputs.ifu_axi_wlast),
      .ifu_axi_bvalid(shadow_core_inputs.ifu_axi_bvalid),
      .ifu_axi_bready(shadow_core_outputs.ifu_axi_bready),
      .ifu_axi_bresp(shadow_core_inputs.ifu_axi_bresp),
      .ifu_axi_bid(shadow_core_inputs.ifu_axi_bid),
      .ifu_axi_arvalid(shadow_core_outputs.ifu_axi_arvalid),
      .ifu_axi_arready(shadow_core_inputs.ifu_axi_arready),
      .ifu_axi_arid(shadow_core_outputs.ifu_axi_arid),
      .ifu_axi_araddr(shadow_core_outputs.ifu_axi_araddr),
      .ifu_axi_arregion(shadow_core_outputs.ifu_axi_arregion),
      .ifu_axi_arlen(shadow_core_outputs.ifu_axi_arlen),
      .ifu_axi_arsize(shadow_core_outputs.ifu_axi_arsize),
      .ifu_axi_arburst(shadow_core_outputs.ifu_axi_arburst),
      .ifu_axi_arlock(shadow_core_outputs.ifu_axi_arlock),
      .ifu_axi_arcache(shadow_core_outputs.ifu_axi_arcache),
      .ifu_axi_arprot(shadow_core_outputs.ifu_axi_arprot),
      .ifu_axi_arqos(shadow_core_outputs.ifu_axi_arqos),
      .ifu_axi_rvalid(shadow_core_inputs.ifu_axi_rvalid),
      .ifu_axi_rready(shadow_core_outputs.ifu_axi_rready),
      .ifu_axi_rid(shadow_core_inputs.ifu_axi_rid),
      .ifu_axi_rdata(shadow_core_inputs.ifu_axi_rdata),
      .ifu_axi_rresp(shadow_core_inputs.ifu_axi_rresp),
      .ifu_axi_rlast(shadow_core_inputs.ifu_axi_rlast),

      .sb_axi_awvalid(shadow_core_outputs.sb_axi_awvalid),
      .sb_axi_awready(shadow_core_inputs.sb_axi_awready),
      .sb_axi_awid(shadow_core_outputs.sb_axi_awid),
      .sb_axi_awaddr(shadow_core_outputs.sb_axi_awaddr),
      .sb_axi_awregion(shadow_core_outputs.sb_axi_awregion),
      .sb_axi_awlen(shadow_core_outputs.sb_axi_awlen),
      .sb_axi_awsize(shadow_core_outputs.sb_axi_awsize),
      .sb_axi_awburst(shadow_core_outputs.sb_axi_awburst),
      .sb_axi_awlock(shadow_core_outputs.sb_axi_awlock),
      .sb_axi_awcache(shadow_core_outputs.sb_axi_awcache),
      .sb_axi_awprot(shadow_core_outputs.sb_axi_awprot),
      .sb_axi_awqos(shadow_core_outputs.sb_axi_awqos),
      .sb_axi_wvalid(shadow_core_outputs.sb_axi_wvalid),
      .sb_axi_wready(shadow_core_inputs.sb_axi_wready),
      .sb_axi_wdata(shadow_core_outputs.sb_axi_wdata),
      .sb_axi_wstrb(shadow_core_outputs.sb_axi_wstrb),
      .sb_axi_wlast(shadow_core_outputs.sb_axi_wlast),
      .sb_axi_bvalid(shadow_core_inputs.sb_axi_bvalid),
      .sb_axi_bready(shadow_core_outputs.sb_axi_bready),
      .sb_axi_bresp(shadow_core_inputs.sb_axi_bresp),
      .sb_axi_bid(shadow_core_inputs.sb_axi_bid),
      .sb_axi_arvalid(shadow_core_outputs.sb_axi_arvalid),
      .sb_axi_arready(shadow_core_inputs.sb_axi_arready),
      .sb_axi_arid(shadow_core_outputs.sb_axi_arid),
      .sb_axi_araddr(shadow_core_outputs.sb_axi_araddr),
      .sb_axi_arregion(shadow_core_outputs.sb_axi_arregion),
      .sb_axi_arlen(shadow_core_outputs.sb_axi_arlen),
      .sb_axi_arsize(shadow_core_outputs.sb_axi_arsize),
      .sb_axi_arburst(shadow_core_outputs.sb_axi_arburst),
      .sb_axi_arlock(shadow_core_outputs.sb_axi_arlock),
      .sb_axi_arcache(shadow_core_outputs.sb_axi_arcache),
      .sb_axi_arprot(shadow_core_outputs.sb_axi_arprot),
      .sb_axi_arqos(shadow_core_outputs.sb_axi_arqos),
      .sb_axi_rvalid(shadow_core_inputs.sb_axi_rvalid),
      .sb_axi_rready(shadow_core_outputs.sb_axi_rready),
      .sb_axi_rid(shadow_core_inputs.sb_axi_rid),
      .sb_axi_rdata(shadow_core_inputs.sb_axi_rdata),
      .sb_axi_rresp(shadow_core_inputs.sb_axi_rresp),
      .sb_axi_rlast(shadow_core_inputs.sb_axi_rlast),

      .dma_axi_awvalid(shadow_core_inputs.dma_axi_awvalid),
      .dma_axi_awready(shadow_core_outputs.dma_axi_awready),
      .dma_axi_awid(shadow_core_inputs.dma_axi_awid),
      .dma_axi_awaddr(shadow_core_inputs.dma_axi_awaddr),
      .dma_axi_awsize(shadow_core_inputs.dma_axi_awsize),
      .dma_axi_awprot(shadow_core_inputs.dma_axi_awprot),
      .dma_axi_awlen(shadow_core_inputs.dma_axi_awlen),
      .dma_axi_awburst(shadow_core_inputs.dma_axi_awburst),
      .dma_axi_wvalid(shadow_core_inputs.dma_axi_wvalid),
      .dma_axi_wready(shadow_core_outputs.dma_axi_wready),
      .dma_axi_wdata(shadow_core_inputs.dma_axi_wdata),
      .dma_axi_wstrb(shadow_core_inputs.dma_axi_wstrb),
      .dma_axi_wlast(shadow_core_inputs.dma_axi_wlast),
      .dma_axi_bvalid(shadow_core_outputs.dma_axi_bvalid),
      .dma_axi_bready(shadow_core_inputs.dma_axi_bready),
      .dma_axi_bresp(shadow_core_outputs.dma_axi_bresp),
      .dma_axi_bid(shadow_core_outputs.dma_axi_bid),
      .dma_axi_arvalid(shadow_core_inputs.dma_axi_arvalid),
      .dma_axi_arready(shadow_core_outputs.dma_axi_arready),
      .dma_axi_arid(shadow_core_inputs.dma_axi_arid),
      .dma_axi_araddr(shadow_core_inputs.dma_axi_araddr),
      .dma_axi_arsize(shadow_core_inputs.dma_axi_arsize),
      .dma_axi_arprot(shadow_core_inputs.dma_axi_arprot),
      .dma_axi_arlen(shadow_core_inputs.dma_axi_arlen),
      .dma_axi_arburst(shadow_core_inputs.dma_axi_arburst),
      .dma_axi_rvalid(shadow_core_outputs.dma_axi_rvalid),
      .dma_axi_rready(shadow_core_inputs.dma_axi_rready),
      .dma_axi_rid(shadow_core_outputs.dma_axi_rid),
      .dma_axi_rdata(shadow_core_outputs.dma_axi_rdata),
      .dma_axi_rresp(shadow_core_outputs.dma_axi_rresp),
      .dma_axi_rlast(shadow_core_outputs.dma_axi_rlast),

      .haddr(shadow_core_outputs.haddr),
      .hburst(shadow_core_outputs.hburst),
      .hmastlock(shadow_core_outputs.hmastlock),
      .hprot(shadow_core_outputs.hprot),
      .hsize(shadow_core_outputs.hsize),
      .htrans(shadow_core_outputs.htrans),
      .hwrite(shadow_core_outputs.hwrite),
      .hrdata(shadow_core_inputs.hrdata),
      .hready(shadow_core_inputs.hready),
      .hresp(shadow_core_inputs.hresp),

      .lsu_haddr(shadow_core_outputs.lsu_haddr),
      .lsu_hburst(shadow_core_outputs.lsu_hburst),
      .lsu_hmastlock(shadow_core_outputs.lsu_hmastlock),
      .lsu_hprot(shadow_core_outputs.lsu_hprot),
      .lsu_hsize(shadow_core_outputs.lsu_hsize),
      .lsu_htrans(shadow_core_outputs.lsu_htrans),
      .lsu_hwrite(shadow_core_outputs.lsu_hwrite),
      .lsu_hwdata(shadow_core_outputs.lsu_hwdata),
      .lsu_hrdata(shadow_core_inputs.lsu_hrdata),
      .lsu_hready(shadow_core_inputs.lsu_hready),
      .lsu_hresp(shadow_core_inputs.lsu_hresp),

      .sb_haddr(shadow_core_outputs.sb_haddr),
      .sb_hburst(shadow_core_outputs.sb_hburst),
      .sb_hmastlock(shadow_core_outputs.sb_hmastlock),
      .sb_hprot(shadow_core_outputs.sb_hprot),
      .sb_hsize(shadow_core_outputs.sb_hsize),
      .sb_htrans(shadow_core_outputs.sb_htrans),
      .sb_hwrite(shadow_core_outputs.sb_hwrite),
      .sb_hwdata(shadow_core_outputs.sb_hwdata),
      .sb_hrdata(shadow_core_inputs.sb_hrdata),
      .sb_hready(shadow_core_inputs.sb_hready),
      .sb_hresp(shadow_core_inputs.sb_hresp),

      .dma_hsel(shadow_core_inputs.dma_hsel),
      .dma_haddr(shadow_core_inputs.dma_haddr),
      .dma_hburst(shadow_core_inputs.dma_hburst),
      .dma_hmastlock(shadow_core_inputs.dma_hmastlock),
      .dma_hprot(shadow_core_inputs.dma_hprot),
      .dma_hsize(shadow_core_inputs.dma_hsize),
      .dma_htrans(shadow_core_inputs.dma_htrans),
      .dma_hwrite(shadow_core_inputs.dma_hwrite),
      .dma_hwdata(shadow_core_inputs.dma_hwdata),
      .dma_hreadyin(shadow_core_inputs.dma_hreadyin),
      .dma_hrdata(shadow_core_outputs.dma_hrdata),
      .dma_hreadyout(shadow_core_outputs.dma_hreadyout),
      .dma_hresp(shadow_core_outputs.dma_hresp),

      .lsu_bus_clk_en(shadow_core_inputs.lsu_bus_clk_en),
      .ifu_bus_clk_en(shadow_core_inputs.ifu_bus_clk_en),
      .dbg_bus_clk_en(shadow_core_inputs.dbg_bus_clk_en),
      .dma_bus_clk_en(shadow_core_inputs.dma_bus_clk_en),

      .dmi_reg_en(shadow_core_inputs.dmi_reg_en),
      .dmi_reg_addr(shadow_core_inputs.dmi_reg_addr),
      .dmi_reg_wr_en(shadow_core_inputs.dmi_reg_wr_en),
      .dmi_reg_wdata(shadow_core_inputs.dmi_reg_wdata),
      .dmi_reg_rdata(shadow_core_outputs.dmi_reg_rdata),

      .iccm_ecc_single_error(shadow_core_outputs.iccm_ecc_single_error),
      .iccm_ecc_double_error(shadow_core_outputs.iccm_ecc_double_error),
      .dccm_ecc_single_error(shadow_core_outputs.dccm_ecc_single_error),
      .dccm_ecc_double_error(shadow_core_outputs.dccm_ecc_double_error),

      .extintsrc_req(shadow_core_inputs.extintsrc_req),
      .timer_int(shadow_core_inputs.timer_int),
      .soft_int(shadow_core_inputs.soft_int),
      .scan_mode(shadow_core_inputs.scan_mode)
  );

  // Equivalence Check
  logic rst_n;
  assign rst_n = rst_shadow & rst_dbg_shadow;

  logic corruption_detected, outputs_corrupted;
  assign outputs_corrupted = delayed_main_core_outputs != shadow_core_outputs;

`ifdef RV_LOCKSTEP_REGFILE_ENABLE
  logic regfile_corrupted;
  assign regfile_corrupted   = (delayed_main_core_regfile[LockstepDelay].gpr != shadow_core_regfile.gpr)
                             | (delayed_main_core_regfile[LockstepDelay].tlu != shadow_core_regfile.tlu);
  assign corruption_detected = outputs_corrupted | regfile_corrupted;
`else
  assign corruption_detected = outputs_corrupted;
`endif

// Report corruption if all of the below requirements are fulfilled:
// - IOs of Main Core and Shadow Core differ OR error injection is enabled
// - Shadow Core is out of reset
// - Shadow Core is enabled
assign corruption_detected_o = ((corruption_detected | lockstep_err_injection_en_i) & rst_n) & ~disable_corruption_detection_i;

endmodule : el2_veer_lockstep
