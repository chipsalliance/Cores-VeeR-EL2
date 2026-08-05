// Copyright 2026 Antmicro <www.antmicro.com>
// //
// // SPDX-License-Identifier: Apache-2.0
//
`ifdef RV_TRIPLE_MODULAR_REDUNDANCY_ENABLE
module el2_tmr_complex
  import el2_pkg::*;
  import el2_mubi_pkg::*;
  import el2_lockstep_pkg::*;
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


    output logic                 dccm_clk_override,
    output logic                 icm_clk_override,
    output logic                 dec_tlu_core_ecc_disable,

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

    // External Buses
    // DCCM
    output logic                            dccm_wren,
    output logic                            dccm_rden,
    output logic [pt.DCCM_BITS-1:0]         dccm_wr_addr_lo,
    output logic [pt.DCCM_BITS-1:0]         dccm_wr_addr_hi,
    output logic [pt.DCCM_BITS-1:0]         dccm_rd_addr_lo,
    output logic [pt.DCCM_BITS-1:0]         dccm_rd_addr_hi,
    output logic [pt.DCCM_FDATA_WIDTH-1:0]  dccm_wr_data_lo,
    output logic [pt.DCCM_FDATA_WIDTH-1:0]  dccm_wr_data_hi,

    input logic [pt.DCCM_FDATA_WIDTH-1:0]   dccm_rd_data_lo,
    input logic [pt.DCCM_FDATA_WIDTH-1:0]   dccm_rd_data_hi,

    // ICCM
    output logic [pt.ICCM_BITS-1:1]     iccm_rw_addr,
    output logic                        iccm_wren,
    output logic                        iccm_rden,
    output logic [2:0]                  iccm_wr_size,
    output logic [77:0]                 iccm_wr_data,
    output logic                        iccm_buf_correct_ecc,
    output logic                        iccm_correction_state,

    input  logic [77:0]                 iccm_rd_data_ecc,

    // ICACHE
    output logic [31:1]                          ic_rw_addr,
    output logic [pt.ICACHE_NUM_WAYS-1:0]        ic_tag_valid,
    output logic [pt.ICACHE_NUM_WAYS-1:0]        ic_wr_en,
    output logic                                 ic_rd_en,

    output logic [pt.ICACHE_BANKS_WAY-1:0][70:0] ic_wr_data,         // Data to fill to the Icache. With ECC
    input  logic [141:0]                         ic_rd_data,              // Raw way-muxed 142-bit ECC-protected word pair. F2 stage.
    input  logic [1:0]                           ic_rd_addr_lo,            // F2-aligned ic_rw_addr_ff[2:1] for core-side rotate
    input  logic [pt.ICACHE_BANKS_WAY-1:0]       ic_rd_bank_check_en, // Per-bank ECC check enable for core-side decode
    input  logic [70:0]                          ic_debug_rd_data,        // Data read from Icache. 2x64bits + parity bits. F2 stage. With ECC
    input  logic [25:0]                          ictag_debug_rd_data,// Debug icache tag.
    output logic [70:0]                          ic_debug_wr_data,   // Debug wr cache.

    output logic [pt.ICACHE_INDEX_HI:3]          ic_debug_addr,      // Read/Write address to the Icache.
    output logic                                 ic_debug_rd_en,     // Icache debug rd
    output logic                                 ic_debug_wr_en,     // Icache debug wr
    output logic                                 ic_debug_tag_array, // Debug tag array
    output logic [pt.ICACHE_NUM_WAYS-1:0]        ic_debug_way,       // Debug way. Rd or Wr.

    input  logic [pt.ICACHE_NUM_WAYS-1:0]        ic_rd_hit,
    input  logic                                 ic_tag_perr,        // Icache Tag parity error

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

  // Cores Buses
  logic        core_rst_l_veer[3];
  logic [31:1] rst_vec_veer[3];
  logic        nmi_int_veer[3];
  logic [31:1] nmi_vec_veer[3];
  logic        active_state_veer[3];
  logic        active_l2clk_veer[3];
  logic        free_l2clk_veer[3];
  logic        active_clk_veer[3];
  logic        free_clk_veer[3];
  logic        timer_int_veer[3];
  logic        soft_int_veer[3];

  logic [31:0] trace_rv_i_insn_ip_veer[3];
  logic [31:0] trace_rv_i_address_ip_veer[3];
  logic        trace_rv_i_valid_ip_veer[3];
  logic        trace_rv_i_exception_ip_veer[3];
  logic [4:0]  trace_rv_i_ecause_ip_veer[3];
  logic        trace_rv_i_interrupt_ip_veer[3];
  logic [31:0] trace_rv_i_tval_ip_veer[3];


  logic dccm_clk_override_veer[3];
  logic icm_clk_override_veer[3];
  logic dec_tlu_bus_clk_override_veer[3];
  logic dec_tlu_force_halt_veer[3];
  logic dec_tlu_core_ecc_disable_veer[3];

  logic i_cpu_halt_req_veer[3];
  logic i_cpu_run_req_veer[3];
  logic o_cpu_halt_ack_veer[3];
  logic o_cpu_halt_status_veer[3];
  logic o_cpu_run_ack_veer[3];
  logic o_debug_mode_status_veer[3];
  // external MPC halt/run interface
  logic mpc_debug_halt_req_veer[3];
  logic mpc_debug_halt_ack_veer[3];
  logic mpc_debug_run_req_veer[3];
  logic mpc_debug_run_ack_veer[3];
  logic mpc_reset_run_req_veer[3];
  logic debug_brkpt_status_veer[3];

  // PIC registers
  logic        pic_clk_override_veer[3];
  logic        pic_io_clk_override_veer[3];
  logic        picm_wren_veer[3];
  logic        picm_rden_veer[3];
  logic        picm_mken_veer[3];
  logic [31:0] picm_rdaddr_veer[3];
  logic [31:0] picm_wraddr_veer[3];
  logic [31:0] picm_wr_data_veer[3];
  logic [31:0] picm_rd_data_veer[3];
  logic [7:0]  pic_claimid_veer[3];
  logic [3:0]  pic_pl_veer[3], meicurpl_veer[3], meipt_veer[3];
  logic        mexintpend_veer[3];
  logic        mhwakeup_veer[3];

  // Perf registers
  logic dec_tlu_perfcnt0_veer[3];
  logic dec_tlu_perfcnt1_veer[3];
  logic dec_tlu_perfcnt2_veer[3];
  logic dec_tlu_perfcnt3_veer[3];
  // DCCM
  logic                           dccm_wren_veer[3];
  logic                           dccm_rden_veer[3];
  logic [pt.DCCM_BITS-1:0]        dccm_wr_addr_lo_veer[3];
  logic [pt.DCCM_BITS-1:0]        dccm_wr_addr_hi_veer[3];
  logic [pt.DCCM_BITS-1:0]        dccm_rd_addr_lo_veer[3];
  logic [pt.DCCM_BITS-1:0]        dccm_rd_addr_hi_veer[3];
  logic [pt.DCCM_FDATA_WIDTH-1:0] dccm_wr_data_lo_veer[3];
  logic [pt.DCCM_FDATA_WIDTH-1:0] dccm_wr_data_hi_veer[3];
  logic [pt.DCCM_FDATA_WIDTH-1:0] dccm_rd_data_lo_veer[3];
  logic [pt.DCCM_FDATA_WIDTH-1:0] dccm_rd_data_hi_veer[3];

  // ICCM
  logic [pt.ICCM_BITS-1:1] iccm_rw_addr_veer[3];
  logic                    iccm_wren_veer[3];
  logic                    iccm_rden_veer[3];
  logic [2:0]              iccm_wr_size_veer[3];
  logic [77:0]             iccm_wr_data_veer[3];
  logic                    iccm_buf_correct_ecc_veer[3];
  logic                    iccm_correction_state_veer[3];
  logic [77:0]             iccm_rd_data_ecc_veer[3];

  // ICACHE
  logic [31:1]                          ic_rw_addr_veer[3];
  logic [pt.ICACHE_NUM_WAYS-1:0]        ic_tag_valid_veer[3];
  logic [pt.ICACHE_NUM_WAYS-1:0]        ic_wr_en_veer[3];
  logic                                 ic_rd_en_veer[3];

  logic [pt.ICACHE_BANKS_WAY-1:0][70:0] ic_wr_data_veer[3];
  logic [141:0]                         ic_rd_data_veer[3];
  logic [1:0]                           ic_rd_addr_lo_veer[3];
  logic [pt.ICACHE_BANKS_WAY-1:0]       ic_rd_bank_check_en_veer[3];
  logic [70:0]                          ic_debug_rd_data_veer[3];
  logic [25:0]                          ictag_debug_rd_data_veer[3];
  logic [70:0]                          ic_debug_wr_data_veer[3];

  logic [pt.ICACHE_INDEX_HI:3]          ic_debug_addr_veer[3];
  logic                                 ic_debug_rd_en_veer[3];
  logic                                 ic_debug_wr_en_veer[3];
  logic                                 ic_debug_tag_array_veer[3];
  logic [pt.ICACHE_NUM_WAYS-1:0]        ic_debug_way_veer[3];

  logic [pt.ICACHE_NUM_WAYS-1:0]        ic_rd_hit_veer[3];
  logic                                 ic_tag_perr_veer[3];

  //-------------------------- LSU AXI signals--------------------------
  // AXI Write Channels
  logic                      lsu_axi_awvalid_veer[3];
  logic                      lsu_axi_awready_veer[3];
  logic [pt.LSU_BUS_TAG-1:0] lsu_axi_awid_veer[3];
  logic [31:0]               lsu_axi_awaddr_veer[3];
  logic [3:0]                lsu_axi_awregion_veer[3];
  logic [7:0]                lsu_axi_awlen_veer[3];
  logic [2:0]                lsu_axi_awsize_veer[3];
  logic [1:0]                lsu_axi_awburst_veer[3];
  logic                      lsu_axi_awlock_veer[3];
  logic [3:0]                lsu_axi_awcache_veer[3];
  logic [2:0]                lsu_axi_awprot_veer[3];
  logic [3:0]                lsu_axi_awqos_veer[3];
  logic                      lsu_axi_wvalid_veer[3];
  logic                      lsu_axi_wready_veer[3];
  logic [63:0]               lsu_axi_wdata_veer[3];
  logic [7:0]                lsu_axi_wstrb_veer[3];
  logic                      lsu_axi_wlast_veer[3];
  logic                      lsu_axi_bvalid_veer[3];
  logic                      lsu_axi_bready_veer[3];
  logic [1:0]                lsu_axi_bresp_veer[3];
  logic [pt.LSU_BUS_TAG-1:0] lsu_axi_bid_veer[3];

  // AXI Read Channels
  logic                      lsu_axi_arvalid_veer[3];
  logic                      lsu_axi_arready_veer[3];
  logic [pt.LSU_BUS_TAG-1:0] lsu_axi_arid_veer[3];
  logic [31:0]               lsu_axi_araddr_veer[3];
  logic [3:0]                lsu_axi_arregion_veer[3];
  logic [7:0]                lsu_axi_arlen_veer[3];
  logic [2:0]                lsu_axi_arsize_veer[3];
  logic [1:0]                lsu_axi_arburst_veer[3];
  logic                      lsu_axi_arlock_veer[3];
  logic [3:0]                lsu_axi_arcache_veer[3];
  logic [2:0]                lsu_axi_arprot_veer[3];
  logic [3:0]                lsu_axi_arqos_veer[3];
  logic                      lsu_axi_rvalid_veer[3];
  logic                      lsu_axi_rready_veer[3];
  logic [pt.LSU_BUS_TAG-1:0] lsu_axi_rid_veer[3];
  logic [63:0]               lsu_axi_rdata_veer[3];
  logic [1:0]                lsu_axi_rresp_veer[3];
  logic                      lsu_axi_rlast_veer[3];

  //-------------------------- IFU AXI signals--------------------------
  // AXI Write Channels
  logic                      ifu_axi_awvalid_veer[3];
  logic                      ifu_axi_awready_veer[3];
  logic [pt.IFU_BUS_TAG-1:0] ifu_axi_awid_veer[3];
  logic [31:0]               ifu_axi_awaddr_veer[3];
  logic [3:0]                ifu_axi_awregion_veer[3];
  logic [7:0]                ifu_axi_awlen_veer[3];
  logic [2:0]                ifu_axi_awsize_veer[3];
  logic [1:0]                ifu_axi_awburst_veer[3];
  logic                      ifu_axi_awlock_veer[3];
  logic [3:0]                ifu_axi_awcache_veer[3];
  logic [2:0]                ifu_axi_awprot_veer[3];
  logic [3:0]                ifu_axi_awqos_veer[3];
  logic                      ifu_axi_wvalid_veer[3];
  logic                      ifu_axi_wready_veer[3];
  logic [63:0]               ifu_axi_wdata_veer[3];
  logic [7:0]                ifu_axi_wstrb_veer[3];
  logic                      ifu_axi_wlast_veer[3];
  logic                      ifu_axi_bvalid_veer[3];
  logic                      ifu_axi_bready_veer[3];
  logic [1:0]                ifu_axi_bresp_veer[3];
  logic [pt.IFU_BUS_TAG-1:0] ifu_axi_bid_veer[3];

  // AXI Read Channels
  logic                      ifu_axi_arvalid_veer[3];
  logic                      ifu_axi_arready_veer[3];
  logic [pt.IFU_BUS_TAG-1:0] ifu_axi_arid_veer[3];
  logic [31:0]               ifu_axi_araddr_veer[3];
  logic [3:0]                ifu_axi_arregion_veer[3];
  logic [7:0]                ifu_axi_arlen_veer[3];
  logic [2:0]                ifu_axi_arsize_veer[3];
  logic [1:0]                ifu_axi_arburst_veer[3];
  logic                      ifu_axi_arlock_veer[3];
  logic [3:0]                ifu_axi_arcache_veer[3];
  logic [2:0]                ifu_axi_arprot_veer[3];
  logic [3:0]                ifu_axi_arqos_veer[3];
  logic                      ifu_axi_rvalid_veer[3];
  logic                      ifu_axi_rready_veer[3];
  logic [pt.IFU_BUS_TAG-1:0] ifu_axi_rid_veer[3];
  logic [63:0]               ifu_axi_rdata_veer[3];
  logic [1:0]                ifu_axi_rresp_veer[3];
  logic                      ifu_axi_rlast_veer[3];

  //-------------------------- SB AXI signals--------------------------
  // AXI Write Channels
  logic                     sb_axi_awvalid_veer[3];
  logic                     sb_axi_awready_veer[3];
  logic [pt.SB_BUS_TAG-1:0] sb_axi_awid_veer[3];
  logic [31:0]              sb_axi_awaddr_veer[3];
  logic [3:0]               sb_axi_awregion_veer[3];
  logic [7:0]               sb_axi_awlen_veer[3];
  logic [2:0]               sb_axi_awsize_veer[3];
  logic [1:0]               sb_axi_awburst_veer[3];
  logic                     sb_axi_awlock_veer[3];
  logic [3:0]               sb_axi_awcache_veer[3];
  logic [2:0]               sb_axi_awprot_veer[3];
  logic [3:0]               sb_axi_awqos_veer[3];
  logic                     sb_axi_wvalid_veer[3];
  logic                     sb_axi_wready_veer[3];
  logic [63:0]              sb_axi_wdata_veer[3];
  logic [7:0]               sb_axi_wstrb_veer[3];
  logic                     sb_axi_wlast_veer[3];
  logic                     sb_axi_bvalid_veer[3];
  logic                     sb_axi_bready_veer[3];
  logic [1:0]               sb_axi_bresp_veer[3];
  logic [pt.SB_BUS_TAG-1:0] sb_axi_bid_veer[3];

  // AXI Read Channels
  logic                     sb_axi_arvalid_veer[3];
  logic                     sb_axi_arready_veer[3];
  logic [pt.SB_BUS_TAG-1:0] sb_axi_arid_veer[3];
  logic [31:0]              sb_axi_araddr_veer[3];
  logic [3:0]               sb_axi_arregion_veer[3];
  logic [7:0]               sb_axi_arlen_veer[3];
  logic [2:0]               sb_axi_arsize_veer[3];
  logic [1:0]               sb_axi_arburst_veer[3];
  logic                     sb_axi_arlock_veer[3];
  logic [3:0]               sb_axi_arcache_veer[3];
  logic [2:0]               sb_axi_arprot_veer[3];
  logic [3:0]               sb_axi_arqos_veer[3];
  logic                     sb_axi_rvalid_veer[3];
  logic                     sb_axi_rready_veer[3];
  logic [pt.SB_BUS_TAG-1:0] sb_axi_rid_veer[3];
  logic [63:0]              sb_axi_rdata_veer[3];
  logic [1:0]               sb_axi_rresp_veer[3];
  logic                     sb_axi_rlast_veer[3];

  //-------------------------- DMA AXI signals--------------------------
  // AXI Write Channels
  logic                      dma_axi_awvalid_veer[3];
  logic                      dma_axi_awready_veer[3];
  logic [pt.DMA_BUS_TAG-1:0] dma_axi_awid_veer[3];
  logic [31:0]               dma_axi_awaddr_veer[3];
  logic [2:0]                dma_axi_awsize_veer[3];
  logic [2:0]                dma_axi_awprot_veer[3];
  logic [7:0]                dma_axi_awlen_veer[3];
  logic [1:0]                dma_axi_awburst_veer[3];
  logic                      dma_axi_wvalid_veer[3];
  logic                      dma_axi_wready_veer[3];
  logic [63:0]               dma_axi_wdata_veer[3];
  logic [7:0]                dma_axi_wstrb_veer[3];
  logic                      dma_axi_wlast_veer[3];
  logic                      dma_axi_bvalid_veer[3];
  logic                      dma_axi_bready_veer[3];
  logic [1:0]                dma_axi_bresp_veer[3];
  logic [pt.DMA_BUS_TAG-1:0] dma_axi_bid_veer[3];

  // AXI Read Channels
  logic                      dma_axi_arvalid_veer[3];
  logic                      dma_axi_arready_veer[3];
  logic [pt.DMA_BUS_TAG-1:0] dma_axi_arid_veer[3];
  logic [31:0]               dma_axi_araddr_veer[3];
  logic [2:0]                dma_axi_arsize_veer[3];
  logic [2:0]                dma_axi_arprot_veer[3];
  logic [7:0]                dma_axi_arlen_veer[3];
  logic [1:0]                dma_axi_arburst_veer[3];
  logic                      dma_axi_rvalid_veer[3];
  logic                      dma_axi_rready_veer[3];
  logic [pt.DMA_BUS_TAG-1:0] dma_axi_rid_veer[3];
  logic [63:0]               dma_axi_rdata_veer[3];
  logic [1:0]                dma_axi_rresp_veer[3];
  logic                      dma_axi_rlast_veer[3];

  logic        lsu_bus_clk_en_veer[3];
  logic        ifu_bus_clk_en_veer[3];
  logic        dbg_bus_clk_en_veer[3];
  logic        dma_bus_clk_en_veer[3];

  logic        dmi_reg_en_veer[3];                // read or write
  logic [6:0]  dmi_reg_addr_veer[3];              // address of DM register
  logic        dmi_reg_wr_en_veer[3];             // write instruction
  logic [31:0] dmi_reg_wdata_veer[3];             // write data
  logic [31:0] dmi_reg_rdata_veer[3];

  // ICCM/DCCM ECC status
  logic iccm_ecc_single_error_veer[3];
  logic iccm_ecc_double_error_veer[3];
  logic dccm_ecc_single_error_veer[3];
  logic dccm_ecc_double_error_veer[3];

  // GPR recovery signals
  el2_mubi_pkg::el2_mubi_t recovery_gpr_en_veer[3];
  logic                    recovery_gpr_wen_veer[3];
  logic [ 4:0]             recovery_gpr_wraddr_veer[3];
  logic [31:0]             recovery_gpr_wrdata_veer[3];
  logic [ 4:0]             recovery_gpr_rdaddr_veer[3];
  logic [31:0]             recovery_gpr_rddata_veer[3];

  // CSR recovery signals
  el2_mubi_pkg::el2_mubi_t recovery_csr_en_veer[3];
  logic                    recovery_csr_wen_veer[3];
  logic [11:0]             recovery_csr_wraddr_veer[3];
  logic [31:0]             recovery_csr_wrdata_veer[3];
  logic [11:0]             recovery_csr_rdaddr_veer[3];
  logic [31:0]             recovery_csr_rddata_veer[3];

  // POST TMR AXI
  //-------------------------- LSU AXI signals--------------------------
  // AXI Write Channels
  logic                      lsu_axi_awvalid_int;
  logic                      lsu_axi_awready_int;
  logic [pt.LSU_BUS_TAG-1:0] lsu_axi_awid_int;
  logic [31:0]               lsu_axi_awaddr_int;
  logic [3:0]                lsu_axi_awregion_int;
  logic [7:0]                lsu_axi_awlen_int;
  logic [2:0]                lsu_axi_awsize_int;
  logic [1:0]                lsu_axi_awburst_int;
  logic                      lsu_axi_awlock_int;
  logic [3:0]                lsu_axi_awcache_int;
  logic [2:0]                lsu_axi_awprot_int;
  logic [3:0]                lsu_axi_awqos_int;
  logic                      lsu_axi_wvalid_int;
  logic                      lsu_axi_wready_int;
  logic [63:0]               lsu_axi_wdata_int;
  logic [7:0]                lsu_axi_wstrb_int;
  logic                      lsu_axi_wlast_int;
  logic                      lsu_axi_bvalid_int;
  logic                      lsu_axi_bready_int;
  logic [1:0]                lsu_axi_bresp_int;
  logic [pt.LSU_BUS_TAG-1:0] lsu_axi_bid_int;
  // AXI Read Channels
  logic                      lsu_axi_arvalid_int;
  logic                      lsu_axi_arready_int;
  logic [pt.LSU_BUS_TAG-1:0] lsu_axi_arid_int;
  logic [31:0]               lsu_axi_araddr_int;
  logic [3:0]                lsu_axi_arregion_int;
  logic [7:0]                lsu_axi_arlen_int;
  logic [2:0]                lsu_axi_arsize_int;
  logic [1:0]                lsu_axi_arburst_int;
  logic                      lsu_axi_arlock_int;
  logic [3:0]                lsu_axi_arcache_int;
  logic [2:0]                lsu_axi_arprot_int;
  logic [3:0]                lsu_axi_arqos_int;
  logic                      lsu_axi_rvalid_int;
  logic                      lsu_axi_rready_int;
  logic [pt.LSU_BUS_TAG-1:0] lsu_axi_rid_int;
  logic [63:0]               lsu_axi_rdata_int;
  logic [1:0]                lsu_axi_rresp_int;
  logic                      lsu_axi_rlast_int;
  //-------------------------- IFU AXI signals--------------------------
  // AXI Write Channels
  logic                      ifu_axi_awvalid_int;
  logic                      ifu_axi_awready_int;
  logic [pt.IFU_BUS_TAG-1:0] ifu_axi_awid_int;
  logic [31:0]               ifu_axi_awaddr_int;
  logic [3:0]                ifu_axi_awregion_int;
  logic [7:0]                ifu_axi_awlen_int;
  logic [2:0]                ifu_axi_awsize_int;
  logic [1:0]                ifu_axi_awburst_int;
  logic                      ifu_axi_awlock_int;
  logic [3:0]                ifu_axi_awcache_int;
  logic [2:0]                ifu_axi_awprot_int;
  logic [3:0]                ifu_axi_awqos_int;
  logic                      ifu_axi_wvalid_int;
  logic                      ifu_axi_wready_int;
  logic [63:0]               ifu_axi_wdata_int;
  logic [7:0]                ifu_axi_wstrb_int;
  logic                      ifu_axi_wlast_int;
  logic                      ifu_axi_bvalid_int;
  logic                      ifu_axi_bready_int;
  logic [1:0]                ifu_axi_bresp_int;
  logic [pt.IFU_BUS_TAG-1:0] ifu_axi_bid_int;
  // AXI Read Channels
  logic                      ifu_axi_arvalid_int;
  logic                      ifu_axi_arready_int;
  logic [pt.IFU_BUS_TAG-1:0] ifu_axi_arid_int;
  logic [31:0]               ifu_axi_araddr_int;
  logic [3:0]                ifu_axi_arregion_int;
  logic [7:0]                ifu_axi_arlen_int;
  logic [2:0]                ifu_axi_arsize_int;
  logic [1:0]                ifu_axi_arburst_int;
  logic                      ifu_axi_arlock_int;
  logic [3:0]                ifu_axi_arcache_int;
  logic [2:0]                ifu_axi_arprot_int;
  logic [3:0]                ifu_axi_arqos_int;
  logic                      ifu_axi_rvalid_int;
  logic                      ifu_axi_rready_int;
  logic [pt.IFU_BUS_TAG-1:0] ifu_axi_rid_int;
  logic [63:0]               ifu_axi_rdata_int;
  logic [1:0]                ifu_axi_rresp_int;
  logic                      ifu_axi_rlast_int;
  //-------------------------- SB AXI signals--------------------------
  // AXI Write Channels
  logic                     sb_axi_awvalid_int;
  logic                     sb_axi_awready_int;
  logic [pt.SB_BUS_TAG-1:0] sb_axi_awid_int;
  logic [31:0]              sb_axi_awaddr_int;
  logic [3:0]               sb_axi_awregion_int;
  logic [7:0]               sb_axi_awlen_int;
  logic [2:0]               sb_axi_awsize_int;
  logic [1:0]               sb_axi_awburst_int;
  logic                     sb_axi_awlock_int;
  logic [3:0]               sb_axi_awcache_int;
  logic [2:0]               sb_axi_awprot_int;
  logic [3:0]               sb_axi_awqos_int;
  logic                     sb_axi_wvalid_int;
  logic                     sb_axi_wready_int;
  logic [63:0]              sb_axi_wdata_int;
  logic [7:0]               sb_axi_wstrb_int;
  logic                     sb_axi_wlast_int;
  logic                     sb_axi_bvalid_int;
  logic                     sb_axi_bready_int;
  logic [1:0]               sb_axi_bresp_int;
  logic [pt.SB_BUS_TAG-1:0] sb_axi_bid_int;
  // AXI Read Channels
  logic                     sb_axi_arvalid_int;
  logic                     sb_axi_arready_int;
  logic [pt.SB_BUS_TAG-1:0] sb_axi_arid_int;
  logic [31:0]              sb_axi_araddr_int;
  logic [3:0]               sb_axi_arregion_int;
  logic [7:0]               sb_axi_arlen_int;
  logic [2:0]               sb_axi_arsize_int;
  logic [1:0]               sb_axi_arburst_int;
  logic                     sb_axi_arlock_int;
  logic [3:0]               sb_axi_arcache_int;
  logic [2:0]               sb_axi_arprot_int;
  logic [3:0]               sb_axi_arqos_int;
  logic                     sb_axi_rvalid_int;
  logic                     sb_axi_rready_int;
  logic [pt.SB_BUS_TAG-1:0] sb_axi_rid_int;
  logic [63:0]              sb_axi_rdata_int;
  logic [1:0]               sb_axi_rresp_int;
  logic                     sb_axi_rlast_int;
  //-------------------------- DMA AXI signals--------------------------
  // AXI Write Channels
  logic                      dma_axi_awvalid_int;
  logic                      dma_axi_awready_int;
  logic [pt.DMA_BUS_TAG-1:0] dma_axi_awid_int;
  logic [31:0]               dma_axi_awaddr_int;
  logic [2:0]                dma_axi_awsize_int;
  logic [2:0]                dma_axi_awprot_int;
  logic [7:0]                dma_axi_awlen_int;
  logic [1:0]                dma_axi_awburst_int;
  logic                      dma_axi_wvalid_int;
  logic                      dma_axi_wready_int;
  logic [63:0]               dma_axi_wdata_int;
  logic [7:0]                dma_axi_wstrb_int;
  logic                      dma_axi_wlast_int;
  logic                      dma_axi_bvalid_int;
  logic                      dma_axi_bready_int;
  logic [1:0]                dma_axi_bresp_int;
  logic [pt.DMA_BUS_TAG-1:0] dma_axi_bid_int;
  // AXI Read Channels
  logic                      dma_axi_arvalid_int;
  logic                      dma_axi_arready_int;
  logic [pt.DMA_BUS_TAG-1:0] dma_axi_arid_int;
  logic [31:0]               dma_axi_araddr_int;
  logic [2:0]                dma_axi_arsize_int;
  logic [2:0]                dma_axi_arprot_int;
  logic [7:0]                dma_axi_arlen_int;
  logic [1:0]                dma_axi_arburst_int;
  logic                      dma_axi_rvalid_int;
  logic                      dma_axi_rready_int;
  logic [pt.DMA_BUS_TAG-1:0] dma_axi_rid_int;
  logic [63:0]               dma_axi_rdata_int;
  logic [1:0]                dma_axi_rresp_int;
  logic                      dma_axi_rlast_int;

  logic dec_tlu_bus_clk_override_int;
  logic dec_tlu_force_halt_int;

  // PIC ports
  logic        pic_clk_override_int;
  logic        pic_io_clk_override_int;
  logic        picm_wren_int;
  logic        picm_rden_int;
  logic        picm_mken_int;
  logic [31:0] picm_rdaddr_int;
  logic [31:0] picm_wraddr_int;
  logic [31:0] picm_wr_data_int;
  logic [31:0] picm_rd_data_int;
  logic [7:0]  pic_claimid_int;
  logic [3:0]  pic_pl_int, meicurpl_int, meipt_int;
  logic        mexintpend_int;
  logic        mhwakeup_int;

  logic        free_clk_int;

  //-------------------------------------------------------------------

  // TMR AXI fault signals
  el2_mubi_pkg::el2_mubi_t axi_fault_d[3];
  el2_mubi_pkg::el2_mubi_t axi_fault_q[3];
  el2_mubi_pkg::el2_mubi_t axi_fault_clr[3];

  // TMR ICCM fault signals
  el2_mubi_pkg::el2_mubi_t iccm_fault_d[3];
  el2_mubi_pkg::el2_mubi_t iccm_fault_q[3];
  el2_mubi_pkg::el2_mubi_t iccm_fault_clr[3];

  // TMR DCCM fault signals
  el2_mubi_pkg::el2_mubi_t dccm_fault_d[3];
  el2_mubi_pkg::el2_mubi_t dccm_fault_q[3];
  el2_mubi_pkg::el2_mubi_t dccm_fault_clr[3];

  // TODO: Other fault signals

  //-------------------------------------------------------------------
  // Global TMR fault state and control

  el2_mubi_pkg::el2_mubi_t tmr_fault_d[3];
  el2_mubi_pkg::el2_mubi_t tmr_fault_q[3];
  el2_mubi_pkg::el2_mubi_t tmr_fault_clr[3];

  // TODO: Potentially move the following to a new "el2_tmr_fault" module
  generate for(genvar i=0; i<3; i=i+1) begin
    assign axi_fault_d[i]    = tmr_fault_d[i];
    assign axi_fault_clr[i]  = tmr_fault_clr[i];

    assign iccm_fault_d[i]   = tmr_fault_d[i];
    assign iccm_fault_clr[i] = tmr_fault_clr[i];

    assign dccm_fault_d[i]   = tmr_fault_d[i];
    assign dccm_fault_clr[i] = tmr_fault_clr[i];

    assign tmr_fault_q[i]  = mubi_or3(axi_fault_q[i], iccm_fault_q[i], dccm_fault_q[i]); // TODO: Aggregate ALL TMR fault state signals
  end endgenerate

  // FIXME: Remove fault stubs
  generate for(genvar i=0; i<3; i=i+1) begin
    assign tmr_fault_d[i] = El2MuBiFalse;
    assign tmr_fault_clr[i] = El2MuBiFalse;
  end endgenerate

  //-------------------------------------------------------------------

  el2_tmr_axi #(.pt(pt)) el2_tmr_axi_u (.*);
  el2_tmr_iccm #(.pt(pt)) el2_tmr_iccm_u (.*);
  el2_tmr_dccm #(.pt(pt)) el2_tmr_dccm_u (.*);
  el2_tmr_dmi #(.pt(pt)) el2_tmr_dmi_u (.*);
  el2_tmr_ic #(.pt(pt)) el2_tmr_ic_u (.*);
  el2_tmr_pic #(.pt(pt)) el2_tmr_pic_u (.*);
  el2_tmr_complex_io el2_tmr_complex_io_u(
      .free_clk(free_clk_int),
      .*
  );
  el2_tmr_complex_clk #(.pt(pt)) el2_tmr_complex_clk_u(.*);
  el2_tmr_exec_ctrl #(.pt(pt)) el2_tmr_exec_ctrl_u (.*);
  el2_tmr_misc #(.pt(pt)) el2_tmr_misc_u (.*);

  // TODO: Implemente recovery logic
  always_comb begin
    for (int i=0;i < 3; i+=1) begin
      recovery_gpr_en_veer[i] = el2_mubi_pkg::El2MuBiFalse;
      recovery_gpr_wen_veer[i] = '0;
      recovery_gpr_wraddr_veer[i] = '0;
      recovery_gpr_wrdata_veer[i] = '0;
      recovery_gpr_rdaddr_veer[i] = '0;
      recovery_csr_en_veer[i] = el2_mubi_pkg::El2MuBiFalse;
      recovery_csr_wen_veer[i] = '0;
      recovery_csr_wraddr_veer[i] = '0;
      recovery_csr_wrdata_veer[i] = '0;
      recovery_csr_rdaddr_veer[i] = '0;
    end
  end

  for (genvar i=0;i < 3; i+=1) begin: cores
    logic dec_tlu_dccm_wr_readback_disable; // TODO: Is it needed?
    logic dccm_write_readback_error; // TODO: Is it needed?

    el2_veer #(.pt(pt)) veer (
        .clk(clk),
        .rst_l(rst_l),
        .dbg_rst_l(dbg_rst_l),
        .rst_vec(rst_vec_veer[i]),
        .nmi_int(nmi_int_veer[i]),
        .nmi_vec(nmi_vec_veer[i]),
        .core_rst_l(core_rst_l_veer[i]),
        .active_state(active_state_veer[i]),
        .active_l2clk(active_l2clk_veer[i]),
        .free_l2clk(free_l2clk_veer[i]),
        .free_clk(free_clk_veer[i]),
        .active_clk(active_clk_veer[i]),
        .trace_rv_i_insn_ip(trace_rv_i_insn_ip_veer[i]),
        .trace_rv_i_address_ip(trace_rv_i_address_ip_veer[i]),
        .trace_rv_i_valid_ip(trace_rv_i_valid_ip_veer[i]),
        .trace_rv_i_exception_ip(trace_rv_i_exception_ip_veer[i]),
        .trace_rv_i_ecause_ip(trace_rv_i_ecause_ip_veer[i]),
        .trace_rv_i_interrupt_ip(trace_rv_i_interrupt_ip_veer[i]),
        .trace_rv_i_tval_ip(trace_rv_i_tval_ip_veer[i]),
        .dccm_clk_override(dccm_clk_override_veer[i]),
        .icm_clk_override(icm_clk_override_veer[i]),
        .dec_tlu_core_ecc_disable(dec_tlu_core_ecc_disable_veer[i]),
        .i_cpu_halt_req(i_cpu_halt_req_veer[i]),
        .i_cpu_run_req(i_cpu_run_req_veer[i]),
        .o_cpu_halt_ack(o_cpu_halt_ack_veer[i]),
        .o_cpu_halt_status(o_cpu_halt_status_veer[i]),
        .o_cpu_run_ack(o_cpu_run_ack_veer[i]),
        .o_debug_mode_status(o_debug_mode_status_veer[i]),
        .core_id(core_id),
        .mpc_debug_halt_req(mpc_debug_halt_req_veer[i]),
        .mpc_debug_run_req(mpc_debug_run_req_veer[i]),
        .mpc_reset_run_req(mpc_reset_run_req_veer[i]),
        .mpc_debug_halt_ack(mpc_debug_halt_ack_veer[i]),
        .mpc_debug_run_ack(mpc_debug_run_ack_veer[i]),
        .debug_brkpt_status(debug_brkpt_status_veer[i]),
        .dec_tlu_perfcnt0(dec_tlu_perfcnt0_veer[i]),
        .dec_tlu_perfcnt1(dec_tlu_perfcnt1_veer[i]),
        .dec_tlu_perfcnt2(dec_tlu_perfcnt2_veer[i]),
        .dec_tlu_perfcnt3(dec_tlu_perfcnt3_veer[i]),
        .dccm_wren(dccm_wren_veer[i]),
        .dccm_rden(dccm_rden_veer[i]),
        .dccm_wr_addr_lo(dccm_wr_addr_lo_veer[i]),
        .dccm_wr_addr_hi(dccm_wr_addr_hi_veer[i]),
        .dccm_rd_addr_lo(dccm_rd_addr_lo_veer[i]),
        .dccm_rd_addr_hi(dccm_rd_addr_hi_veer[i]),
        .dccm_wr_data_lo(dccm_wr_data_lo_veer[i]),
        .dccm_wr_data_hi(dccm_wr_data_hi_veer[i]),
        .dccm_rd_data_lo(dccm_rd_data_lo_veer[i]),
        .dccm_rd_data_hi(dccm_rd_data_hi_veer[i]),
        .iccm_rw_addr(iccm_rw_addr_veer[i]),
        .iccm_wren(iccm_wren_veer[i]),
        .iccm_rden(iccm_rden_veer[i]),
        .iccm_wr_size(iccm_wr_size_veer[i]),
        .iccm_wr_data(iccm_wr_data_veer[i]),
        .iccm_buf_correct_ecc(iccm_buf_correct_ecc_veer[i]),
        .iccm_correction_state(iccm_correction_state_veer[i]),
        .iccm_rd_data_ecc(iccm_rd_data_ecc_veer[i]),
        .ic_rw_addr(ic_rw_addr_veer[i]),
        .ic_tag_valid(ic_tag_valid_veer[i]),
        .ic_wr_en(ic_wr_en_veer[i]),
        .ic_rd_en(ic_rd_en_veer[i]),
        .ic_wr_data(ic_wr_data_veer[i]),
        .ic_rd_data (ic_rd_data_veer[i]),
        .ic_rd_addr_lo(ic_rd_addr_lo_veer[i]),
        .ic_rd_bank_check_en(ic_rd_bank_check_en_veer[i]),
        .ic_debug_rd_data (ic_debug_rd_data_veer[i]),
        .ictag_debug_rd_data(ictag_debug_rd_data_veer[i]),
        .ic_debug_wr_data(ic_debug_wr_data_veer[i]),
        .ic_debug_addr(ic_debug_addr_veer[i]),
        .ic_debug_rd_en(ic_debug_rd_en_veer[i]),
        .ic_debug_wr_en(ic_debug_wr_en_veer[i]),
        .ic_debug_tag_array(ic_debug_tag_array_veer[i]),
        .ic_debug_way(ic_debug_way_veer[i]),
        .ic_rd_hit(ic_rd_hit_veer[i]),
        .ic_tag_perr(ic_tag_perr_veer[i]),
        .lsu_axi_awvalid(lsu_axi_awvalid_veer[i]),
        .lsu_axi_awready(lsu_axi_awready_veer[i]),
        .lsu_axi_awid(lsu_axi_awid_veer[i]),
        .lsu_axi_awaddr(lsu_axi_awaddr_veer[i]),
        .lsu_axi_awregion(lsu_axi_awregion_veer[i]),
        .lsu_axi_awlen(lsu_axi_awlen_veer[i]),
        .lsu_axi_awsize(lsu_axi_awsize_veer[i]),
        .lsu_axi_awburst(lsu_axi_awburst_veer[i]),
        .lsu_axi_awlock(lsu_axi_awlock_veer[i]),
        .lsu_axi_awcache(lsu_axi_awcache_veer[i]),
        .lsu_axi_awprot(lsu_axi_awprot_veer[i]),
        .lsu_axi_awqos(lsu_axi_awqos_veer[i]),
        .lsu_axi_wvalid(lsu_axi_wvalid_veer[i]),
        .lsu_axi_wready(lsu_axi_wready_veer[i]),
        .lsu_axi_wdata(lsu_axi_wdata_veer[i]),
        .lsu_axi_wstrb(lsu_axi_wstrb_veer[i]),
        .lsu_axi_wlast(lsu_axi_wlast_veer[i]),
        .lsu_axi_bvalid(lsu_axi_bvalid_veer[i]),
        .lsu_axi_bready(lsu_axi_bready_veer[i]),
        .lsu_axi_bresp(lsu_axi_bresp_veer[i]),
        .lsu_axi_bid(lsu_axi_bid_veer[i]),
        .lsu_axi_arvalid(lsu_axi_arvalid_veer[i]),
        .lsu_axi_arready(lsu_axi_arready_veer[i]),
        .lsu_axi_arid(lsu_axi_arid_veer[i]),
        .lsu_axi_araddr(lsu_axi_araddr_veer[i]),
        .lsu_axi_arregion(lsu_axi_arregion_veer[i]),
        .lsu_axi_arlen(lsu_axi_arlen_veer[i]),
        .lsu_axi_arsize(lsu_axi_arsize_veer[i]),
        .lsu_axi_arburst(lsu_axi_arburst_veer[i]),
        .lsu_axi_arlock(lsu_axi_arlock_veer[i]),
        .lsu_axi_arcache(lsu_axi_arcache_veer[i]),
        .lsu_axi_arprot(lsu_axi_arprot_veer[i]),
        .lsu_axi_arqos(lsu_axi_arqos_veer[i]),
        .lsu_axi_rvalid(lsu_axi_rvalid_veer[i]),
        .lsu_axi_rready(lsu_axi_rready_veer[i]),
        .lsu_axi_rid(lsu_axi_rid_veer[i]),
        .lsu_axi_rdata(lsu_axi_rdata_veer[i]),
        .lsu_axi_rresp(lsu_axi_rresp_veer[i]),
        .lsu_axi_rlast(lsu_axi_rlast_veer[i]),
        .ifu_axi_awvalid(ifu_axi_awvalid_veer[i]),
        .ifu_axi_awready(ifu_axi_awready_veer[i]),
        .ifu_axi_awid(ifu_axi_awid_veer[i]),
        .ifu_axi_awaddr(ifu_axi_awaddr_veer[i]),
        .ifu_axi_awregion(ifu_axi_awregion_veer[i]),
        .ifu_axi_awlen(ifu_axi_awlen_veer[i]),
        .ifu_axi_awsize(ifu_axi_awsize_veer[i]),
        .ifu_axi_awburst(ifu_axi_awburst_veer[i]),
        .ifu_axi_awlock(ifu_axi_awlock_veer[i]),
        .ifu_axi_awcache(ifu_axi_awcache_veer[i]),
        .ifu_axi_awprot(ifu_axi_awprot_veer[i]),
        .ifu_axi_awqos(ifu_axi_awqos_veer[i]),
        .ifu_axi_wvalid(ifu_axi_wvalid_veer[i]),
        .ifu_axi_wready(ifu_axi_wready_veer[i]),
        .ifu_axi_wdata(ifu_axi_wdata_veer[i]),
        .ifu_axi_wstrb(ifu_axi_wstrb_veer[i]),
        .ifu_axi_wlast(ifu_axi_wlast_veer[i]),
        .ifu_axi_bvalid(ifu_axi_bvalid_veer[i]),
        .ifu_axi_bready(ifu_axi_bready_veer[i]),
        .ifu_axi_bresp(ifu_axi_bresp_veer[i]),
        .ifu_axi_bid(ifu_axi_bid_veer[i]),
        .ifu_axi_arvalid(ifu_axi_arvalid_veer[i]),
        .ifu_axi_arready(ifu_axi_arready_veer[i]),
        .ifu_axi_arid(ifu_axi_arid_veer[i]),
        .ifu_axi_araddr(ifu_axi_araddr_veer[i]),
        .ifu_axi_arregion(ifu_axi_arregion_veer[i]),
        .ifu_axi_arlen(ifu_axi_arlen_veer[i]),
        .ifu_axi_arsize(ifu_axi_arsize_veer[i]),
        .ifu_axi_arburst(ifu_axi_arburst_veer[i]),
        .ifu_axi_arlock(ifu_axi_arlock_veer[i]),
        .ifu_axi_arcache(ifu_axi_arcache_veer[i]),
        .ifu_axi_arprot(ifu_axi_arprot_veer[i]),
        .ifu_axi_arqos(ifu_axi_arqos_veer[i]),
        .ifu_axi_rvalid(ifu_axi_rvalid_veer[i]),
        .ifu_axi_rready(ifu_axi_rready_veer[i]),
        .ifu_axi_rid(ifu_axi_rid_veer[i]),
        .ifu_axi_rdata(ifu_axi_rdata_veer[i]),
        .ifu_axi_rresp(ifu_axi_rresp_veer[i]),
        .ifu_axi_rlast(ifu_axi_rlast_veer[i]),
        .sb_axi_awvalid(sb_axi_awvalid_veer[i]),
        .sb_axi_awready(sb_axi_awready_veer[i]),
        .sb_axi_awid(sb_axi_awid_veer[i]),
        .sb_axi_awaddr(sb_axi_awaddr_veer[i]),
        .sb_axi_awregion(sb_axi_awregion_veer[i]),
        .sb_axi_awlen(sb_axi_awlen_veer[i]),
        .sb_axi_awsize(sb_axi_awsize_veer[i]),
        .sb_axi_awburst(sb_axi_awburst_veer[i]),
        .sb_axi_awlock(sb_axi_awlock_veer[i]),
        .sb_axi_awcache(sb_axi_awcache_veer[i]),
        .sb_axi_awprot(sb_axi_awprot_veer[i]),
        .sb_axi_awqos(sb_axi_awqos_veer[i]),
        .sb_axi_wvalid(sb_axi_wvalid_veer[i]),
        .sb_axi_wready(sb_axi_wready_veer[i]),
        .sb_axi_wdata(sb_axi_wdata_veer[i]),
        .sb_axi_wstrb(sb_axi_wstrb_veer[i]),
        .sb_axi_wlast(sb_axi_wlast_veer[i]),
        .sb_axi_bvalid(sb_axi_bvalid_veer[i]),
        .sb_axi_bready(sb_axi_bready_veer[i]),
        .sb_axi_bresp(sb_axi_bresp_veer[i]),
        .sb_axi_bid(sb_axi_bid_veer[i]),
        .sb_axi_arvalid(sb_axi_arvalid_veer[i]),
        .sb_axi_arready(sb_axi_arready_veer[i]),
        .sb_axi_arid(sb_axi_arid_veer[i]),
        .sb_axi_araddr(sb_axi_araddr_veer[i]),
        .sb_axi_arregion(sb_axi_arregion_veer[i]),
        .sb_axi_arlen(sb_axi_arlen_veer[i]),
        .sb_axi_arsize(sb_axi_arsize_veer[i]),
        .sb_axi_arburst(sb_axi_arburst_veer[i]),
        .sb_axi_arlock(sb_axi_arlock_veer[i]),
        .sb_axi_arcache(sb_axi_arcache_veer[i]),
        .sb_axi_arprot(sb_axi_arprot_veer[i]),
        .sb_axi_arqos(sb_axi_arqos_veer[i]),
        .sb_axi_rvalid(sb_axi_rvalid_veer[i]),
        .sb_axi_rready(sb_axi_rready_veer[i]),
        .sb_axi_rid(sb_axi_rid_veer[i]),
        .sb_axi_rdata(sb_axi_rdata_veer[i]),
        .sb_axi_rresp(sb_axi_rresp_veer[i]),
        .sb_axi_rlast(sb_axi_rlast_veer[i]),
        .dma_axi_awvalid(dma_axi_awvalid_veer[i]),
        .dma_axi_awready(dma_axi_awready_veer[i]),
        .dma_axi_awid(dma_axi_awid_veer[i]),
        .dma_axi_awaddr(dma_axi_awaddr_veer[i]),
        .dma_axi_awsize(dma_axi_awsize_veer[i]),
        .dma_axi_awprot(dma_axi_awprot_veer[i]),
        .dma_axi_awlen(dma_axi_awlen_veer[i]),
        .dma_axi_awburst(dma_axi_awburst_veer[i]),
        .dma_axi_wvalid(dma_axi_wvalid_veer[i]),
        .dma_axi_wready(dma_axi_wready_veer[i]),
        .dma_axi_wdata(dma_axi_wdata_veer[i]),
        .dma_axi_wstrb(dma_axi_wstrb_veer[i]),
        .dma_axi_wlast(dma_axi_wlast_veer[i]),
        .dma_axi_bvalid(dma_axi_bvalid_veer[i]),
        .dma_axi_bready(dma_axi_bready_veer[i]),
        .dma_axi_bresp(dma_axi_bresp_veer[i]),
        .dma_axi_bid(dma_axi_bid_veer[i]),
        .dma_axi_arvalid(dma_axi_arvalid_veer[i]),
        .dma_axi_arready(dma_axi_arready_veer[i]),
        .dma_axi_arid(dma_axi_arid_veer[i]),
        .dma_axi_araddr(dma_axi_araddr_veer[i]),
        .dma_axi_arsize(dma_axi_arsize_veer[i]),
        .dma_axi_arprot(dma_axi_arprot_veer[i]),
        .dma_axi_arlen(dma_axi_arlen_veer[i]),
        .dma_axi_arburst(dma_axi_arburst_veer[i]),
        .dma_axi_rvalid(dma_axi_rvalid_veer[i]),
        .dma_axi_rready(dma_axi_rready_veer[i]),
        .dma_axi_rid(dma_axi_rid_veer[i]),
        .dma_axi_rdata(dma_axi_rdata_veer[i]),
        .dma_axi_rresp(dma_axi_rresp_veer[i]),
        .dma_axi_rlast(dma_axi_rlast_veer[i]),
        .lsu_bus_clk_en(lsu_bus_clk_en_veer[i]),
        .ifu_bus_clk_en(ifu_bus_clk_en_veer[i]),
        .dbg_bus_clk_en(dbg_bus_clk_en_veer[i]),
        .dma_bus_clk_en(dma_bus_clk_en_veer[i]),
        .dmi_reg_en(dmi_reg_en_veer[i]),
        .dmi_reg_addr(dmi_reg_addr_veer[i]),
        .dmi_reg_wr_en(dmi_reg_wr_en_veer[i]),
        .dmi_reg_wdata(dmi_reg_wdata_veer[i]),
        .dmi_reg_rdata(dmi_reg_rdata_veer[i]),
        .iccm_ecc_single_error(iccm_ecc_single_error_veer[i]),
        .iccm_ecc_double_error(iccm_ecc_double_error_veer[i]),
        .dccm_ecc_single_error(dccm_ecc_single_error_veer[i]),
        .dccm_ecc_double_error(dccm_ecc_double_error_veer[i]),
        .dccm_write_readback_error(dccm_write_readback_error),
        .recovery_gpr_en(recovery_gpr_en_veer[i]),
        .recovery_gpr_wen(recovery_gpr_wen_veer[i]),
        .recovery_gpr_wraddr(recovery_gpr_wraddr_veer[i]),
        .recovery_gpr_wrdata(recovery_gpr_wrdata_veer[i]),
        .recovery_gpr_rdaddr(recovery_gpr_rdaddr_veer[i]),
        .recovery_gpr_rddata(recovery_gpr_rddata_veer[i]),
        .recovery_csr_en(recovery_csr_en_veer[i]),
        .recovery_csr_wen(recovery_csr_wen_veer[i]),
        .recovery_csr_wraddr(recovery_csr_wraddr_veer[i]),
        .recovery_csr_wrdata(recovery_csr_wrdata_veer[i]),
        .recovery_csr_rdaddr(recovery_csr_rdaddr_veer[i]),
        .recovery_csr_rddata(recovery_csr_rddata_veer[i]),
        .dec_tlu_force_halt(dec_tlu_force_halt_veer[i]),
        .dec_tlu_bus_clk_override(dec_tlu_bus_clk_override_veer[i]),
        .dec_tlu_dccm_wr_readback_disable(dec_tlu_dccm_wr_readback_disable),
        .pic_clk_override(pic_clk_override_veer[i]),
        .pic_io_clk_override(pic_io_clk_override_veer[i]),
        .picm_rdaddr(picm_rdaddr_veer[i]),
        .picm_wraddr(picm_wraddr_veer[i]),
        .picm_wr_data(picm_wr_data_veer[i]),
        .picm_wren(picm_wren_veer[i]),
        .picm_rden(picm_rden_veer[i]),
        .picm_mken(picm_mken_veer[i]),
        .dec_tlu_meicurpl(meicurpl_veer[i]),
        .dec_tlu_meipt(meipt_veer[i]),
        .mexintpend(mexintpend_veer[i]),
        .pic_pl(pic_pl_veer[i]),
        .pic_claimid(pic_claimid_veer[i]),
        .picm_rd_data(picm_rd_data_veer[i]),
        .mhwakeup(mhwakeup_veer[i]),
        .timer_int(timer_int_veer[i]),
        .soft_int(soft_int_veer[i]),
        .scan_mode(scan_mode)
      );
  end

  // Common PIC for all the VeeRs instances
  el2_pic_ctrl  #(.pt(pt)) pic_ctrl_inst (
    .clk(free_l2clk),
    .free_clk(free_clk_int),
    .clk_override(pic_clk_override_int),
    .io_clk_override(pic_io_clk_override_int),
    .picm_rdaddr(picm_rdaddr_int),
    .picm_wraddr(picm_wraddr_int),
    .picm_wr_data(picm_wr_data_int),
    .picm_wren(picm_wren_int),
    .picm_rden(picm_rden_int),
    .picm_rd_data(picm_rd_data_int),
    .picm_mken(picm_mken_int),
    .mexintpend(mexintpend_int),
    .mhwakeup(mhwakeup_int),
    .extintsrc_req({extintsrc_req[pt.PIC_TOTAL_INT:1],1'b0}),
    .pl(pic_pl_int[3:0]),
    .claimid(pic_claimid_int[7:0]),
    .meicurpl(meicurpl_int[3:0]),
    .meipt(meipt_int[3:0]),
    .rst_l(core_rst_l),
    .*
  );
endmodule
`endif
