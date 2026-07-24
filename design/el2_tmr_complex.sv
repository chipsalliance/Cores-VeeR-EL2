// Copyright 2026 Antmicro <www.antmicro.com>
// //
// // SPDX-License-Identifier: Apache-2.0
//
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

    input  logic [63:0]                 iccm_rd_data,
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

    output logic [63:0]                          ic_premux_data,     // Premux data to be muxed with each way of the Icache.
    output logic                                 ic_sel_premux_data, // Select premux data

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

    // DMI to the core with invalid state
    input  logic        broken_core_dmi_reg_en,                // read or write
    input  logic [6:0]  broken_core_dmi_reg_addr,              // address of DM register
    input  logic        broken_core_dmi_reg_wr_en,             // write instruction
    input  logic [31:0] broken_core_dmi_reg_wdata,             // write data
    output logic [31:0] broken_core_dmi_reg_rdata,

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
  logic       core_rst_l_veer[3];
  logic       active_state_veer[3];
  logic       dec_tlu_force_halt_veer[3];
  logic [31:0] rst_vec_veer[3];
  logic        nmi_int_veer[3];
  logic [31:0] nmi_vec_veer[3];

  logic [31:0] trace_rv_i_insn_ip_veer[3];
  logic [31:0] trace_rv_i_address_ip_veer[3];
  logic        trace_rv_i_valid_ip_veer[3];
  logic        trace_rv_i_exception_ip_veer[3];
  logic [4:0]  trace_rv_i_ecause_ip_veer[3];
  logic        trace_rv_i_interrupt_ip_veer[3];
  logic [31:0] trace_rv_i_tval_ip_veer[3];


  logic dec_tlu_bus_clk_override_veer[3];
  logic dec_tlu_pic_clk_override_veer[3];
  logic dec_tlu_picio_clk_override_veer[3];
  logic dccm_clk_override_veer[3];
  logic icm_clk_override_veer[3];

  logic dec_tlu_core_ecc_disable_veer[3];

  logic o_cpu_halt_ack_veer[3];
  logic o_cpu_halt_status_veer[3];
  logic o_cpu_run_ack_veer[3];
  logic o_debug_mode_status_veer[3];

  logic        picm_wren_veer[3];
  logic        picm_rden_veer[3];
  logic        picm_mken_veer[3];
  logic [31:0] picm_rdaddr_veer[3];
  logic [31:0] picm_wraddr_veer[3];
  logic [31:0] picm_wr_data_veer[3];
  logic [31:0] picm_rd_data_veer[3];
  logic [7:0]  pic_claimid_veer[3];
  logic [3:0]  pic_pl_veer[3], dec_tlu_meicurpl_veer[3], dec_tlu_meipt_veer[3];
  logic        mexintpend_veer[3];
  logic        mhwakeup_veer[3];

  // external MPC halt/run interface
  logic mpc_debug_halt_ack_veer[3];
  logic mpc_debug_run_ack_veer[3];
  logic debug_brkpt_status_veer[3];
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
  logic [63:0]             iccm_rd_data_veer[3];
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

  logic [63:0]                          ic_premux_data_veer[3];
  logic                                 ic_sel_premux_data_veer[3];

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

  // Cores Buses post TMR
  logic free_clk;
  logic active_clk;
  logic dec_tlu_bus_clk_override_int;
  logic active_state_int;
  logic dec_tlu_force_halt_int;
  logic dec_tlu_pic_clk_override_int;
  logic dec_tlu_picio_clk_override_int;

  // PIC ports
  logic        picm_wren_int;
  logic        picm_rden_int;
  logic        picm_mken_int;
  logic [31:0] picm_rdaddr_int;
  logic [31:0] picm_wraddr_int;
  logic [31:0] picm_wr_data_int;
  logic [31:0] picm_rd_data_int;
  logic [7:0]  pic_claimid_int;
  logic [3:0]  pic_pl_int, dec_tlu_meicurpl_int, dec_tlu_meipt_int;
  logic        mexintpend_int;
  logic        mhwakeup_int;


  //TODO: Change it to use voters

  always_comb begin
    // Propagate response to Cores
    for (int i=0;i < 3; i+=1) begin
      rst_vec_veer[i] = rst_vec;
      nmi_int_veer[i] = nmi_int;
      nmi_vec_veer[i] = nmi_vec;
      lsu_bus_clk_en_veer[i] = lsu_bus_clk_en;
      ifu_bus_clk_en_veer[i] = ifu_bus_clk_en;
      dbg_bus_clk_en_veer[i] = dbg_bus_clk_en;
      dma_bus_clk_en_veer[i] = dma_bus_clk_en;

      dmi_reg_en_veer[i] = dmi_reg_en;
      dmi_reg_addr_veer[i] = dmi_reg_addr;
      dmi_reg_wr_en_veer[i] = dmi_reg_wr_en;
      dmi_reg_wdata_veer[i] = dmi_reg_wdata;

      picm_rd_data_veer[i] = picm_rd_data_int;
      pic_claimid_veer[i] = pic_claimid_int;
      pic_pl_veer[i] = pic_pl_int;
      mexintpend_veer[i] = mexintpend_int;
      mhwakeup_veer[i] = mhwakeup_int;
    end
    // Get value from Core 0 for the time being
    core_rst_l = core_rst_l_veer[0];
    dec_tlu_bus_clk_override_int = dec_tlu_bus_clk_override_veer[0];
    dec_tlu_pic_clk_override_int = dec_tlu_pic_clk_override_veer[0];
    dec_tlu_picio_clk_override_int = dec_tlu_picio_clk_override_veer[0];

    trace_rv_i_insn_ip = trace_rv_i_insn_ip_veer[0];
    trace_rv_i_address_ip = trace_rv_i_address_ip_veer[0];
    trace_rv_i_valid_ip = trace_rv_i_valid_ip_veer[0];
    trace_rv_i_exception_ip = trace_rv_i_exception_ip_veer[0];
    trace_rv_i_ecause_ip = trace_rv_i_ecause_ip_veer[0];
    trace_rv_i_interrupt_ip = trace_rv_i_interrupt_ip_veer[0];
    trace_rv_i_tval_ip = trace_rv_i_tval_ip_veer[0];

    dccm_clk_override = dccm_clk_override_veer[0];
    icm_clk_override = icm_clk_override_veer[0];
    dec_tlu_core_ecc_disable = dec_tlu_core_ecc_disable_veer[0];

    o_cpu_halt_ack = o_cpu_halt_ack_veer[0];
    o_cpu_halt_status = o_cpu_halt_status_veer[0];
    o_cpu_run_ack = o_cpu_run_ack_veer[0];
    o_debug_mode_status = o_debug_mode_status_veer[0];

    mpc_debug_halt_ack = mpc_debug_halt_ack_veer[0];
    mpc_debug_run_ack = mpc_debug_run_ack_veer[0];
    debug_brkpt_status = debug_brkpt_status_veer[0];

    dec_tlu_perfcnt0 = dec_tlu_perfcnt0_veer[0];
    dec_tlu_perfcnt1 = dec_tlu_perfcnt1_veer[0];
    dec_tlu_perfcnt2 = dec_tlu_perfcnt2_veer[0];
    dec_tlu_perfcnt3 = dec_tlu_perfcnt3_veer[0];

    dmi_reg_rdata = dmi_reg_rdata_veer[0];
    active_state_int  = active_state_veer[0];
    dec_tlu_force_halt_int  = dec_tlu_force_halt_veer[0];
    picm_wren_int    = picm_wren_veer[0];
    picm_rden_int    = picm_rden_veer[0];
    picm_mken_int    = picm_mken_veer[0];
    picm_rdaddr_int  = picm_rdaddr_veer[0];
    picm_wraddr_int  = picm_wraddr_veer[0];
    picm_wr_data_int = picm_wr_data_veer[0];
    dec_tlu_meicurpl_int = dec_tlu_meicurpl_veer[0];
    dec_tlu_meipt_int = dec_tlu_meipt_veer[0];
  end
  el2_tmr_axi #(.pt(pt)) el2_tmr_axi_u (.*);
  el2_tmr_iccm #(.pt(pt)) el2_tmr_iccm_u (.*);
  el2_tmr_dccm #(.pt(pt)) el2_tmr_dccm_u (.*);
  el2_tmr_ic #(.pt(pt)) el2_tmr_ic_u (.*);
  el2_tmr_complex_io el2_tmr_complex_io_u(.*);

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

  rvoclkhdr free_cg2   ( .clk(clk), .en(1'b1),         .l1clk(free_l2clk), .* );
  rvoclkhdr active_cg2 ( .clk(clk), .en(active_state_int), .l1clk(active_l2clk), .* );

  //  all other clock headers are 1st level
  rvoclkhdr free_cg1   ( .clk(free_l2clk),     .en(1'b1), .l1clk(free_clk), .* );
  rvoclkhdr active_cg1 ( .clk(active_l2clk),   .en(1'b1), .l1clk(active_clk), .* );

  for (genvar i=0;i < 3; i+=1) begin: cores
    //----------------------------------------------------------------------
    //
    //----------------------------------------------------------------------
    logic                         ifu_pmu_instr_aligned;
    logic                         ifu_ic_error_start;
    logic                         ifu_iccm_dma_rd_ecc_single_err;
    logic                         ifu_iccm_rd_ecc_single_err;
    logic                         ifu_iccm_rd_ecc_double_err;
    logic                         lsu_dccm_rd_ecc_single_err;
    logic                         lsu_dccm_rd_ecc_double_err;
    //  Icache debug
    logic [70:0] ifu_ic_debug_rd_data; // diagnostic icache read data
    logic ifu_ic_debug_rd_data_valid; // diagnostic icache read data valid
    el2_cache_debug_pkt_t dec_tlu_ic_diag_pkt; // packet of DICAWICS, DICAD0/1, DICAGO info for icache diagnostics
    logic         dec_i0_rs1_en_d;
    logic         dec_i0_rs2_en_d;
    logic  [31:0] gpr_i0_rs1_d;
    logic  [31:0] gpr_i0_rs2_d;

    logic [31:0] dec_i0_result_r;
    logic [31:0] exu_i0_result_x;
    logic [31:1] exu_i0_pc_x;
    logic [31:1] exu_npc_r;
    el2_alu_pkt_t  i0_ap;
    // Trigger signals
    el2_trigger_pkt_t [3:0]     trigger_pkt_any;
    logic [3:0]             lsu_trigger_match_m;
    logic [31:0] dec_i0_immed_d;
    logic [12:1] dec_i0_br_immed_d;
    logic         dec_i0_select_pc_d;
    logic [31:1] dec_i0_pc_d;
    logic [3:0]  dec_i0_rs1_bypass_en_d;
    logic [3:0]  dec_i0_rs2_bypass_en_d;
    logic         dec_i0_alu_decode_d;
    logic         dec_i0_branch_d;
    logic         ifu_miss_state_idle;
    logic         dec_tlu_flush_noredir_r;
    logic         dec_tlu_flush_leak_one_r;
    logic         dec_tlu_flush_err_r;
    logic         ifu_i0_valid;
    logic [31:0]  ifu_i0_instr;
    logic [31:1]  ifu_i0_pc;
    logic        exu_flush_final;
    logic [31:1] exu_flush_path_final;
    logic [31:0] exu_lsu_rs1_d;
    logic [31:0] exu_lsu_rs2_d;
    el2_lsu_pkt_t    lsu_p;
    logic             dec_qual_lsu_d;
    logic        dec_lsu_valid_raw_d;
    logic [11:0] dec_lsu_offset_d;
    logic [31:0]  lsu_result_m;
    logic [31:0]  lsu_result_corr_r;     // This is the ECC corrected data going to RF
    logic         lsu_single_ecc_error_incr;     // Increment the ecc counter
    el2_lsu_error_pkt_t lsu_error_pkt_r;
    logic         lsu_imprecise_error_load_any;
    logic         lsu_imprecise_error_store_any;
    logic [31:0]  lsu_imprecise_error_addr_any;
    logic         lsu_load_stall_any;       // This is for blocking loads
    logic         lsu_store_stall_any;      // This is for blocking stores
    logic         lsu_idle_any;             // doesn't include DMA
    logic         lsu_active;               // lsu is active. used for clock
    logic [31:1]  lsu_fir_addr;        // fast interrupt address
    logic [1:0]   lsu_fir_error;       // Error during fast interrupt lookup
    // Non-blocking loads
    logic                                 lsu_nonblock_load_valid_m;
    logic [pt.LSU_NUM_NBLOAD_WIDTH-1:0]   lsu_nonblock_load_tag_m;
    logic                                 lsu_nonblock_load_inv_r;
    logic [pt.LSU_NUM_NBLOAD_WIDTH-1:0]   lsu_nonblock_load_inv_tag_r;
    logic                                 lsu_nonblock_load_data_valid;
    logic [pt.LSU_NUM_NBLOAD_WIDTH-1:0]   lsu_nonblock_load_data_tag;
    logic [31:0]                          lsu_nonblock_load_data;
    logic        dec_csr_ren_d;
    logic [31:0] dec_csr_rddata_d;
    logic [31:0] exu_csr_rs1_x;
    logic        dec_tlu_i0_commit_cmt;
    logic        dec_tlu_flush_lower_r;
    logic        dec_tlu_flush_lower_wb;
    logic        dec_tlu_i0_kill_writeb_r;     // I0 is flushed, don't writeback any results to arch state
    logic        dec_tlu_fence_i_r;            // flush is a fence_i rfnpc, flush icache
    logic [31:1] dec_tlu_flush_path_r;
    logic [31:0] dec_tlu_mrac_ff;        // CSR for memory region control
    logic        ifu_i0_pc4;
    el2_mul_pkt_t  mul_p;
    el2_div_pkt_t  div_p;
    logic           dec_div_cancel;
    logic [31:0] exu_div_result;
    logic exu_div_wren;
    logic dec_i0_decode_d;
    logic [31:1] pred_correct_npc_x;
    el2_br_tlu_pkt_t dec_tlu_br0_r_pkt;
    el2_predict_pkt_t  exu_mp_pkt;
    logic [pt.BHT_GHR_SIZE-1:0]  exu_mp_eghr;
    logic [pt.BHT_GHR_SIZE-1:0]  exu_mp_fghr;
    logic [pt.BTB_ADDR_HI:pt.BTB_ADDR_LO] exu_mp_index;
    logic [pt.BTB_BTAG_SIZE-1:0]          exu_mp_btag;
    logic [pt.BHT_GHR_SIZE-1:0]  exu_i0_br_fghr_r;
    logic [1:0]  exu_i0_br_hist_r;
    logic        exu_i0_br_error_r;
    logic        exu_i0_br_start_error_r;
    logic        exu_i0_br_valid_r;
    logic        exu_i0_br_mp_r;
    logic        exu_i0_br_middle_r;
    logic        exu_i0_br_way_r;
    logic [pt.BTB_ADDR_HI:pt.BTB_ADDR_LO] exu_i0_br_index_r;
    logic        dma_dccm_req;
    logic        dma_iccm_req;
    logic [2:0]  dma_mem_tag;
    logic [31:0] dma_mem_addr;
    logic [2:0]  dma_mem_sz;
    logic        dma_mem_write;
    logic [63:0] dma_mem_wdata;
    logic        dccm_dma_rvalid;
    logic        dccm_dma_ecc_error;
    logic [2:0]  dccm_dma_rtag;
    logic [63:0] dccm_dma_rdata;
    logic        iccm_dma_rvalid;
    logic        iccm_dma_ecc_error;
    logic [2:0]  iccm_dma_rtag;
    logic [63:0] iccm_dma_rdata;
    logic        dma_dccm_stall_any;       // Stall the ld/st in decode if asserted
    logic        dma_iccm_stall_any;       // Stall the fetch
    logic        dccm_ready;
    logic        iccm_ready;
    logic        dma_pmu_dccm_read;
    logic        dma_pmu_dccm_write;
    logic        dma_pmu_any_read;
    logic        dma_pmu_any_write;
    logic        ifu_i0_icaf;
    logic [1:0]  ifu_i0_icaf_type;
    logic        ifu_i0_icaf_second;
    logic        ifu_i0_dbecc;
    logic        iccm_dma_sb_error;
    el2_br_pkt_t i0_brp;
    logic [pt.BTB_ADDR_HI:pt.BTB_ADDR_LO] ifu_i0_bp_index;
    logic [pt.BHT_GHR_SIZE-1:0] ifu_i0_bp_fghr;
    logic [pt.BTB_BTAG_SIZE-1:0] ifu_i0_bp_btag;
    logic [$clog2(pt.BTB_SIZE)-1:0] ifu_i0_fa_index;
    logic [$clog2(pt.BTB_SIZE)-1:0] dec_fa_error_index; // Fully associative btb error index
    el2_predict_pkt_t dec_i0_predict_p_d;
    logic [pt.BHT_GHR_SIZE-1:0] i0_predict_fghr_d;                // DEC predict fghr
    logic [pt.BTB_ADDR_HI:pt.BTB_ADDR_LO] i0_predict_index_d;     // DEC predict index
    logic [pt.BTB_BTAG_SIZE-1:0] i0_predict_btag_d;               // DEC predict branch tag
    // feature disable from mfdc
    logic  dec_tlu_external_ldfwd_disable; // disable external load forwarding
    logic  dec_tlu_bpred_disable;
    logic  dec_tlu_wb_coalescing_disable;
    logic  dec_tlu_sideeffect_posted_disable;
    logic [2:0] dec_tlu_dma_qos_prty;         // DMA QoS priority coming from MFDC [18:16]
    // clock gating overrides from mcgc
    logic  dec_tlu_misc_clk_override;
    logic  dec_tlu_ifu_clk_override;
    logic  dec_tlu_lsu_clk_override;
    logic  dec_tlu_dccm_clk_override;
    logic  dec_tlu_icm_clk_override;
    assign        dccm_clk_override_veer[i] = dec_tlu_dccm_clk_override;   // dccm memory
    assign        icm_clk_override_veer[i] = dec_tlu_icm_clk_override;    // icache/iccm memory
    // PMP Signals
    el2_pmp_cfg_pkt_t       pmp_pmpcfg  [pt.PMP_ENTRIES];
    logic [31:0]            pmp_pmpaddr [pt.PMP_ENTRIES];
    logic [31:0]            pmp_chan_addr [3];
    el2_pmp_type_pkt_t      pmp_chan_type [3];
    logic                   pmp_chan_err  [3];
    logic [31:1] ifu_pmp_addr;
    logic        ifu_pmp_error;
    logic [31:0] lsu_pmp_addr_start;
    logic        lsu_pmp_error_start;
    logic [31:0] lsu_pmp_addr_end;
    logic        lsu_pmp_error_end;
    logic        lsu_pmp_we;
    logic        lsu_pmp_re;
    // -----------------------DEBUG  START -------------------------------
    logic [31:0]            dbg_cmd_addr;              // the address of the debug command to used by the core
    logic [31:0]            dbg_cmd_wrdata;            // If the debug command is a write command, this has the data to be written to the CSR/GPR
    logic                   dbg_cmd_valid;             // commad is being driven by the dbg module. One pulse. Only dirven when core_halted has been seen
    logic                   dbg_cmd_write;             // 1: write command; 0: read_command
    logic [1:0]             dbg_cmd_type;              // 0:gpr 1:csr 2: memory
    logic [1:0]             dbg_cmd_size;              // size of the abstract mem access debug command
    logic                   dbg_halt_req;              // Sticky signal indicating that the debug module wants to start the entering of debug mode ( start the halting sequence )
    logic                   dbg_resume_req;            // Sticky signal indicating that the debug module wants to resume from debug mode
    logic                   dbg_core_rst_l;            // Core reset from DM
    logic                   core_dbg_cmd_done;         // Final muxed cmd done to debug
    logic                   core_dbg_cmd_fail;         // Final muxed cmd done to debug
    logic [31:0]            core_dbg_rddata;           // Final muxed cmd done to debug
    logic                   dma_dbg_cmd_done;          // Abstarct memory command sent to dma is done
    logic                   dma_dbg_cmd_fail;          // Abstarct memory command sent to dma failed
    logic [31:0]            dma_dbg_rddata;            // Read data for abstract memory access
    logic                   dbg_dma_bubble;            // Debug needs a bubble to send a valid
    logic                   dma_dbg_ready;             // DMA is ready to accept debug request
    logic [31:0]            dec_dbg_rddata;            // The core drives this data ( intercepts the pipe and sends it here )
    logic                   dec_dbg_cmd_done;          // This will be treated like a valid signal
    logic                   dec_dbg_cmd_fail;          // Abstract command failed
    logic                   dec_tlu_mpc_halted_only;   // Only halted due to MPC
    logic                   dec_tlu_dbg_halted;        // The core has finished the queiscing sequence. Sticks this signal high
    logic                   dec_tlu_resume_ack;
    logic                   dec_tlu_debug_mode;        // Core is in debug mode
    logic                   dec_debug_wdata_rs1_d;
    logic [1:0]             dec_data_en;
    logic [1:0]             dec_ctl_en;
    // PMU Signals
    logic                   exu_pmu_i0_br_misp;
    logic                   exu_pmu_i0_br_ataken;
    logic                   exu_pmu_i0_pc4;
    logic                   lsu_pmu_load_external_m;
    logic                   lsu_pmu_store_external_m;
    logic                   lsu_pmu_misaligned_m;
    logic                   lsu_pmu_bus_trxn;
    logic                   lsu_pmu_bus_misaligned;
    logic                   lsu_pmu_bus_error;
    logic                   lsu_pmu_bus_busy;
    logic                   ifu_pmu_fetch_stall;
    logic                   ifu_pmu_ic_miss;
    logic                   ifu_pmu_ic_hit;
    logic                   ifu_pmu_bus_error;
    logic                   ifu_pmu_bus_busy;
    logic                   ifu_pmu_bus_trxn;
    logic                   dec_pause_state_cg;
    logic                   lsu_nonblock_load_data_error;
    logic [15:0]            ifu_i0_cinst;
    //  fast interrupt
    logic [31:2]            dec_tlu_meihap;
    logic                   dec_extint_stall;
    el2_trace_pkt_t  trace_rv_trace_pkt;
    logic                   lsu_fastint_stall_any;
    logic        dma_active;
    logic        pause_state;
    logic        halt_state;
    logic        dec_tlu_core_empty;
    assign pause_state = dec_pause_state_cg & ~(dma_active | lsu_active) & dec_tlu_core_empty;
    assign halt_state = o_cpu_halt_status_veer[i] & ~(dma_active | lsu_active);
    assign active_state_veer[i] = (~(halt_state | pause_state) | dec_tlu_flush_lower_r | dec_tlu_flush_lower_wb)  | dec_tlu_misc_clk_override;
    assign core_dbg_cmd_done = dma_dbg_cmd_done | dec_dbg_cmd_done;
    assign core_dbg_cmd_fail = dma_dbg_cmd_fail | dec_dbg_cmd_fail;
    assign core_dbg_rddata[31:0] = dma_dbg_cmd_done ? dma_dbg_rddata[31:0] : dec_dbg_rddata[31:0];
    el2_dbg #(.pt(pt)) dbg (
      .rst_l(core_rst_l_veer[i]),
      .clk(free_l2clk),
      .clk_override(dec_tlu_misc_clk_override),
      .dbg_bus_clk_en(dbg_bus_clk_en_veer[i]),

      // AXI signals
      .sb_axi_awvalid(sb_axi_awvalid_veer[i]),
      .sb_axi_awready(sb_axi_awready_veer[i]),
      .sb_axi_awid(sb_axi_awid_veer[i][pt.SB_BUS_TAG-1:0]),
      .sb_axi_awaddr(sb_axi_awaddr_veer[i][31:0]),
      .sb_axi_awregion(sb_axi_awregion_veer[i][3:0]),
      .sb_axi_awlen(sb_axi_awlen_veer[i][7:0]),
      .sb_axi_awsize(sb_axi_awsize_veer[i][2:0]),
      .sb_axi_awburst(sb_axi_awburst_veer[i][1:0]),
      .sb_axi_awlock(sb_axi_awlock_veer[i]),
      .sb_axi_awcache(sb_axi_awcache_veer[i][3:0]),
      .sb_axi_awprot(sb_axi_awprot_veer[i][2:0]),
      .sb_axi_awqos(sb_axi_awqos_veer[i][3:0]),
      .sb_axi_wvalid(sb_axi_wvalid_veer[i]),
      .sb_axi_wready(sb_axi_wready_veer[i]),
      .sb_axi_wdata(sb_axi_wdata_veer[i][63:0]),
      .sb_axi_wstrb(sb_axi_wstrb_veer[i][7:0]),
      .sb_axi_wlast(sb_axi_wlast_veer[i]),
      .sb_axi_bvalid(sb_axi_bvalid_veer[i]),
      .sb_axi_bready(sb_axi_bready_veer[i]),
      .sb_axi_bresp(sb_axi_bresp_veer[i][1:0]),

      .sb_axi_arvalid(sb_axi_arvalid_veer[i]),
      .sb_axi_arready(sb_axi_arready_veer[i]),
      .sb_axi_arid(sb_axi_arid_veer[i][pt.SB_BUS_TAG-1:0]),
      .sb_axi_araddr(sb_axi_araddr_veer[i][31:0]),
      .sb_axi_arregion(sb_axi_arregion_veer[i][3:0]),
      .sb_axi_arlen(sb_axi_arlen_veer[i][7:0]),
      .sb_axi_arsize(sb_axi_arsize_veer[i][2:0]),
      .sb_axi_arburst(sb_axi_arburst_veer[i][1:0]),
      .sb_axi_arlock(sb_axi_arlock_veer[i]),
      .sb_axi_arcache(sb_axi_arcache_veer[i][3:0]),
      .sb_axi_arprot(sb_axi_arprot_veer[i][2:0]),
      .sb_axi_arqos(sb_axi_arqos_veer[i][3:0]),
      .sb_axi_rvalid(sb_axi_rvalid_veer[i]),
      .sb_axi_rready(sb_axi_rready_veer[i]),
      .sb_axi_rdata(sb_axi_rdata_veer[i][63:0]),
      .sb_axi_rresp(sb_axi_rresp_veer[i][1:0]),

      .dmi_reg_en(dmi_reg_en_veer[i]),
      .dmi_reg_addr(dmi_reg_addr_veer[i]),
      .dmi_reg_wr_en(dmi_reg_wr_en_veer[i]),
      .dmi_reg_wdata(dmi_reg_wdata_veer[i]),
      .dmi_reg_rdata(dmi_reg_rdata_veer[i]),
      .*
    );

`ifdef RV_ASSERT_ON
    assert_fetch_indbghalt: assert #0 (~(ifu.ifc_fetch_req_f & dec.tlu.dbg_tlu_halted_f & ~dec.tlu.dcsr_single_step_running))
    else $display("ERROR: Fetching in dBG halt!");
`endif

   // -----------------   DEBUG END -----------------------------
   assign core_rst_l_veer[i] = rst_l & (dbg_core_rst_l | scan_mode);
`ifdef RV_USER_MODE
   // Operating privilege mode, 0 - machine, 1 - user
   logic priv_mode;
   // Effective privilege mode, 0 - machine, 1 - user (driven in el2_dec_tlu_ctl.sv)
   logic priv_mode_eff;
   // Next privilege mode
   logic priv_mode_ns;

   el2_mseccfg_pkt_t mseccfg; // mseccfg CSR for PMP
`endif

   // fetch
   el2_ifu #(.pt(pt)) ifu (
      .clk(active_l2clk),
      .rst_l(core_rst_l_veer[i]),
      .dec_tlu_flush_err_wb       (dec_tlu_flush_err_r      ),
      .dec_tlu_flush_noredir_wb   (dec_tlu_flush_noredir_r  ),
      .dec_tlu_fence_i_wb         (dec_tlu_fence_i_r        ),
      .dec_tlu_flush_leak_one_wb  (dec_tlu_flush_leak_one_r ),
      .dec_tlu_flush_lower_wb     (dec_tlu_flush_lower_r    ),

      // AXI signals
      .ifu_axi_awvalid(ifu_axi_awvalid_veer[i]),
      .ifu_axi_awid(ifu_axi_awid_veer[i][pt.IFU_BUS_TAG-1:0]),
      .ifu_axi_awaddr(ifu_axi_awaddr_veer[i][31:0]),
      .ifu_axi_awregion(ifu_axi_awregion_veer[i][3:0]),
      .ifu_axi_awlen(ifu_axi_awlen_veer[i][7:0]),
      .ifu_axi_awsize(ifu_axi_awsize_veer[i][2:0]),
      .ifu_axi_awburst(ifu_axi_awburst_veer[i][1:0]),
      .ifu_axi_awlock(ifu_axi_awlock_veer[i]),
      .ifu_axi_awcache(ifu_axi_awcache_veer[i][3:0]),
      .ifu_axi_awprot(ifu_axi_awprot_veer[i][2:0]),
      .ifu_axi_awqos(ifu_axi_awqos_veer[i][3:0]),
      .ifu_axi_wvalid(ifu_axi_wvalid_veer[i]),
      .ifu_axi_wdata(ifu_axi_wdata_veer[i][63:0]),
      .ifu_axi_wstrb(ifu_axi_wstrb_veer[i][7:0]),
      .ifu_axi_wlast(ifu_axi_wlast_veer[i]),
      .ifu_axi_bready(ifu_axi_bready_veer[i]),

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
      .ifu_axi_rid(ifu_axi_rid_veer[i][pt.IFU_BUS_TAG-1:0]),
      .ifu_axi_rdata(ifu_axi_rdata_veer[i][63:0]),
      .ifu_axi_rresp(ifu_axi_rresp_veer[i][1:0]),

      .dec_tlu_force_halt(dec_tlu_force_halt_veer[i]),
      .dec_tlu_core_ecc_disable(dec_tlu_core_ecc_disable_veer[i]),
      .ifu_bus_clk_en(ifu_bus_clk_en_veer[i]),
      .ic_rw_addr(ic_rw_addr_veer[i]),
      .ic_wr_en(ic_wr_en_veer[i]),
      .ic_rd_en(ic_rd_en_veer[i]),
      .ic_wr_data(ic_wr_data_veer[i]),
      .ic_rd_data(ic_rd_data_veer[i]),
      .ic_rd_addr_lo(ic_rd_addr_lo_veer[i]),
      .ic_rd_bank_check_en(ic_rd_bank_check_en_veer[i]),
      .ic_debug_rd_data(ic_debug_rd_data_veer[i]),
      .ictag_debug_rd_data(ictag_debug_rd_data_veer[i]),
      .ic_debug_wr_data(ic_debug_wr_data_veer[i]),
      .ic_premux_data(ic_premux_data_veer[i]),
      .ic_sel_premux_data(ic_sel_premux_data_veer[i]),
      .ic_debug_addr(ic_debug_addr_veer[i]),
      .ic_debug_rd_en(ic_debug_rd_en_veer[i]),
      .ic_debug_wr_en(ic_debug_wr_en_veer[i]),
      .ic_debug_tag_array(ic_debug_tag_array_veer[i]),
      .ic_debug_way(ic_debug_way_veer[i]),
      .ic_tag_valid(ic_tag_valid_veer[i]),
      .ic_rd_hit(ic_rd_hit_veer[i]),
      .ic_tag_perr(ic_tag_perr_veer[i]),
      .iccm_rw_addr(iccm_rw_addr_veer[i]),
      .iccm_wren(iccm_wren_veer[i]),
      .iccm_rden(iccm_rden_veer[i]),
      .iccm_wr_data(iccm_wr_data_veer[i]),
      .iccm_wr_size(iccm_wr_size_veer[i]),
      .iccm_rd_data(iccm_rd_data_veer[i]),
      .iccm_rd_data_ecc(iccm_rd_data_ecc_veer[i]),
      .iccm_buf_correct_ecc(iccm_buf_correct_ecc_veer[i]),
      .iccm_correction_state(iccm_correction_state_veer[i]),
      .*
    );

    assign iccm_ecc_single_error_veer[i] = ifu_iccm_rd_ecc_single_err || ifu_iccm_dma_rd_ecc_single_err;
    assign iccm_ecc_double_error_veer[i] = ifu_iccm_rd_ecc_double_err;

    el2_dec #(.pt(pt)) dec (
      .clk(active_l2clk),
      .free_l2clk(free_l2clk),
      .dbg_cmd_wrdata(dbg_cmd_wrdata[1:0]),
      .rst_l(core_rst_l_veer[i]),
      .rst_vec(rst_vec_veer[i]),
      .nmi_int(nmi_int_veer[i]),
      .nmi_vec(nmi_vec_veer[i]),
      .o_cpu_halt_status(o_cpu_halt_status_veer[i]),
      .o_cpu_halt_ack(o_cpu_halt_ack_veer[i]),
      .o_cpu_run_ack(o_cpu_run_ack_veer[i]),
      .o_debug_mode_status(o_debug_mode_status_veer[i]),
      .pic_claimid(pic_claimid_veer[i]),
      .pic_pl(pic_pl_veer[i]),
      .dec_tlu_meicurpl(dec_tlu_meicurpl_veer[i]),
      .dec_tlu_meipt(dec_tlu_meipt_veer[i]),
      .mexintpend(mexintpend_veer[i]),
      .mhwakeup(mhwakeup_veer[i]),
      .mpc_debug_halt_ack(mpc_debug_halt_ack_veer[i]),
      .mpc_debug_run_ack(mpc_debug_run_ack_veer[i]),
      .debug_brkpt_status(debug_brkpt_status_veer[i]),
      .dec_tlu_core_ecc_disable(dec_tlu_core_ecc_disable_veer[i]),
      .dec_tlu_perfcnt0(dec_tlu_perfcnt0_veer[i]),
      .dec_tlu_perfcnt1(dec_tlu_perfcnt1_veer[i]),
      .dec_tlu_perfcnt2(dec_tlu_perfcnt2_veer[i]),
      .dec_tlu_perfcnt3(dec_tlu_perfcnt3_veer[i]),
      .dec_tlu_bus_clk_override(dec_tlu_bus_clk_override_veer[i]),
      .dec_tlu_pic_clk_override(dec_tlu_pic_clk_override_veer[i]),
      .dec_tlu_picio_clk_override(dec_tlu_picio_clk_override_veer[i]),
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
      .*
    );

    el2_exu #(.pt(pt)) exu (
      .clk(active_l2clk),
      .rst_l(core_rst_l_veer[i]),
      .*
    );

    el2_lsu #(.pt(pt)) lsu (
      .clk(active_l2clk),
      .rst_l(core_rst_l_veer[i]),
      .clk_override(dec_tlu_lsu_clk_override),
      .dec_tlu_force_halt(dec_tlu_force_halt_veer[i]),
      .dec_tlu_i0_kill_writeb_r(dec_tlu_i0_kill_writeb_r),
      .dec_tlu_core_ecc_disable(dec_tlu_core_ecc_disable_veer[i]),
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
      // PIC
      .picm_wren(picm_wren_veer[i]),
      .picm_rden(picm_rden_veer[i]),
      .picm_mken(picm_mken_veer[i]),
      .picm_rdaddr(picm_rdaddr_veer[i]),
      .picm_wraddr(picm_wraddr_veer[i]),
      .picm_wr_data(picm_wr_data_veer[i]),
      .picm_rd_data(picm_rd_data_veer[i]),
      // AXI signals
      .lsu_axi_awvalid(lsu_axi_awvalid_veer[i]),
      .lsu_axi_awready(lsu_axi_awready_veer[i]),
      .lsu_axi_awid(lsu_axi_awid_veer[i][pt.LSU_BUS_TAG-1:0]),
      .lsu_axi_awaddr(lsu_axi_awaddr_veer[i][31:0]),
      .lsu_axi_awregion(lsu_axi_awregion_veer[i][3:0]),
      .lsu_axi_awlen(lsu_axi_awlen_veer[i][7:0]),
      .lsu_axi_awsize(lsu_axi_awsize_veer[i][2:0]),
      .lsu_axi_awburst(lsu_axi_awburst_veer[i][1:0]),
      .lsu_axi_awlock(lsu_axi_awlock_veer[i]),
      .lsu_axi_awcache(lsu_axi_awcache_veer[i][3:0]),
      .lsu_axi_awprot(lsu_axi_awprot_veer[i][2:0]),
      .lsu_axi_awqos(lsu_axi_awqos_veer[i][3:0]),
      .lsu_axi_wvalid(lsu_axi_wvalid_veer[i]),
      .lsu_axi_wready(lsu_axi_wready_veer[i]),
      .lsu_axi_wdata(lsu_axi_wdata_veer[i][63:0]),
      .lsu_axi_wstrb(lsu_axi_wstrb_veer[i][7:0]),
      .lsu_axi_wlast(lsu_axi_wlast_veer[i]),
      .lsu_axi_bvalid(lsu_axi_bvalid_veer[i]),
      .lsu_axi_bready(lsu_axi_bready_veer[i]),
      .lsu_axi_bid(lsu_axi_bid_veer[i][pt.LSU_BUS_TAG-1:0]),
      .lsu_axi_bresp(lsu_axi_bresp_veer[i][1:0]),

      .lsu_axi_arvalid(lsu_axi_arvalid_veer[i]),
      .lsu_axi_arready(lsu_axi_arready_veer[i]),
      .lsu_axi_arid(lsu_axi_arid_veer[i][pt.LSU_BUS_TAG-1:0]),
      .lsu_axi_araddr(lsu_axi_araddr_veer[i][31:0]),
      .lsu_axi_arregion(lsu_axi_arregion_veer[i][3:0]),
      .lsu_axi_arlen(lsu_axi_arlen_veer[i][7:0]),
      .lsu_axi_arsize(lsu_axi_arsize_veer[i][2:0]),
      .lsu_axi_arburst(lsu_axi_arburst_veer[i][1:0]),
      .lsu_axi_arlock(lsu_axi_arlock_veer[i]),
      .lsu_axi_arcache(lsu_axi_arcache_veer[i][3:0]),
      .lsu_axi_arprot(lsu_axi_arprot_veer[i][2:0]),
      .lsu_axi_arqos(lsu_axi_arqos_veer[i][3:0]),
      .lsu_axi_rvalid(lsu_axi_rvalid_veer[i]),
      .lsu_axi_rready(lsu_axi_rready_veer[i]),
      .lsu_axi_rid(lsu_axi_rid_veer[i][pt.LSU_BUS_TAG-1:0]),
      .lsu_axi_rdata(lsu_axi_rdata_veer[i][63:0]),
      .lsu_axi_rresp(lsu_axi_rresp_veer[i][1:0]),
      .lsu_axi_rlast(lsu_axi_rlast_veer[i]),

      .lsu_bus_clk_en(lsu_bus_clk_en_veer[i]),
      .*
    );

    assign dccm_ecc_single_error_veer[i] = lsu_dccm_rd_ecc_single_err;
    assign dccm_ecc_double_error_veer[i] = lsu_dccm_rd_ecc_double_err;

    el2_dma_ctrl #(.pt(pt)) dma_ctrl (
      .clk(free_l2clk),
      .rst_l(core_rst_l_veer[i]),
      .clk_override(dec_tlu_misc_clk_override),
      .dma_bus_clk_en(dma_bus_clk_en_veer[i]),

      // AXI signals
      .dma_axi_awvalid(dma_axi_awvalid_veer[i]),
      .dma_axi_awready(dma_axi_awready_veer[i]),
      .dma_axi_awid(dma_axi_awid_veer[i][pt.DMA_BUS_TAG-1:0]),
      .dma_axi_awaddr(dma_axi_awaddr_veer[i][31:0]),
      .dma_axi_awsize(dma_axi_awsize_veer[i][2:0]),
      .dma_axi_wvalid(dma_axi_wvalid_veer[i]),
      .dma_axi_wready(dma_axi_wready_veer[i]),
      .dma_axi_wdata(dma_axi_wdata_veer[i][63:0]),
      .dma_axi_wstrb(dma_axi_wstrb_veer[i][7:0]),
      .dma_axi_bvalid(dma_axi_bvalid_veer[i]),
      .dma_axi_bready(dma_axi_bready_veer[i]),
      .dma_axi_bresp(dma_axi_bresp_veer[i]),
      .dma_axi_bid(dma_axi_bid_veer[i]),

      .dma_axi_arvalid(dma_axi_arvalid_veer[i]),
      .dma_axi_arready(dma_axi_arready_veer[i]),
      .dma_axi_arid(dma_axi_arid_veer[i][pt.DMA_BUS_TAG-1:0]),
      .dma_axi_araddr(dma_axi_araddr_veer[i][31:0]),
      .dma_axi_arsize(dma_axi_arsize_veer[i][2:0]),
      .dma_axi_rvalid(dma_axi_rvalid_veer[i]),
      .dma_axi_rready(dma_axi_rready_veer[i]),
      .dma_axi_rid(dma_axi_rid_veer[i]),
      .dma_axi_rdata(dma_axi_rdata_veer[i]),
      .dma_axi_rresp(dma_axi_rresp_veer[i]),
      .dma_axi_rlast(dma_axi_rlast_veer[i]),

      .*
    );

    assign pmp_chan_addr[0] = {ifu_pmp_addr, 1'b0};
    assign pmp_chan_type[0] = EXEC;
    assign ifu_pmp_error    = pmp_chan_err[0];
    assign pmp_chan_addr[1] = lsu_pmp_addr_start;
    assign pmp_chan_type[1] = lsu_pmp_we ? WRITE : (lsu_pmp_re ? READ : NONE);
    assign lsu_pmp_error_start = pmp_chan_err[1];
    assign pmp_chan_addr[2] = lsu_pmp_addr_end;
    assign pmp_chan_type[2] = lsu_pmp_we ? WRITE : (lsu_pmp_re ? READ : NONE);
    assign lsu_pmp_error_end = pmp_chan_err[2];

    el2_pmp #(
        .PMP_CHANNELS(3),
        .pt(pt)
    ) pmp (
        .clk  (active_l2clk),
        .rst_l(core_rst_l_veer[i]),
        .*
    );
    // unpack packet
    // also need retires_p==3
    assign trace_rv_i_insn_ip_veer[i][31:0]    = trace_rv_trace_pkt.trace_rv_i_insn_ip[31:0];
    assign trace_rv_i_address_ip_veer[i][31:0] = trace_rv_trace_pkt.trace_rv_i_address_ip[31:0];
    assign trace_rv_i_valid_ip_veer[i]         = trace_rv_trace_pkt.trace_rv_i_valid_ip;
    assign trace_rv_i_exception_ip_veer[i]     = trace_rv_trace_pkt.trace_rv_i_exception_ip;
    assign trace_rv_i_ecause_ip_veer[i][4:0]   = trace_rv_trace_pkt.trace_rv_i_ecause_ip[4:0];
    assign trace_rv_i_interrupt_ip_veer[i]     = trace_rv_trace_pkt.trace_rv_i_interrupt_ip;
    assign trace_rv_i_tval_ip_veer[i][31:0]    = trace_rv_trace_pkt.trace_rv_i_tval_ip[31:0];
  end

  // Common PIC for all the VeeRs instances
  el2_pic_ctrl  #(.pt(pt)) pic_ctrl_inst (
    .clk(free_l2clk),
    .clk_override(dec_tlu_pic_clk_override_int),
    .io_clk_override(dec_tlu_picio_clk_override_int),
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
    .meicurpl(dec_tlu_meicurpl_int[3:0]),
    .meipt(dec_tlu_meipt_int[3:0]),
    .rst_l(core_rst_l),
    .*
  );
endmodule
