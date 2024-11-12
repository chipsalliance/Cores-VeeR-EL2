// Copyright (c) 2024 Antmicro <www.antmicro.com>
// SPDX-License-Identifier: Apache-2.0

module el2_veer_lockstep_wrapper
  import el2_pkg::*;
#(
    `include "el2_param.vh"
) (
    input logic clk,
    input logic rst_l,
    input logic dbg_rst_l,

    output logic shadow_reset,
    output logic shadow_dbg_reset,

    // Shadow Core control
    input logic disable_corruption_detection_i,
    input logic lockstep_err_injection_en_i,

    // Equivalency Checker
    output logic corruption_detected_o
);
  logic core_rst_l;   // This is "rst_l | dbg_rst_l"

  logic [31:1] rst_vec;
  logic [31:1] nmi_vec;

  logic nmi_int;
  logic timer_int;
  logic soft_int;

  logic [pt.PIC_TOTAL_INT:1] extintsrc_req;

  logic active_l2clk;
  logic free_l2clk;

  logic [31:0] trace_rv_i_insn_ip;
  logic [31:0] trace_rv_i_address_ip;
  logic        trace_rv_i_valid_ip;
  logic        trace_rv_i_exception_ip;
  logic [ 4:0] trace_rv_i_ecause_ip;
  logic        trace_rv_i_interrupt_ip;
  logic [31:0] trace_rv_i_tval_ip;


  logic dccm_clk_override;
  logic icm_clk_override;
  logic dec_tlu_core_ecc_disable;

   // external halt/run interface
  logic i_cpu_halt_req;    // Asynchronous Halt request to CPU
  logic i_cpu_run_req;     // Asynchronous Restart request to CPU
  logic o_cpu_halt_ack;    // Core Acknowledge to Halt request
  logic o_cpu_halt_status; // 1'b1 indicates processor is halted
  logic o_cpu_run_ack;     // Core Acknowledge to run request
  logic o_debug_mode_status; // Core to the PMU that core is in debug mode. When core is in debug mode; the PMU should refrain from sendng a halt or run request

  logic [31:4] core_id; // CORE ID

   // external MPC halt/run interface
  logic mpc_debug_halt_req; // Async halt request
  logic mpc_debug_run_req; // Async run request
  logic mpc_reset_run_req; // Run/halt after reset
  logic mpc_debug_halt_ack; // Halt ack
  logic mpc_debug_run_ack; // Run ack
  logic debug_brkpt_status; // debug breakpoint

  logic dec_tlu_perfcnt0; // toggles when slot0 perf counter 0 has an event inc
  logic dec_tlu_perfcnt1;
  logic dec_tlu_perfcnt2;
  logic dec_tlu_perfcnt3;

   // DCCM ports
  logic                           dccm_wren;
  logic                           dccm_rden;
  logic [       pt.DCCM_BITS-1:0] dccm_wr_addr_lo;
  logic [       pt.DCCM_BITS-1:0] dccm_wr_addr_hi;
  logic [       pt.DCCM_BITS-1:0] dccm_rd_addr_lo;
  logic [       pt.DCCM_BITS-1:0] dccm_rd_addr_hi;
  logic [pt.DCCM_FDATA_WIDTH-1:0] dccm_wr_data_lo;
  logic [pt.DCCM_FDATA_WIDTH-1:0] dccm_wr_data_hi;

  logic [pt.DCCM_FDATA_WIDTH-1:0] dccm_rd_data_lo;
  logic [pt.DCCM_FDATA_WIDTH-1:0] dccm_rd_data_hi;

   // ICCM ports
  logic [pt.ICCM_BITS-1:1] iccm_rw_addr;
  logic                    iccm_wren;
  logic                    iccm_rden;
  logic [             2:0] iccm_wr_size;
  logic [            77:0] iccm_wr_data;
  logic                    iccm_buf_correct_ecc;
  logic                    iccm_correction_state;

  logic [63:0] iccm_rd_data;
  logic [77:0] iccm_rd_data_ecc;

   // ICache ; ITAG  ports
  logic [                  31:1] ic_rw_addr;
  logic [pt.ICACHE_NUM_WAYS-1:0] ic_tag_valid;
  logic [pt.ICACHE_NUM_WAYS-1:0] ic_wr_en;
  logic                          ic_rd_en;

  logic [pt.ICACHE_BANKS_WAY-1:0][70:0] ic_wr_data;         // Data to fill to the Icache. With ECC
  logic [                         63:0] ic_rd_data ;        // Data read from Icache. 2x64bits + parity bits. F2 stage. With ECC
  logic [                         70:0] ic_debug_rd_data ;        // Data read from Icache. 2x64bits + parity bits. F2 stage. With ECC
  logic [                         25:0] ictag_debug_rd_data;// Debug icache tag.
  logic [                         70:0] ic_debug_wr_data;   // Debug wr cache.

  logic [pt.ICACHE_BANKS_WAY-1:0] ic_eccerr;
  logic [pt.ICACHE_BANKS_WAY-1:0] ic_parerr;
  logic [                   63:0] ic_premux_data;     // Premux data to be muxed with each way of the Icache.
  logic                           ic_sel_premux_data; // Select premux data


  logic [  pt.ICACHE_INDEX_HI:3] ic_debug_addr;      // Read/Write addresss to the Icache.
  logic                          ic_debug_rd_en;     // Icache debug rd
  logic                          ic_debug_wr_en;     // Icache debug wr
  logic                          ic_debug_tag_array; // Debug tag array
  logic [pt.ICACHE_NUM_WAYS-1:0] ic_debug_way;       // Debug way. Rd or Wr.



  logic [pt.ICACHE_NUM_WAYS-1:0] ic_rd_hit;
  logic                          ic_tag_perr;        // Icache Tag parity error

   //-------------------------- LSU AXI signals--------------------------
   // AXI Write Channels
  logic                      lsu_axi_awvalid;
  logic                      lsu_axi_awready;
  logic [pt.LSU_BUS_TAG-1:0] lsu_axi_awid;
  logic [              31:0] lsu_axi_awaddr;
  logic [               3:0] lsu_axi_awregion;
  logic [               7:0] lsu_axi_awlen;
  logic [               2:0] lsu_axi_awsize;
  logic [               1:0] lsu_axi_awburst;
  logic                      lsu_axi_awlock;
  logic [               3:0] lsu_axi_awcache;
  logic [               2:0] lsu_axi_awprot;
  logic [               3:0] lsu_axi_awqos;

  logic        lsu_axi_wvalid;
  logic        lsu_axi_wready;
  logic [63:0] lsu_axi_wdata;
  logic [ 7:0] lsu_axi_wstrb;
  logic        lsu_axi_wlast;

  logic                      lsu_axi_bvalid;
  logic                      lsu_axi_bready;
  logic [               1:0] lsu_axi_bresp;
  logic [pt.LSU_BUS_TAG-1:0] lsu_axi_bid;

   // AXI Read Channels
  logic                      lsu_axi_arvalid;
  logic                      lsu_axi_arready;
  logic [pt.LSU_BUS_TAG-1:0] lsu_axi_arid;
  logic [              31:0] lsu_axi_araddr;
  logic [               3:0] lsu_axi_arregion;
  logic [               7:0] lsu_axi_arlen;
  logic [               2:0] lsu_axi_arsize;
  logic [               1:0] lsu_axi_arburst;
  logic                      lsu_axi_arlock;
  logic [               3:0] lsu_axi_arcache;
  logic [               2:0] lsu_axi_arprot;
  logic [               3:0] lsu_axi_arqos;

  logic                      lsu_axi_rvalid;
  logic                      lsu_axi_rready;
  logic [pt.LSU_BUS_TAG-1:0] lsu_axi_rid;
  logic [              63:0] lsu_axi_rdata;
  logic [               1:0] lsu_axi_rresp;
  logic                      lsu_axi_rlast;

  //-------------------------- IFU AXI signals--------------------------
  // AXI Write Channels
  logic                      ifu_axi_awvalid;
  logic                      ifu_axi_awready;
  logic [pt.IFU_BUS_TAG-1:0] ifu_axi_awid;
  logic [              31:0] ifu_axi_awaddr;
  logic [               3:0] ifu_axi_awregion;
  logic [               7:0] ifu_axi_awlen;
  logic [               2:0] ifu_axi_awsize;
  logic [               1:0] ifu_axi_awburst;
  logic                      ifu_axi_awlock;
  logic [               3:0] ifu_axi_awcache;
  logic [               2:0] ifu_axi_awprot;
  logic [               3:0] ifu_axi_awqos;

  logic        ifu_axi_wvalid;
  logic        ifu_axi_wready;
  logic [63:0] ifu_axi_wdata;
  logic [ 7:0] ifu_axi_wstrb;
  logic        ifu_axi_wlast;

  logic                      ifu_axi_bvalid;
  logic                      ifu_axi_bready;
  logic [               1:0] ifu_axi_bresp;
  logic [pt.IFU_BUS_TAG-1:0] ifu_axi_bid;

   // AXI Read Channels
  logic                      ifu_axi_arvalid;
  logic                      ifu_axi_arready;
  logic [pt.IFU_BUS_TAG-1:0] ifu_axi_arid;
  logic [              31:0] ifu_axi_araddr;
  logic [               3:0] ifu_axi_arregion;
  logic [               7:0] ifu_axi_arlen;
  logic [               2:0] ifu_axi_arsize;
  logic [               1:0] ifu_axi_arburst;
  logic                      ifu_axi_arlock;
  logic [               3:0] ifu_axi_arcache;
  logic [               2:0] ifu_axi_arprot;
  logic [               3:0] ifu_axi_arqos;

  logic                      ifu_axi_rvalid;
  logic                      ifu_axi_rready;
  logic [pt.IFU_BUS_TAG-1:0] ifu_axi_rid;
  logic [              63:0] ifu_axi_rdata;
  logic [               1:0] ifu_axi_rresp;
  logic                      ifu_axi_rlast;

   //-------------------------- SB AXI signals--------------------------
   // AXI Write Channels
  logic                     sb_axi_awvalid;
  logic                     sb_axi_awready;
  logic [pt.SB_BUS_TAG-1:0] sb_axi_awid;
  logic [             31:0] sb_axi_awaddr;
  logic [              3:0] sb_axi_awregion;
  logic [              7:0] sb_axi_awlen;
  logic [              2:0] sb_axi_awsize;
  logic [              1:0] sb_axi_awburst;
  logic                     sb_axi_awlock;
  logic [              3:0] sb_axi_awcache;
  logic [              2:0] sb_axi_awprot;
  logic [              3:0] sb_axi_awqos;

  logic        sb_axi_wvalid;
  logic        sb_axi_wready;
  logic [63:0] sb_axi_wdata;
  logic [ 7:0] sb_axi_wstrb;
  logic        sb_axi_wlast;

  logic                     sb_axi_bvalid;
  logic                     sb_axi_bready;
  logic [              1:0] sb_axi_bresp;
  logic [pt.SB_BUS_TAG-1:0] sb_axi_bid;

   // AXI Read Channels
  logic                     sb_axi_arvalid;
  logic                     sb_axi_arready;
  logic [pt.SB_BUS_TAG-1:0] sb_axi_arid;
  logic [             31:0] sb_axi_araddr;
  logic [              3:0] sb_axi_arregion;
  logic [              7:0] sb_axi_arlen;
  logic [              2:0] sb_axi_arsize;
  logic [              1:0] sb_axi_arburst;
  logic                     sb_axi_arlock;
  logic [              3:0] sb_axi_arcache;
  logic [              2:0] sb_axi_arprot;
  logic [              3:0] sb_axi_arqos;

  logic                     sb_axi_rvalid;
  logic                     sb_axi_rready;
  logic [pt.SB_BUS_TAG-1:0] sb_axi_rid;
  logic [             63:0] sb_axi_rdata;
  logic [              1:0] sb_axi_rresp;
  logic                     sb_axi_rlast;

  //-------------------------- DMA AXI signals--------------------------
  // AXI Write Channels
  logic                      dma_axi_awvalid;
  logic                      dma_axi_awready;
  logic [pt.DMA_BUS_TAG-1:0] dma_axi_awid;
  logic [              31:0] dma_axi_awaddr;
  logic [               2:0] dma_axi_awsize;
  logic [               2:0] dma_axi_awprot;
  logic [               7:0] dma_axi_awlen;
  logic [               1:0] dma_axi_awburst;


  logic        dma_axi_wvalid;
  logic        dma_axi_wready;
  logic [63:0] dma_axi_wdata;
  logic [ 7:0] dma_axi_wstrb;
  logic        dma_axi_wlast;

  logic                      dma_axi_bvalid;
  logic                      dma_axi_bready;
  logic [               1:0] dma_axi_bresp;
  logic [pt.DMA_BUS_TAG-1:0] dma_axi_bid;

  // AXI Read Channels
  logic                      dma_axi_arvalid;
  logic                      dma_axi_arready;
  logic [pt.DMA_BUS_TAG-1:0] dma_axi_arid;
  logic [              31:0] dma_axi_araddr;
  logic [               2:0] dma_axi_arsize;
  logic [               2:0] dma_axi_arprot;
  logic [               7:0] dma_axi_arlen;
  logic [               1:0] dma_axi_arburst;

  logic                      dma_axi_rvalid;
  logic                      dma_axi_rready;
  logic [pt.DMA_BUS_TAG-1:0] dma_axi_rid;
  logic [              63:0] dma_axi_rdata;
  logic [               1:0] dma_axi_rresp;
  logic                      dma_axi_rlast;


  //// AHB LITE BUS
  logic [31:0] haddr;
  logic [ 2:0] hburst;
  logic        hmastlock;
  logic [ 3:0] hprot;
  logic [ 2:0] hsize;
  logic [ 1:0] htrans;
  logic        hwrite;

  logic [63:0] hrdata;
  logic        hready;
  logic        hresp;

  // LSU AHB Master
  logic [31:0] lsu_haddr;
  logic [ 2:0] lsu_hburst;
  logic        lsu_hmastlock;
  logic [ 3:0] lsu_hprot;
  logic [ 2:0] lsu_hsize;
  logic [ 1:0] lsu_htrans;
  logic        lsu_hwrite;
  logic [63:0] lsu_hwdata;

  logic [63:0] lsu_hrdata;
  logic        lsu_hready;
  logic        lsu_hresp;

  //System Bus Debug Master
  logic [31:0] sb_haddr;
  logic [ 2:0] sb_hburst;
  logic        sb_hmastlock;
  logic [ 3:0] sb_hprot;
  logic [ 2:0] sb_hsize;
  logic [ 1:0] sb_htrans;
  logic        sb_hwrite;
  logic [63:0] sb_hwdata;

  logic [63:0] sb_hrdata;
  logic        sb_hready;
  logic        sb_hresp;

   // DMA Slave
  logic        dma_hsel;
  logic [31:0] dma_haddr;
  logic [ 2:0] dma_hburst;
  logic        dma_hmastlock;
  logic [ 3:0] dma_hprot;
  logic [ 2:0] dma_hsize;
  logic [ 1:0] dma_htrans;
  logic        dma_hwrite;
  logic [63:0] dma_hwdata;
  logic        dma_hreadyin;

  logic [63:0] dma_hrdata;
  logic        dma_hreadyout;
  logic        dma_hresp;

  logic lsu_bus_clk_en;
  logic ifu_bus_clk_en;
  logic dbg_bus_clk_en;
  logic dma_bus_clk_en;

  logic        dmi_reg_en;                // read or write
  logic [ 6:0] dmi_reg_addr;              // address of DM register
  logic        dmi_reg_wr_en;             // write instruction
  logic [31:0] dmi_reg_wdata;             // write data
  logic [31:0] dmi_reg_rdata;

   // ICCM/DCCM ECC status
  logic iccm_ecc_single_error;
  logic iccm_ecc_double_error;
  logic dccm_ecc_single_error;
  logic dccm_ecc_double_error;

  logic scan_mode;

`ifdef RV_LOCKSTEP_REGFILE_ENABLE
  el2_regfile_if regfile ();
`endif // `ifdef RV_LOCKSTEP_REGFILE_ENABLE

  el2_veer #(.pt(pt)) veer (
`ifdef RV_LOCKSTEP_REGFILE_ENABLE
      .regfile(regfile.veer_rf_src),
`endif // `ifdef RV_LOCKSTEP_REGFILE_ENABLE
      .*
  );

  el2_veer_lockstep #(.pt(pt)) lockstep (
`ifdef RV_LOCKSTEP_REGFILE_ENABLE
      .main_core_regfile(regfile.veer_rf_sink),
`endif // `ifdef RV_LOCKSTEP_REGFILE_ENABLE
      .*
  );

  assign shadow_reset = lockstep.rst_shadow;
  assign shadow_dbg_reset = lockstep.rst_dbg_shadow;
endmodule
