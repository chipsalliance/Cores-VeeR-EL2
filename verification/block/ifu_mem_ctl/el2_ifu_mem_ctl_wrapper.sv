module el2_ifu_mem_ctl_wrapper
  import el2_pkg::*;
#(
    `include "el2_param.vh"
) (
    input logic clk,                                                 // Clock only while core active.  Through one clock header.  For flops with    second clock header built in.  Connected to ACTIVE_L2CLK.
    input logic active_clk,                                          // Clock only while core active.  Through two clock headers. For flops without second clock header built in.
    input logic free_l2clk,                                          // Clock always.                  Through one clock header.  For flops with    second header built in.
    input logic rst_l,  // reset, active low

    input logic exu_flush_final,         // Flush from the pipeline., includes flush lower
    input logic dec_tlu_flush_lower_wb,  // Flush lower from the pipeline.
    input logic dec_tlu_flush_err_wb,    // Flush from the pipeline due to perr.
    input logic dec_tlu_i0_commit_cmt,   // committed i0 instruction
    input logic dec_tlu_force_halt,      // force halt.

    input logic [31:1] ifc_fetch_addr_bf,  // Fetch Address byte aligned always.      F1 stage.
    input logic ifc_fetch_uncacheable_bf,  // The fetch request is uncacheable space. F1 stage
    input logic ifc_fetch_req_bf,  // Fetch request. Comes with the address.  F1 stage
    input logic                       ifc_fetch_req_bf_raw,          // Fetch request without some qualifications. Used for clock-gating. F1 stage
    input logic                       ifc_iccm_access_bf,            // This request is to the ICCM. Do not generate misses to the bus.
    input logic                       ifc_region_acc_fault_bf,       // Access fault. in ICCM region but offset is outside defined ICCM.
    input logic                       ifc_dma_access_ok,             // It is OK to give dma access to the ICCM. (ICCM is not busy this cycle).
    input logic dec_tlu_fence_i_wb,  // Fence.i instruction is committing. Clear all Icache valids.
    input logic ifu_bp_hit_taken_f,  // Branch is predicted taken. Kill the fetch next cycle.

    input logic                       ifu_bp_inst_mask_f,            // tell ic which valids to kill because of a taken branch, right justified

    output logic ifu_miss_state_idle,  // No icache misses are outstanding.
    output logic                      ifu_ic_mb_empty,               // Continue with normal fetching. This does not mean that miss is finished.
    output logic                      ic_dma_active  ,               // In the middle of servicing dma request to ICCM. Do not make any new requests.
    output logic ic_write_stall,  // Stall fetch the cycle we are writing the cache.

    /// PMU signals
    output logic ifu_pmu_ic_miss,    // IC miss event
    output logic ifu_pmu_ic_hit,     // IC hit event
    output logic ifu_pmu_bus_error,  // Bus error event
    output logic ifu_pmu_bus_busy,   // Bus busy event
    output logic ifu_pmu_bus_trxn,   // Bus transaction

    //-------------------------- IFU AXI signals--------------------------
    // AXI Write Channels
    /* exclude signals that are tied to constant value in this file */
    /*pragma coverage off*/
    output logic                      ifu_axi_awvalid,
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
    output logic [63:0] ifu_axi_wdata,
    output logic [ 7:0] ifu_axi_wstrb,
    output logic        ifu_axi_wlast,

    output logic ifu_axi_bready,
    /*pragma coverage on*/

    // AXI Read Channels
    output logic                      ifu_axi_arvalid,
    input  logic                      ifu_axi_arready,
    output logic [pt.IFU_BUS_TAG-1:0] ifu_axi_arid,
    output logic [              31:0] ifu_axi_araddr,
    output logic [               3:0] ifu_axi_arregion,
    /* exclude signals that are tied to constant value in this file */
    /*pragma coverage off*/
    output logic [               7:0] ifu_axi_arlen,
    output logic [               2:0] ifu_axi_arsize,
    output logic [               1:0] ifu_axi_arburst,
    output logic                      ifu_axi_arlock,
    output logic [               3:0] ifu_axi_arcache,
    output logic [               2:0] ifu_axi_arprot,
    output logic [               3:0] ifu_axi_arqos,
    /*pragma coverage on*/

    input  logic                      ifu_axi_rvalid,
    /* exclude signals that are tied to constant value in this file */
    /*pragma coverage off*/
    output logic                      ifu_axi_rready,
    /*pragma coverage on*/
    input  logic [pt.IFU_BUS_TAG-1:0] ifu_axi_rid,
    input  logic [              63:0] ifu_axi_rdata,
    input  logic [               1:0] ifu_axi_rresp,

    input logic ifu_bus_clk_en,


    input logic        dma_iccm_req,   //  dma iccm command (read or write)
    input logic [31:0] dma_mem_addr,   //  dma address
    input logic [ 2:0] dma_mem_sz,     //  size
    input logic        dma_mem_write,  //  write
    input logic [63:0] dma_mem_wdata,  //  write data
    input logic [ 2:0] dma_mem_tag,    //  DMA Buffer entry number

    output logic        iccm_dma_ecc_error,  //   Data read from iccm has an ecc error
    output logic        iccm_dma_rvalid,     //   Data read from iccm is valid
    output logic [63:0] iccm_dma_rdata,      //   dma data read from iccm
    output logic [ 2:0] iccm_dma_rtag,       //   Tag of the DMA req
    output logic        iccm_ready,          //   iccm ready to accept new command.


    //   I$ & ITAG Ports
    output logic [31:1] ic_rw_addr,  // Read/Write addresss to the Icache.
    output logic [pt.ICACHE_NUM_WAYS-1:0]                ic_wr_en,           // Icache write enable, when filling the Icache.
    output logic ic_rd_en,  // Icache read  enable.

    output logic [pt.ICACHE_BANKS_WAY-1:0] [70:0]               ic_wr_data,           // Data to fill to the Icache. With ECC
    input  logic [63:0]               ic_rd_data ,          // Data read from Icache. 2x64bits + parity bits. F2 stage. With ECC
    input  logic [70:0]               ic_debug_rd_data ,          // Data read from Icache. 2x64bits + parity bits. F2 stage. With ECC
    input logic [25:0] ictag_debug_rd_data,  // Debug icache tag.
    output logic [70:0] ic_debug_wr_data,  // Debug wr cache.
    output logic [70:0] ifu_ic_debug_rd_data,  // debug data read


    input logic [pt.ICACHE_BANKS_WAY-1:0] ic_eccerr,  //
    input logic [pt.ICACHE_BANKS_WAY-1:0] ic_parerr,

    output logic [  pt.ICACHE_INDEX_HI:3] ic_debug_addr,       // Read/Write addresss to the Icache.
    output logic                          ic_debug_rd_en,      // Icache debug rd
    output logic                          ic_debug_wr_en,      // Icache debug wr
    output logic                          ic_debug_tag_array,  // Debug tag array
    output logic [pt.ICACHE_NUM_WAYS-1:0] ic_debug_way,        // Debug way. Rd or Wr.


    output logic [pt.ICACHE_NUM_WAYS-1:0]                ic_tag_valid,       // Valid bits when accessing the Icache. One valid bit per way. F2 stage

    input  logic [pt.ICACHE_NUM_WAYS-1:0]                ic_rd_hit,          // Compare hits from Icache tags. Per way.  F2 stage
    input logic ic_tag_perr,  // Icache Tag parity error

    // ICCM ports
    output logic [pt.ICCM_BITS-1:1] iccm_rw_addr,  // ICCM read/write address.
    output logic                    iccm_wren,     // ICCM write enable (through the DMA)
    output logic                    iccm_rden,     // ICCM read enable.
    output logic [            77:0] iccm_wr_data,  // ICCM write data.
    output logic [             2:0] iccm_wr_size,  // ICCM write location within DW.

    input logic [63:0] iccm_rd_data,  // Data read from ICCM.
    input logic [77:0] iccm_rd_data_ecc,  // Data + ECC read from ICCM.
    input logic [1:0] ifu_fetch_val,
    // IFU control signals
    output logic                      ic_hit_f,               // Hit in Icache(if Icache access) or ICCM access( ICCM always has ic_hit_f)
    output logic [1:0]                ic_access_fault_f,      // Access fault (bus error or ICCM access in region but out of offset range).
    output logic [1:0] ic_access_fault_type_f,  // Access fault types
    output logic iccm_rd_ecc_single_err,  // This fetch has a single ICCM ECC error.
    output logic [1:0] iccm_rd_ecc_double_err,  // This fetch has a double ICCM ECC error.
    output logic iccm_dma_rd_ecc_single_err,  // This fetch has a single ICCM DMA ECC error.
    output logic iccm_dma_rd_ecc_double_err,  // This fetch has a double ICCM DMA ECC error.
    output logic ic_error_start,  // This has any I$ errors ( data/tag/ecc/parity )

    output logic                      ifu_async_error_start,  // Or of the sb iccm, and all the icache errors sent to aligner to stop
    output logic iccm_dma_sb_error,  // Single Bit ECC error from a DMA access
    output logic [1:0] ic_fetch_val_f,  // valid bytes for fetch. To the Aligner.
    output logic [31:0] ic_data_f,  // Data read from Icache or ICCM. To the Aligner.
    output logic [63:0] ic_premux_data,  // Premuxed data to be muxed with Icache data
    output logic ic_sel_premux_data,  // Select premux data.

    /////  Debug
    // Icache/tag debug read/write packet
    input logic [70:0] icache_wrdata,
    input logic [16:0] icache_dicawics,
    input logic        icache_rd_valid,
    input logic        icache_wr_valid,

    input  logic dec_tlu_core_ecc_disable,    // disable the ecc checking and flagging
    output logic ifu_ic_debug_rd_data_valid,  // debug data valid.
    output logic iccm_buf_correct_ecc,
    output logic iccm_correction_state,

    input logic ifu_pmp_error,

    input logic scan_mode
);
  el2_cache_debug_pkt_t dec_tlu_ic_diag_pkt;

  assign dec_tlu_ic_diag_pkt = {icache_wrdata, icache_dicawics, icache_rd_valid, icache_wr_valid};

  el2_ifu_mem_ctl ifu_mem_ctl (.*);

endmodule  // el2_ifu_mem_ctl_wrapper
