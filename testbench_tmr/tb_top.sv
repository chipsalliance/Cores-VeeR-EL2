module tb_top #(
  `include "el2_param.vh"
);

import tb_top_pkg::*;

// ============================================================================

logic core_clk;
logic rst_l;
logic porst_l;

logic [7:0] rst_l_cmd;
logic rst_l_combined;

logic [pt.PIC_TOTAL_INT:1]  extintsrc_req;
logic                       nmi_int;
logic                       timer_int;
logic                       soft_int;

el2_mem_if el2_mem_export ();

logic [31:1] jtag_id;
assign jtag_id[31:28] = 4'b1;
assign jtag_id[27:12] = '0;
assign jtag_id[ 11:1] = 11'h45;

logic i_cpu_halt_req, o_cpu_halt_ack, o_cpu_halt_status;
logic i_cpu_run_req, o_cpu_run_ack;
logic mpc_debug_halt_req, mpc_debug_halt_ack;
logic mpc_debug_run_req, mpc_debug_run_ack;
logic o_debug_mode_status;

logic [31:0] trace_rv_i_insn_ip;
logic [31:0] trace_rv_i_address_ip;
logic        trace_rv_i_valid_ip;
logic        trace_rv_i_exception_ip;
logic [4:0]  trace_rv_i_ecause_ip;
logic        trace_rv_i_interrupt_ip;
logic [31:0] trace_rv_i_tval_ip;

logic jtag_tdo;
logic jtag_tck;
logic jtag_tms;
logic jtag_tdi;
logic jtag_trst_n;

logic dmi_core_enable;

assign i_cpu_halt_req      = '0;
assign i_cpu_run_req       = '0;
assign mpc_debug_halt_req  = '0;
assign mpc_debug_run_req   = '0;

assign dmi_core_enable     = ~o_cpu_halt_status;

// ------------------------------------------------------------------
// CRG
// ------------------------------------------------------------------

initial core_clk = '0;
always #2 core_clk <= ~core_clk;

initial begin
  porst_l =     '1;
  porst_l = #1  '0;
  porst_l = #10 '1;
end

initial begin
  rst_l =     '1;
  rst_l = #5  '0;
  rst_l = #25 '1;
end

assign rst_l_combined = rst_l & (&rst_l_cmd);

// Cycle counting
int     cycleCnt;
initial cycleCnt = '0;

int maxCycles;
initial begin
    maxCycles = 2_000_000;
    $value$plusargs("maxCycles=%d", maxCycles);
end

always @(negedge core_clk) begin
  cycleCnt <= cycleCnt + 1;

  // timeout monitor
  if (cycleCnt == maxCycles) begin
      $display("Hit max cycle count (%0d) .. stopping", cycleCnt);
      $display("TEST_FAILED");
      `ifdef TB_SILENT_FAIL
          $finish;
      `else
          $fatal;
      `endif // TB_SILENT_FAIL
  end
end

// ------------------------------------------------------------------
// AHB logic
// ------------------------------------------------------------------
`ifdef RV_BUILD_AHB_LITE

logic                       lmem_hsel;
logic        [31:0]         lmem_haddr;
logic        [2:0]          lmem_hburst;
logic                       lmem_hmastlock;
logic        [3:0]          lmem_hprot;
logic        [2:0]          lmem_hsize;
logic        [1:0]          lmem_htrans;
logic                       lmem_hwrite;
logic                       lmem_hreadyout;
logic                       lmem_hreadyin;

logic        [31:0]         ic_haddr        ;
logic        [2:0]          ic_hburst       ;
logic                       ic_hmastlock    ;
logic        [3:0]          ic_hprot        ;
logic        [2:0]          ic_hsize        ;
logic        [1:0]          ic_htrans       ;
logic                       ic_hwrite       ;
logic        [63:0]         ic_hrdata       ;
logic                       ic_hready       ;
logic                       ic_hresp        ;

logic        [31:0]         lsu_haddr       ;
logic        [2:0]          lsu_hburst      ;
logic                       lsu_hmastlock   ;
logic        [3:0]          lsu_hprot       ;
logic        [2:0]          lsu_hsize       ;
logic        [1:0]          lsu_htrans      ;
logic                       lsu_hwrite      ;
logic        [63:0]         lsu_hrdata      ;
logic        [63:0]         lsu_hwdata      ;
logic                       lsu_hready      ;
logic                       lsu_hresp       ;

logic        [31:0]         sb_haddr        ;
logic        [2:0]          sb_hburst       ;
logic                       sb_hmastlock    ;
logic        [3:0]          sb_hprot        ;
logic        [2:0]          sb_hsize        ;
logic        [1:0]          sb_htrans       ;
logic                       sb_hwrite       ;

logic        [63:0]         sb_hrdata       ;
logic        [63:0]         sb_hwdata       ;
logic                       sb_hready       ;
logic                       sb_hresp        ;

logic                       dma_hsel;
logic        [31:0]         dma_haddr;
logic        [2:0]          dma_hburst;
logic                       dma_hmastlock;
logic        [3:0]          dma_hprot;
logic        [2:0]          dma_hsize;
logic        [1:0]          dma_htrans;
logic                       dma_hwrite;
logic                       dma_hreadyout;
logic                       dma_hreadyin;

// SB and LSU AHB master mux
ahb_lite_2to1_mux #(
    .AHB_LITE_ADDR_WIDTH (32),
    .AHB_LITE_DATA_WIDTH (64),
    .AHB_NO_OPT(1) //Prevent address and data phase overlap between initiators

) u_sb_lsu_ahb_mux (

    .hclk                (core_clk),
    .hreset_n            (rst_l_combined),
    .force_bus_idle      (),

    // Initiator 0
    .hsel_i_0            (1'b1      ),
    .haddr_i_0           (lsu_haddr ),
    .hwdata_i_0          (lsu_hwdata),
    .hwrite_i_0          (lsu_hwrite),
    .htrans_i_0          (lsu_htrans),
    .hsize_i_0           (lsu_hsize ),
    .hready_i_0          (lsu_hready),
    .hresp_o_0           (lsu_hresp ),
    .hready_o_0          (lsu_hready),
    .hrdata_o_0          (lsu_hrdata),

    // Initiator 1
    .hsel_i_1            (1'b1      ),
    .haddr_i_1           (sb_haddr  ),
    .hwdata_i_1          (sb_hwdata ),
    .hwrite_i_1          (sb_hwrite ),
    .htrans_i_1          (sb_htrans ),
    .hsize_i_1           (sb_hsize  ),
    .hready_i_1          (sb_hready ),
    .hresp_o_1           (sb_hresp  ),
    .hready_o_1          (sb_hready ),
    .hrdata_o_1          (sb_hrdata ),

    // Responder
    .hsel_o              (mux_hsel),
    .haddr_o             (mux_haddr ),
    .hwdata_o            (mux_hwdata),
    .hwrite_o            (mux_hwrite),
    .htrans_o            (mux_htrans),
    .hsize_o             (mux_hsize ),
    .hready_o            (mux_hready),
    .hresp_i             (mux_hresp ),
    .hreadyout_i         (mux_hreadyout),
    .hrdata_i            (mux_hrdata)
);

// DMA AHB subordinate mux
ahb_lsu_dma_bridge #(.pt(pt)) bridge (
    .clk                 (core_clk),
    .reset_l             (rst_l_combined),

    .m_ahb_haddr         (mux_haddr[31:0]),
    .m_ahb_hburst        (mux_hburst),
    .m_ahb_hmastlock     (mux_hmastlock),
    .m_ahb_hprot         (mux_hprot[3:0]),
    .m_ahb_hsize         (mux_hsize[2:0]),
    .m_ahb_htrans        (mux_htrans[1:0]),
    .m_ahb_hwrite        (mux_hwrite),
    .m_ahb_hwdata        (mux_hwdata[63:0]),
    .m_ahb_hsel          (mux_hsel),
    .m_ahb_hreadyin      (mux_hready),
    .m_ahb_hrdata        (mux_hrdata[63:0]),
    .m_ahb_hreadyout     (mux_hreadyout),
    .m_ahb_hresp         (mux_hresp),

    .s0_ahb_hsel         (lmem_hsel),
    .s0_ahb_haddr        (lmem_haddr),
    .s0_ahb_hburst       (lmem_hburst),
    .s0_ahb_hmastlock    (lmem_hmastlock),
    .s0_ahb_hprot        (lmem_hprot),
    .s0_ahb_hsize        (lmem_hsize),
    .s0_ahb_htrans       (lmem_htrans),
    .s0_ahb_hwrite       (lmem_hwrite),
    .s0_ahb_hwdata       (lmem_hwdata),
    .s0_ahb_hrdata       (lmem_hrdata),
    .s0_ahb_hready       (lmem_hready_out),
    .s0_ahb_hresp        (lmem_hresp),

    .s1_ahb_hsel         (dma_hsel),
    .s1_ahb_haddr        (dma_haddr),
    .s1_ahb_hburst       (dma_hburst),
    .s1_ahb_hmastlock    (dma_hmastlock),
    .s1_ahb_hprot        (dma_hprot),
    .s1_ahb_hsize        (dma_hsize),
    .s1_ahb_htrans       (dma_htrans),
    .s1_ahb_hwrite       (dma_hwrite),
    .s1_ahb_hwdata       (dma_hwdata),
    .s1_ahb_hrdata       (dma_hrdata),
    .s1_ahb_hready       (dma_hready_out),
    .s1_ahb_hresp        (dma_hresp)
);

ahb_sif imem (

    // Inputs
    .HCLK      (core_clk),
    .HRESETn   (rst_l_combined),

    .HSEL      (1'b1),
    .HADDR     (ic_haddr),
    .HBURST    (ic_hburst),
    .HPROT     (ic_hprot),
    .HWRITE    (ic_hwrite),
    .HWDATA    (64'h0),
    .HTRANS    (ic_htrans),
    .HSIZE     (ic_hsize),
    .HREADY    (ic_hready),

    // Outputs
    .HREADYOUT (ic_hready),
    .HRESP     (ic_hresp),
    .HRDATA    (ic_hrdata[63:0])
);

ahb_sif #(
    .MAX_DELAY(1),
    .MIN_DELAY(1)

) lmem (

    // Inputs
    .HCLK      (core_clk),
    .HRESETn   (rst_l_combined),

    .HSEL      (lmem_hsel),
    .HADDR     (lmem_haddr),
    .HBURST    (lmem_hburst),
    .HPROT     (lmem_hprot),
    .HWRITE    (lmem_hwrite),
    .HWDATA    (lmem_hwdata),
    .HTRANS    (lmem_htrans),
    .HSIZE     (lmem_hsize),
    .HREADY    (lmem_hready_out),

    // Outputs
    .HREADYOUT (lmem_hready_out),
    .HRESP     (lmem_hresp),
    .HRDATA    (lmem_hrdata)
);

`endif // RV_BUILD_AHB_LITE

// ------------------------------------------------------------------
// AXI logic
// ------------------------------------------------------------------
`ifdef RV_BUILD_AXI4

parameter int RV_MUX_BUS_TAG = (`RV_LSU_BUS_TAG > `RV_SB_BUS_TAG ? `RV_LSU_BUS_TAG : `RV_SB_BUS_TAG) + 1;

//-------------------------- LSU AXI signals--------------------------
// AXI Write Channels
wire                        lsu_axi_awvalid;
wire                        lsu_axi_awready;
wire [`RV_LSU_BUS_TAG-1:0]  lsu_axi_awid;
wire [31:0]                 lsu_axi_awaddr;
wire [3:0]                  lsu_axi_awregion;
wire [7:0]                  lsu_axi_awlen;
wire [2:0]                  lsu_axi_awsize;
wire [1:0]                  lsu_axi_awburst;
wire                        lsu_axi_awlock;
wire [3:0]                  lsu_axi_awcache;
wire [2:0]                  lsu_axi_awprot;
wire [3:0]                  lsu_axi_awqos;

wire                        lsu_axi_wvalid;
wire                        lsu_axi_wready;
wire [63:0]                 lsu_axi_wdata;
wire [7:0]                  lsu_axi_wstrb;
wire                        lsu_axi_wlast;

wire                        lsu_axi_bvalid;
wire                        lsu_axi_bready;
wire [1:0]                  lsu_axi_bresp;
wire [`RV_LSU_BUS_TAG-1:0]  lsu_axi_bid;

// AXI Read Channels
wire                        lsu_axi_arvalid;
wire                        lsu_axi_arready;
wire [`RV_LSU_BUS_TAG-1:0]  lsu_axi_arid;
wire [31:0]                 lsu_axi_araddr;
wire [3:0]                  lsu_axi_arregion;
wire [7:0]                  lsu_axi_arlen;
wire [2:0]                  lsu_axi_arsize;
wire [1:0]                  lsu_axi_arburst;
wire                        lsu_axi_arlock;
wire [3:0]                  lsu_axi_arcache;
wire [2:0]                  lsu_axi_arprot;
wire [3:0]                  lsu_axi_arqos;

wire                        lsu_axi_rvalid;
wire                        lsu_axi_rready;
wire [`RV_LSU_BUS_TAG-1:0]  lsu_axi_rid;
wire [63:0]                 lsu_axi_rdata;
wire [1:0]                  lsu_axi_rresp;
wire                        lsu_axi_rlast;
wire                        lsu_axi_awuser;
wire                        lsu_axi_wuser;
wire                        lsu_axi_buser;
wire                        lsu_axi_aruser;
wire                        lsu_axi_ruser;

//-------------------------- IFU AXI signals--------------------------
// AXI Write Channels
wire                        ifu_axi_awvalid;
wire                        ifu_axi_awready;
wire [`RV_IFU_BUS_TAG-1:0]  ifu_axi_awid;
wire [31:0]                 ifu_axi_awaddr;
wire [3:0]                  ifu_axi_awregion;
wire [7:0]                  ifu_axi_awlen;
wire [2:0]                  ifu_axi_awsize;
wire [1:0]                  ifu_axi_awburst;
wire                        ifu_axi_awlock;
wire [3:0]                  ifu_axi_awcache;
wire [2:0]                  ifu_axi_awprot;
wire [3:0]                  ifu_axi_awqos;

wire                        ifu_axi_wvalid;
wire                        ifu_axi_wready;
wire [63:0]                 ifu_axi_wdata;
wire [7:0]                  ifu_axi_wstrb;
wire                        ifu_axi_wlast;

wire                        ifu_axi_bvalid;
wire                        ifu_axi_bready;
wire [1:0]                  ifu_axi_bresp;
wire [`RV_IFU_BUS_TAG-1:0]  ifu_axi_bid;

// AXI Read Channels
wire                        ifu_axi_arvalid;
wire                        ifu_axi_arready;
wire [`RV_IFU_BUS_TAG-1:0]  ifu_axi_arid;
wire [31:0]                 ifu_axi_araddr;
wire [3:0]                  ifu_axi_arregion;
wire [7:0]                  ifu_axi_arlen;
wire [2:0]                  ifu_axi_arsize;
wire [1:0]                  ifu_axi_arburst;
wire                        ifu_axi_arlock;
wire [3:0]                  ifu_axi_arcache;
wire [2:0]                  ifu_axi_arprot;
wire [3:0]                  ifu_axi_arqos;

wire                        ifu_axi_rvalid;
wire                        ifu_axi_rready;
wire [`RV_IFU_BUS_TAG-1:0]  ifu_axi_rid;
wire [63:0]                 ifu_axi_rdata;
wire [1:0]                  ifu_axi_rresp;
wire                        ifu_axi_rlast;

//-------------------------- SB AXI signals--------------------------
// AXI Write Channels
wire                        sb_axi_awvalid;
wire                        sb_axi_awready;
wire [`RV_SB_BUS_TAG-1:0]   sb_axi_awid;
wire [31:0]                 sb_axi_awaddr;
wire [3:0]                  sb_axi_awregion;
wire [7:0]                  sb_axi_awlen;
wire [2:0]                  sb_axi_awsize;
wire [1:0]                  sb_axi_awburst;
wire                        sb_axi_awlock;
wire [3:0]                  sb_axi_awcache;
wire [2:0]                  sb_axi_awprot;
wire [3:0]                  sb_axi_awqos;

wire                        sb_axi_wvalid;
wire                        sb_axi_wready;
wire [63:0]                 sb_axi_wdata;
wire [7:0]                  sb_axi_wstrb;
wire                        sb_axi_wlast;

wire                        sb_axi_bvalid;
wire                        sb_axi_bready;
wire [1:0]                  sb_axi_bresp;
wire [`RV_SB_BUS_TAG-1:0]   sb_axi_bid;

// AXI Read Channels
wire                        sb_axi_arvalid;
wire                        sb_axi_arready;
wire [`RV_SB_BUS_TAG-1:0]   sb_axi_arid;
wire [31:0]                 sb_axi_araddr;
wire [3:0]                  sb_axi_arregion;
wire [7:0]                  sb_axi_arlen;
wire [2:0]                  sb_axi_arsize;
wire [1:0]                  sb_axi_arburst;
wire                        sb_axi_arlock;
wire [3:0]                  sb_axi_arcache;
wire [2:0]                  sb_axi_arprot;
wire [3:0]                  sb_axi_arqos;

wire                        sb_axi_rvalid;
wire                        sb_axi_rready;
wire [`RV_SB_BUS_TAG-1:0]   sb_axi_rid;
wire [63:0]                 sb_axi_rdata;
wire [1:0]                  sb_axi_rresp;
wire                        sb_axi_rlast;
wire                        sb_axi_awuser;
wire                        sb_axi_wuser;
wire                        sb_axi_buser;
wire                        sb_axi_aruser;
wire                        sb_axi_ruser;

//-------------------------- DMA AXI signals--------------------------
// AXI Write Channels
wire                        dma_axi_awvalid;
wire                        dma_axi_awready;
wire [`RV_DMA_BUS_TAG-1:0]  dma_axi_awid;
wire [31:0]                 dma_axi_awaddr;
wire [2:0]                  dma_axi_awsize;
wire [2:0]                  dma_axi_awprot;
wire [7:0]                  dma_axi_awlen;
wire [1:0]                  dma_axi_awburst;


wire                        dma_axi_wvalid;
wire                        dma_axi_wready;
wire [63:0]                 dma_axi_wdata;
wire [7:0]                  dma_axi_wstrb;
wire                        dma_axi_wlast;

wire                        dma_axi_bvalid;
wire                        dma_axi_bready;
wire [1:0]                  dma_axi_bresp;
wire [`RV_DMA_BUS_TAG-1:0]  dma_axi_bid;

// AXI Read Channels
wire                        dma_axi_arvalid;
wire                        dma_axi_arready;
wire [`RV_DMA_BUS_TAG-1:0]  dma_axi_arid;
wire [31:0]                 dma_axi_araddr;
wire [2:0]                  dma_axi_arsize;
wire [2:0]                  dma_axi_arprot;
wire [7:0]                  dma_axi_arlen;
wire [1:0]                  dma_axi_arburst;

wire                        dma_axi_rvalid;
wire                        dma_axi_rready;
wire [`RV_DMA_BUS_TAG-1:0]  dma_axi_rid;
wire [63:0]                 dma_axi_rdata;
wire [1:0]                  dma_axi_rresp;
wire                        dma_axi_rlast;

//-------------------------- Intermediate AXI signals--------------------------

wire                        lmem_axi_arvalid;
wire                        lmem_axi_arready;
wire                        lmem_axi_rvalid;
wire [RV_MUX_BUS_TAG-1:0]   lmem_axi_rid;
wire [1:0]                  lmem_axi_rresp;
wire [63:0]                 lmem_axi_rdata;
wire                        lmem_axi_rlast;
wire                        lmem_axi_rready;

wire                        lmem_axi_awvalid;
wire                        lmem_axi_awready;

wire                        lmem_axi_wvalid;
wire                        lmem_axi_wready;

wire [1:0]                  lmem_axi_bresp;
wire                        lmem_axi_bvalid;
wire [RV_MUX_BUS_TAG-1:0]   lmem_axi_bid;
wire                        lmem_axi_bready;

wire                        mux_axi_awvalid;
wire                        mux_axi_awready;
wire [RV_MUX_BUS_TAG-1:0]   mux_axi_awid;
wire [31:0]                 mux_axi_awaddr;
wire [3:0]                  mux_axi_awregion;
wire [7:0]                  mux_axi_awlen;
wire [2:0]                  mux_axi_awsize;
wire [1:0]                  mux_axi_awburst;
wire                        mux_axi_awlock;
wire [3:0]                  mux_axi_awcache;
wire [2:0]                  mux_axi_awprot;
wire [3:0]                  mux_axi_awqos;

wire                        mux_axi_wvalid;
wire                        mux_axi_wready;
wire [63:0]                 mux_axi_wdata;
wire [7:0]                  mux_axi_wstrb;
wire                        mux_axi_wlast;

wire                        mux_axi_bvalid;
wire                        mux_axi_bready;
wire [1:0]                  mux_axi_bresp;
wire [RV_MUX_BUS_TAG-1:0]   mux_axi_bid;

// AXI Read Channels
wire                        mux_axi_arvalid;
wire                        mux_axi_arready;
wire [RV_MUX_BUS_TAG-1:0]   mux_axi_arid;
wire [31:0]                 mux_axi_araddr;
wire [3:0]                  mux_axi_arregion;
wire [7:0]                  mux_axi_arlen;
wire [2:0]                  mux_axi_arsize;
wire [1:0]                  mux_axi_arburst;
wire                        mux_axi_arlock;
wire [3:0]                  mux_axi_arcache;
wire [2:0]                  mux_axi_arprot;
wire [3:0]                  mux_axi_arqos;

wire                        mux_axi_rvalid;
wire                        mux_axi_rready;
wire [RV_MUX_BUS_TAG-1:0]   mux_axi_rid;
wire [63:0]                 mux_axi_rdata;
wire [1:0]                  mux_axi_rresp;
wire                        mux_axi_rlast;
wire                        mux_axi_awuser;
wire                        mux_axi_wuser;
wire                        mux_axi_buser;
wire                        mux_axi_aruser;
wire                        mux_axi_ruser;

// AXI LSU and SB 2:1 crossbar
axi_crossbar_wrap_2x1 #(
    .ADDR_WIDTH     (32),
    .DATA_WIDTH     (64),
    .S_ID_WIDTH     (RV_MUX_BUS_TAG - 1),
    .M00_ADDR_WIDTH (32)

) u_axi_crossbar (

  .clk              (core_clk),
  .rst              (!rst_l_combined),

  // LSU
  .s00_axi_arvalid  (lsu_axi_arvalid),
  .s00_axi_arready  (lsu_axi_arready),
  .s00_axi_araddr   (lsu_axi_araddr),
  .s00_axi_arid     (lsu_axi_arid),
  .s00_axi_arlen    (lsu_axi_arlen),
  .s00_axi_arburst  (lsu_axi_arburst),
  .s00_axi_arsize   (lsu_axi_arsize),

  .s00_axi_rvalid   (lsu_axi_rvalid),
  .s00_axi_rready   (lsu_axi_rready),
  .s00_axi_rdata    (lsu_axi_rdata),
  .s00_axi_rresp    (lsu_axi_rresp),
  .s00_axi_rid      (lsu_axi_rid),
  .s00_axi_rlast    (lsu_axi_rlast),

  .s00_axi_awvalid  (lsu_axi_awvalid),
  .s00_axi_awready  (lsu_axi_awready),
  .s00_axi_awaddr   (lsu_axi_awaddr),
  .s00_axi_awid     (lsu_axi_awid),
  .s00_axi_awlen    (lsu_axi_awlen),
  .s00_axi_awburst  (lsu_axi_awburst),
  .s00_axi_awlock   (lsu_axi_awlock),
  .s00_axi_awcache  (lsu_axi_awcache),
  .s00_axi_awprot   (lsu_axi_awprot),
  .s00_axi_awqos    (lsu_axi_awqos),
  .s00_axi_awuser   (lsu_axi_awuser),
  .s00_axi_wlast    (lsu_axi_wlast),
  .s00_axi_wuser    (lsu_axi_wuser),
  .s00_axi_buser    (lsu_axi_buser),
  .s00_axi_arlock   (lsu_axi_arlock),
  .s00_axi_arcache  (lsu_axi_arcache),
  .s00_axi_arprot   (lsu_axi_arprot),
  .s00_axi_arqos    (lsu_axi_arqos),
  .s00_axi_aruser   (lsu_axi_aruser),
  .s00_axi_ruser    (lsu_axi_ruser),
  .s00_axi_awsize   (lsu_axi_awsize),

  .s00_axi_wdata    (lsu_axi_wdata),
  .s00_axi_wstrb    (lsu_axi_wstrb),
  .s00_axi_wvalid   (lsu_axi_wvalid),
  .s00_axi_wready   (lsu_axi_wready),

  .s00_axi_bvalid   (lsu_axi_bvalid),
  .s00_axi_bready   (lsu_axi_bready),
  .s00_axi_bresp    (lsu_axi_bresp),
  .s00_axi_bid      (lsu_axi_bid),

  // SB
  .s01_axi_arvalid  (sb_axi_arvalid),
  .s01_axi_arready  (sb_axi_arready),
  .s01_axi_araddr   (sb_axi_araddr),
  .s01_axi_arid     (sb_axi_arid),
  .s01_axi_arlen    (sb_axi_arlen),
  .s01_axi_arburst  (sb_axi_arburst),
  .s01_axi_arsize   (sb_axi_arsize),

  .s01_axi_rvalid   (sb_axi_rvalid),
  .s01_axi_rready   (sb_axi_rready),
  .s01_axi_rdata    (sb_axi_rdata),
  .s01_axi_rresp    (sb_axi_rresp),
  .s01_axi_rid      (sb_axi_rid),
  .s01_axi_rlast    (sb_axi_rlast),

  .s01_axi_awvalid  (sb_axi_awvalid),
  .s01_axi_awready  (sb_axi_awready),
  .s01_axi_awaddr   (sb_axi_awaddr),
  .s01_axi_awid     (sb_axi_awid),
  .s01_axi_awlen    (sb_axi_awlen),
  .s01_axi_awburst  (sb_axi_awburst),
  .s01_axi_awlock   (sb_axi_awlock),
  .s01_axi_awcache  (sb_axi_awcache),
  .s01_axi_awprot   (sb_axi_awprot),
  .s01_axi_awqos    (sb_axi_awqos),
  .s01_axi_awuser   (sb_axi_awuser),
  .s01_axi_wlast    (sb_axi_wlast),
  .s01_axi_wuser    (sb_axi_wuser),
  .s01_axi_buser    (sb_axi_buser),
  .s01_axi_arlock   (sb_axi_arlock),
  .s01_axi_arcache  (sb_axi_arcache),
  .s01_axi_arprot   (sb_axi_arprot),
  .s01_axi_arqos    (sb_axi_arqos),
  .s01_axi_aruser   (sb_axi_aruser),
  .s01_axi_ruser    (sb_axi_ruser),
  .s01_axi_awsize   (sb_axi_awsize),

  .s01_axi_wdata    (sb_axi_wdata),
  .s01_axi_wstrb    (sb_axi_wstrb),
  .s01_axi_wvalid   (sb_axi_wvalid),
  .s01_axi_wready   (sb_axi_wready),

  .s01_axi_bvalid   (sb_axi_bvalid),
  .s01_axi_bready   (sb_axi_bready),
  .s01_axi_bresp    (sb_axi_bresp),
  .s01_axi_bid      (sb_axi_bid),

  // Output
  .m00_axi_arvalid  (mux_axi_arvalid),
  .m00_axi_arready  (mux_axi_arready),
  .m00_axi_araddr   (mux_axi_araddr),
  .m00_axi_arid     (mux_axi_arid),
  .m00_axi_arlen    (mux_axi_arlen),
  .m00_axi_arburst  (mux_axi_arburst),
  .m00_axi_arsize   (mux_axi_arsize),

  .m00_axi_rvalid   (mux_axi_rvalid),
  .m00_axi_rready   (mux_axi_rready),
  .m00_axi_rdata    (mux_axi_rdata),
  .m00_axi_rresp    (mux_axi_rresp),
  .m00_axi_rid      (mux_axi_rid),
  .m00_axi_rlast    (mux_axi_rlast),

  .m00_axi_awvalid  (mux_axi_awvalid),
  .m00_axi_awready  (mux_axi_awready),
  .m00_axi_awaddr   (mux_axi_awaddr),
  .m00_axi_awid     (mux_axi_awid),
  .m00_axi_awlen    (mux_axi_awlen),
  .m00_axi_awburst  (mux_axi_awburst),
  .m00_axi_awlock   (mux_axi_awlock),
  .m00_axi_awcache  (mux_axi_awcache),
  .m00_axi_awprot   (mux_axi_awprot),
  .m00_axi_awqos    (mux_axi_awqos),
  .m00_axi_awuser   (mux_axi_awuser),
  .m00_axi_wlast    (mux_axi_wlast),
  .m00_axi_wuser    (mux_axi_wuser),
  .m00_axi_buser    (mux_axi_buser),
  .m00_axi_arlock   (mux_axi_arlock),
  .m00_axi_arcache  (mux_axi_arcache),
  .m00_axi_arprot   (mux_axi_arprot),
  .m00_axi_arqos    (mux_axi_arqos),
  .m00_axi_aruser   (mux_axi_aruser),
  .m00_axi_ruser    (mux_axi_ruser),
  .m00_axi_awsize   (mux_axi_awsize),

  .m00_axi_wdata    (mux_axi_wdata),
  .m00_axi_wstrb    (mux_axi_wstrb),
  .m00_axi_wvalid   (mux_axi_wvalid),
  .m00_axi_wready   (mux_axi_wready),

  .m00_axi_bvalid   (mux_axi_bvalid),
  .m00_axi_bready   (mux_axi_bready),
  .m00_axi_bresp    (mux_axi_bresp),
  .m00_axi_bid      (mux_axi_bid),
  .m00_axi_awregion (mux_axi_awregion),
  .m00_axi_arregion (mux_axi_arregion)
);

// AXI DMA Bridge
axi_lsu_dma_bridge # (RV_MUX_BUS_TAG, RV_MUX_BUS_TAG) bridge (
  .clk        (core_clk),
  .reset_l    (rst_l_combined),

  .m_arvalid  (mux_axi_arvalid),
  .m_arid     (mux_axi_arid),
  .m_araddr   (mux_axi_araddr),
  .m_arready  (mux_axi_arready),

  .m_rvalid   (mux_axi_rvalid),
  .m_rready   (mux_axi_rready),
  .m_rdata    (mux_axi_rdata),
  .m_rid      (mux_axi_rid),
  .m_rresp    (mux_axi_rresp),
  .m_rlast    (mux_axi_rlast),

  .m_awvalid  (mux_axi_awvalid),
  .m_awid     (mux_axi_awid),
  .m_awaddr   (mux_axi_awaddr),
  .m_awready  (mux_axi_awready),

  .m_wvalid   (mux_axi_wvalid),
  .m_wready   (mux_axi_wready),

  .m_bresp    (mux_axi_bresp),
  .m_bvalid   (mux_axi_bvalid),
  .m_bid      (mux_axi_bid),
  .m_bready   (mux_axi_bready),


  .s0_arvalid (lmem_axi_arvalid),
  .s0_arready (lmem_axi_arready),

  .s0_rvalid  (lmem_axi_rvalid),
  .s0_rid     (lmem_axi_rid),
  .s0_rresp   (lmem_axi_rresp),
  .s0_rdata   (lmem_axi_rdata),
  .s0_rlast   (lmem_axi_rlast),
  .s0_rready  (lmem_axi_rready),

  .s0_awvalid (lmem_axi_awvalid),
  .s0_awready (lmem_axi_awready),

  .s0_wvalid  (lmem_axi_wvalid),
  .s0_wready  (lmem_axi_wready),

  .s0_bresp   (lmem_axi_bresp),
  .s0_bvalid  (lmem_axi_bvalid),
  .s0_bid     (lmem_axi_bid),
  .s0_bready  (lmem_axi_bready),


  .s1_arvalid (dma_axi_arvalid),
  .s1_arready (dma_axi_arready),

  .s1_rvalid  (dma_axi_rvalid),
  .s1_rresp   (dma_axi_rresp),
  .s1_rdata   (dma_axi_rdata),
  .s1_rlast   (dma_axi_rlast),
  .s1_rready  (dma_axi_rready),

  .s1_awvalid (dma_axi_awvalid),
  .s1_awready (dma_axi_awready),

  .s1_wvalid  (dma_axi_wvalid),
  .s1_wready  (dma_axi_wready),

  .s1_bresp   (dma_axi_bresp),
  .s1_bvalid  (dma_axi_bvalid),
  .s1_bready  (dma_axi_bready)
);

axi_slv # (
  .TAGW(`RV_IFU_BUS_TAG)

) imem (

  .aclk    (core_clk),
  .rst_l   (rst_l_combined),

  .arvalid (ifu_axi_arvalid),
  .arready (ifu_axi_arready),
  .araddr  (ifu_axi_araddr),
  .arid    (ifu_axi_arid),
  .arlen   (ifu_axi_arlen),
  .arburst (ifu_axi_arburst),
  .arsize  (ifu_axi_arsize),

  .rvalid  (ifu_axi_rvalid),
  .rready  (ifu_axi_rready),
  .rdata   (ifu_axi_rdata),
  .rresp   (ifu_axi_rresp),
  .rid     (ifu_axi_rid),
  .rlast   (ifu_axi_rlast),

  .awvalid (1'b0),
  .awready (),
  .awaddr  ('0),
  .awid    ('0),
  .awlen   ('0),
  .awburst ('0),
  .awsize  ('0),

  .wdata   ('0),
  .wstrb   ('0),
  .wvalid  (1'b0),
  .wready  (),

  .bvalid  (),
  .bready  (1'b0),
  .bresp   (),
  .bid     ()
);

defparam lmem.TAGW = RV_MUX_BUS_TAG;
//axi_slv #(.TAGW(`RV_LSU_BUS_TAG)) lmem(
axi_slv lmem (

  .aclk    (core_clk),
  .rst_l   (rst_l_combined),

  .arvalid (lmem_axi_arvalid),
  .arready (lmem_axi_arready),
  .araddr  (mux_axi_araddr),
  .arid    (mux_axi_arid),
  .arlen   (mux_axi_arlen),
  .arburst (mux_axi_arburst),
  .arsize  (mux_axi_arsize),

  .rvalid  (lmem_axi_rvalid),
  .rready  (lmem_axi_rready),
  .rdata   (lmem_axi_rdata),
  .rresp   (lmem_axi_rresp),
  .rid     (lmem_axi_rid),
  .rlast   (lmem_axi_rlast),

  .awvalid (lmem_axi_awvalid),
  .awready (lmem_axi_awready),
  .awaddr  (mux_axi_awaddr),
  .awid    (mux_axi_awid),
  .awlen   (mux_axi_awlen),
  .awburst (mux_axi_awburst),
  .awsize  (mux_axi_awsize),

  .wdata   (mux_axi_wdata),
  .wstrb   (mux_axi_wstrb),
  .wvalid  (lmem_axi_wvalid),
  .wready  (lmem_axi_wready),

  .bvalid  (lmem_axi_bvalid),
  .bready  (lmem_axi_bready),
  .bresp   (lmem_axi_bresp),
  .bid     (lmem_axi_bid)
);

`endif // RV_BUILD_AXI4

// ------------------------------------------------------------------
// DCCM
// ------------------------------------------------------------------
if (pt.DCCM_ENABLE == 1) begin: Gen_dccm_enable
    `define EL2_LOCAL_DCCM_RAM_TEST_PORTS   .TEST1   (1'b0   ), \
                                            .RME     (1'b0   ), \
                                            .RM      (4'b0000), \
                                            .LS      (1'b0   ), \
                                            .DS      (1'b0   ), \
                                            .SD      (1'b0   ), \
                                            .TEST_RNM(1'b0   ), \
                                            .BC1     (1'b0   ), \
                                            .BC2     (1'b0   ), \

    localparam DCCM_INDEX_DEPTH = ((pt.DCCM_SIZE)*1024)/((pt.DCCM_BYTE_WIDTH)*(pt.DCCM_NUM_BANKS));  // Depth of memory bank

    // 8 Banks, 16KB each (2048 x 72)
    logic [pt.DCCM_NUM_BANKS-1:0][pt.DCCM_FDATA_WIDTH-1:0] dccm_wr_fdata_bank;
    logic [pt.DCCM_NUM_BANKS-1:0][pt.DCCM_FDATA_WIDTH-1:0] dccm_bank_fdout;

    for (genvar i=0; i<pt.DCCM_NUM_BANKS; i++) begin: dccm_loop
        assign dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0] = {el2_mem_export.dccm_wr_ecc_bank[i], el2_mem_export.dccm_wr_data_bank[i]};
        assign el2_mem_export.dccm_bank_dout[i] = dccm_bank_fdout[i][31:0];
        assign el2_mem_export.dccm_bank_ecc[i]  = dccm_bank_fdout[i][38:32];

        if (DCCM_INDEX_DEPTH == 32768) begin : dccm
            ram_32768x39  dccm_bank (
                                    // Primary ports
                                    .ME(el2_mem_export.dccm_clken[i]),
                                    .CLK(el2_mem_export.clk),
                                    .WE(el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 16384) begin : dccm
            ram_16384x39  dccm_bank (
                                    // Primary ports
                                    .ME(el2_mem_export.dccm_clken[i]),
                                    .CLK(el2_mem_export.clk),
                                    .WE(el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 8192) begin : dccm
            ram_8192x39  dccm_bank (
                                    // Primary ports
                                    .ME(el2_mem_export.dccm_clken[i]),
                                    .CLK(el2_mem_export.clk),
                                    .WE(el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 4096) begin : dccm
            ram_4096x39  dccm_bank (
                                    // Primary ports
                                    .ME(el2_mem_export.dccm_clken[i]),
                                    .CLK(el2_mem_export.clk),
                                    .WE(el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 3072) begin : dccm
            ram_3072x39  dccm_bank (
                                    // Primary ports
                                    .ME(el2_mem_export.dccm_clken[i]),
                                    .CLK(el2_mem_export.clk),
                                    .WE(el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 2048) begin : dccm
            ram_2048x39  dccm_bank (
                                    // Primary ports
                                    .ME(el2_mem_export.dccm_clken[i]),
                                    .CLK(el2_mem_export.clk),
                                    .WE(el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 1024) begin : dccm
            ram_1024x39  dccm_bank (
                                    // Primary ports
                                    .ME(el2_mem_export.dccm_clken[i]),
                                    .CLK(el2_mem_export.clk),
                                    .WE(el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 512) begin : dccm
            ram_512x39  dccm_bank (
                                    // Primary ports
                                    .ME(el2_mem_export.dccm_clken[i]),
                                    .CLK(el2_mem_export.clk),
                                    .WE(el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 256) begin : dccm
            ram_256x39  dccm_bank (
                                    // Primary ports
                                    .ME(el2_mem_export.dccm_clken[i]),
                                    .CLK(el2_mem_export.clk),
                                    .WE(el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
        else if (DCCM_INDEX_DEPTH == 128) begin : dccm
            ram_128x39  dccm_bank (
                                    // Primary ports
                                    .ME(el2_mem_export.dccm_clken[i]),
                                    .CLK(el2_mem_export.clk),
                                    .WE(el2_mem_export.dccm_wren_bank[i]),
                                    .ADR(el2_mem_export.dccm_addr_bank[i]),
                                    .D(dccm_wr_fdata_bank[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .Q(dccm_bank_fdout[i][pt.DCCM_FDATA_WIDTH-1:0]),
                                    .ROP ( ),
                                    // These are used by SoC
                                    `EL2_LOCAL_DCCM_RAM_TEST_PORTS
                                    .*
                                    );
        end
    end : dccm_loop
end :Gen_dccm_enable

// ------------------------------------------------------------------
// ICCM
// ------------------------------------------------------------------
if (pt.ICCM_ENABLE) begin : Gen_iccm_enable
  logic [pt.ICCM_NUM_BANKS-1:0][38:0] iccm_bank_wr_fdata;
  logic [pt.ICCM_NUM_BANKS-1:0][38:0] iccm_bank_fdout;

    for (genvar i=0; i<pt.ICCM_NUM_BANKS; i++) begin: iccm_loop
        assign iccm_bank_wr_fdata[i][32+pt.ICCM_ECC_WIDTH-1:0] = {el2_mem_export.iccm_bank_wr_ecc[i], el2_mem_export.iccm_bank_wr_data[i]};
        assign el2_mem_export.iccm_bank_dout[i] = iccm_bank_fdout[i][31:0];
        assign el2_mem_export.iccm_bank_ecc[i]  = iccm_bank_fdout[i][32+pt.ICCM_ECC_WIDTH-1:32];

         if (pt.ICCM_INDEX_BITS == 6 ) begin : iccm
                   ram_64x39 iccm_bank (
                                         // Primary ports
                                         .CLK(el2_mem_export.clk),
                                         .ME(el2_mem_export.iccm_clken[i]),
                                         .WE(el2_mem_export.iccm_wren_bank[i]),
                                         .ADR(el2_mem_export.iccm_addr_bank[i]),
                                         .D(iccm_bank_wr_fdata[i][38:0]),
                                         .Q(iccm_bank_fdout[i][38:0]),
                                         .ROP ( ),
                                         // These are used by SoC
                                         .TEST1    (1'b0   ),
                                         .RME      (1'b0   ),
                                         .RM       (4'b0000),
                                         .LS       (1'b0   ),
                                         .DS       (1'b0   ),
                                         .SD       (1'b0   ) ,
                                         .TEST_RNM (1'b0   ),
                                         .BC1      (1'b0   ),
                                         .BC2      (1'b0   )

                                          );
         end // block: iccm

       else if (pt.ICCM_INDEX_BITS == 7 ) begin : iccm
                   ram_128x39 iccm_bank (
                                         // Primary ports
                                         .CLK(el2_mem_export.clk),
                                         .ME(el2_mem_export.iccm_clken[i]),
                                         .WE(el2_mem_export.iccm_wren_bank[i]),
                                         .ADR(el2_mem_export.iccm_addr_bank[i]),
                                         .D(iccm_bank_wr_fdata[i][38:0]),
                                         .Q(iccm_bank_fdout[i][38:0]),
                                         .ROP ( ),
                                         // These are used by SoC
                                         .TEST1    (1'b0   ),
                                         .RME      (1'b0   ),
                                         .RM       (4'b0000),
                                         .LS       (1'b0   ),
                                         .DS       (1'b0   ),
                                         .SD       (1'b0   ) ,
                                         .TEST_RNM (1'b0   ),
                                         .BC1      (1'b0   ),
                                         .BC2      (1'b0   )

                                          );
         end // block: iccm

         else if (pt.ICCM_INDEX_BITS == 8 ) begin : iccm
                   ram_256x39 iccm_bank (
                                         // Primary ports
                                         .CLK(el2_mem_export.clk),
                                         .ME(el2_mem_export.iccm_clken[i]),
                                         .WE(el2_mem_export.iccm_wren_bank[i]),
                                         .ADR(el2_mem_export.iccm_addr_bank[i]),
                                         .D(iccm_bank_wr_fdata[i][38:0]),
                                         .Q(iccm_bank_fdout[i][38:0]),
                                         .ROP ( ),
                                         // These are used by SoC
                                         .TEST1    (1'b0   ),
                                         .RME      (1'b0   ),
                                         .RM       (4'b0000),
                                         .LS       (1'b0   ),
                                         .DS       (1'b0   ),
                                         .SD       (1'b0   ) ,
                                         .TEST_RNM (1'b0   ),
                                         .BC1      (1'b0   ),
                                         .BC2      (1'b0   )

                                          );
         end // block: iccm
         else if (pt.ICCM_INDEX_BITS == 9 ) begin : iccm
                   ram_512x39 iccm_bank (
                                         // Primary ports
                                         .CLK(el2_mem_export.clk),
                                         .ME(el2_mem_export.iccm_clken[i]),
                                         .WE(el2_mem_export.iccm_wren_bank[i]),
                                         .ADR(el2_mem_export.iccm_addr_bank[i]),
                                         .D(iccm_bank_wr_fdata[i][38:0]),
                                         .Q(iccm_bank_fdout[i][38:0]),
                                         .ROP ( ),
                                         // These are used by SoC
                                         .TEST1    (1'b0   ),
                                         .RME      (1'b0   ),
                                         .RM       (4'b0000),
                                         .LS       (1'b0   ),
                                         .DS       (1'b0   ),
                                         .SD       (1'b0   ) ,
                                         .TEST_RNM (1'b0   ),
                                         .BC1      (1'b0   ),
                                         .BC2      (1'b0   )

                                          );
         end // block: iccm
         else if (pt.ICCM_INDEX_BITS == 10 ) begin : iccm
                   ram_1024x39 iccm_bank (
                                         // Primary ports
                                         .CLK(el2_mem_export.clk),
                                         .ME(el2_mem_export.iccm_clken[i]),
                                         .WE(el2_mem_export.iccm_wren_bank[i]),
                                         .ADR(el2_mem_export.iccm_addr_bank[i]),
                                         .D(iccm_bank_wr_fdata[i][38:0]),
                                         .Q(iccm_bank_fdout[i][38:0]),
                                         .ROP ( ),
                                         // These are used by SoC
                                         .TEST1    (1'b0   ),
                                         .RME      (1'b0   ),
                                         .RM       (4'b0000),
                                         .LS       (1'b0   ),
                                         .DS       (1'b0   ),
                                         .SD       (1'b0   ) ,
                                         .TEST_RNM (1'b0   ),
                                         .BC1      (1'b0   ),
                                         .BC2      (1'b0   )

                                          );
         end // block: iccm
         else if (pt.ICCM_INDEX_BITS == 11 ) begin : iccm
                   ram_2048x39 iccm_bank (
                                         // Primary ports
                                         .CLK(el2_mem_export.clk),
                                         .ME(el2_mem_export.iccm_clken[i]),
                                         .WE(el2_mem_export.iccm_wren_bank[i]),
                                         .ADR(el2_mem_export.iccm_addr_bank[i]),
                                         .D(iccm_bank_wr_fdata[i][38:0]),
                                         .Q(iccm_bank_fdout[i][38:0]),
                                         .ROP ( ),
                                         // These are used by SoC
                                         .TEST1    (1'b0   ),
                                         .RME      (1'b0   ),
                                         .RM       (4'b0000),
                                         .LS       (1'b0   ),
                                         .DS       (1'b0   ),
                                         .SD       (1'b0   ) ,
                                         .TEST_RNM (1'b0   ),
                                         .BC1      (1'b0   ),
                                         .BC2      (1'b0   )

                                          );
         end // block: iccm
         else if (pt.ICCM_INDEX_BITS == 12 ) begin : iccm
                   ram_4096x39 iccm_bank (
                                         // Primary ports
                                         .CLK(el2_mem_export.clk),
                                         .ME(el2_mem_export.iccm_clken[i]),
                                         .WE(el2_mem_export.iccm_wren_bank[i]),
                                         .ADR(el2_mem_export.iccm_addr_bank[i]),
                                         .D(iccm_bank_wr_fdata[i][38:0]),
                                         .Q(iccm_bank_fdout[i][38:0]),
                                         .ROP ( ),
                                         // These are used by SoC
                                         .TEST1    (1'b0   ),
                                         .RME      (1'b0   ),
                                         .RM       (4'b0000),
                                         .LS       (1'b0   ),
                                         .DS       (1'b0   ),
                                         .SD       (1'b0   ) ,
                                         .TEST_RNM (1'b0   ),
                                         .BC1      (1'b0   ),
                                         .BC2      (1'b0   )

                                          );
         end // block: iccm
         else if (pt.ICCM_INDEX_BITS == 13 ) begin : iccm
                   ram_8192x39 iccm_bank (
                                         // Primary ports
                                         .CLK(el2_mem_export.clk),
                                         .ME(el2_mem_export.iccm_clken[i]),
                                         .WE(el2_mem_export.iccm_wren_bank[i]),
                                         .ADR(el2_mem_export.iccm_addr_bank[i]),
                                         .D(iccm_bank_wr_fdata[i][38:0]),
                                         .Q(iccm_bank_fdout[i][38:0]),
                                         .ROP ( ),
                                         // These are used by SoC
                                         .TEST1    (1'b0   ),
                                         .RME      (1'b0   ),
                                         .RM       (4'b0000),
                                         .LS       (1'b0   ),
                                         .DS       (1'b0   ),
                                         .SD       (1'b0   ) ,
                                         .TEST_RNM (1'b0   ),
                                         .BC1      (1'b0   ),
                                         .BC2      (1'b0   )

                                          );
         end // block: iccm
         else if (pt.ICCM_INDEX_BITS == 14 ) begin : iccm
                   ram_16384x39 iccm_bank (
                                         // Primary ports
                                         .CLK(el2_mem_export.clk),
                                         .ME(el2_mem_export.iccm_clken[i]),
                                         .WE(el2_mem_export.iccm_wren_bank[i]),
                                         .ADR(el2_mem_export.iccm_addr_bank[i]),
                                         .D(iccm_bank_wr_fdata[i][38:0]),
                                         .Q(iccm_bank_fdout[i][38:0]),
                                         .ROP ( ),
                                         // These are used by SoC
                                         .TEST1    (1'b0   ),
                                         .RME      (1'b0   ),
                                         .RM       (4'b0000),
                                         .LS       (1'b0   ),
                                         .DS       (1'b0   ),
                                         .SD       (1'b0   ) ,
                                         .TEST_RNM (1'b0   ),
                                         .BC1      (1'b0   ),
                                         .BC2      (1'b0   )

                                          );
         end // block: iccm
         else begin : iccm
                   ram_32768x39 iccm_bank (
                                         // Primary ports
                                         .CLK(el2_mem_export.clk),
                                         .ME(el2_mem_export.iccm_clken[i]),
                                         .WE(el2_mem_export.iccm_wren_bank[i]),
                                         .ADR(el2_mem_export.iccm_addr_bank[i]),
                                         .D(iccm_bank_wr_fdata[i][38:0]),
                                         .Q(iccm_bank_fdout[i][38:0]),
                                         .ROP ( ),
                                         // These are used by SoC
                                         .TEST1    (1'b0   ),
                                         .RME      (1'b0   ),
                                         .RM       (4'b0000),
                                         .LS       (1'b0   ),
                                         .DS       (1'b0   ),
                                         .SD       (1'b0   ) ,
                                         .TEST_RNM (1'b0   ),
                                         .BC1      (1'b0   ),
                                         .BC2      (1'b0   )

                                          );
         end // block: iccm
    end : iccm_loop
end : Gen_iccm_enable


// ------------------------------------------------------------------
// VeeR core
// ------------------------------------------------------------------

veer_wrapper rvtop_wrapper (
    .rst_l                  (rst_l_combined ),
    .dbg_rst_l              (porst_l       ),
    .clk                    (core_clk      ),
    .rst_vec                (`RV_RESET_VEC >> 1), // rst_vec is [31:1]
    .nmi_int                (nmi_int       ),
    .nmi_vec                (32'hEE000000),
    .jtag_id                (jtag_id[31:1]),

`ifdef RV_BUILD_AHB_LITE
    .haddr                  (ic_haddr      ),
    .hburst                 (ic_hburst     ),
    .hmastlock              (ic_hmastlock  ),
    .hprot                  (ic_hprot      ),
    .hsize                  (ic_hsize      ),
    .htrans                 (ic_htrans     ),
    .hwrite                 (ic_hwrite     ),
    .hrdata                 (ic_hrdata[63:0]),
    .hready                 (ic_hready     ),
    .hresp                  (ic_hresp      ),

    //---------------------------------------------------------------
    // Debug AHB Master
    //---------------------------------------------------------------
    .sb_haddr               (sb_haddr      ),
    .sb_hburst              (sb_hburst     ),
    .sb_hmastlock           (sb_hmastlock  ),
    .sb_hprot               (sb_hprot      ),
    .sb_hsize               (sb_hsize      ),
    .sb_htrans              (sb_htrans     ),
    .sb_hwrite              (sb_hwrite     ),
    .sb_hwdata              (sb_hwdata     ),

    .sb_hrdata              (sb_hrdata     ),
    .sb_hready              (sb_hready     ),
    .sb_hresp               (sb_hresp      ),

    //---------------------------------------------------------------
    // LSU AHB Master
    //---------------------------------------------------------------
    .lsu_haddr              (lsu_haddr       ),
    .lsu_hburst             (lsu_hburst      ),
    .lsu_hmastlock          (lsu_hmastlock   ),
    .lsu_hprot              (lsu_hprot       ),
    .lsu_hsize              (lsu_hsize       ),
    .lsu_htrans             (lsu_htrans      ),
    .lsu_hwrite             (lsu_hwrite      ),
    .lsu_hwdata             (lsu_hwdata      ),

    .lsu_hrdata             (lsu_hrdata[63:0]),
    .lsu_hready             (lsu_hready      ),
    .lsu_hresp              (lsu_hresp       ),

    //---------------------------------------------------------------
    // DMA Slave
    //---------------------------------------------------------------
    .dma_haddr              (dma_haddr),
    .dma_hburst             (dma_hburst),
    .dma_hmastlock          (dma_hmastlock),
    .dma_hprot              (dma_hprot),
    .dma_hsize              (dma_hsize),
    .dma_htrans             (dma_htrans),
    .dma_hwrite             (dma_hwrite),
    .dma_hwdata             (dma_hwdata),

    .dma_hrdata             (dma_hrdata    ),
    .dma_hresp              (dma_hresp     ),
    .dma_hsel               (dma_hsel      ),
    .dma_hreadyin           (dma_hready_out  ),
    .dma_hreadyout          (dma_hready_out  ),

`endif // RV_BUILD_AHB_LITE
`ifdef RV_BUILD_AXI4

    //-------------------------- LSU AXI signals--------------------------
    // AXI Write Channels
    .lsu_axi_awvalid        (lsu_axi_awvalid),
    .lsu_axi_awready        (lsu_axi_awready),
    .lsu_axi_awid           (lsu_axi_awid),
    .lsu_axi_awaddr         (lsu_axi_awaddr),
    .lsu_axi_awregion       (lsu_axi_awregion),
    .lsu_axi_awlen          (lsu_axi_awlen),
    .lsu_axi_awsize         (lsu_axi_awsize),
    .lsu_axi_awburst        (lsu_axi_awburst),
    .lsu_axi_awlock         (lsu_axi_awlock),
    .lsu_axi_awcache        (lsu_axi_awcache),
    .lsu_axi_awprot         (lsu_axi_awprot),
    .lsu_axi_awqos          (lsu_axi_awqos),

    .lsu_axi_wvalid         (lsu_axi_wvalid),
    .lsu_axi_wready         (lsu_axi_wready),
    .lsu_axi_wdata          (lsu_axi_wdata),
    .lsu_axi_wstrb          (lsu_axi_wstrb),
    .lsu_axi_wlast          (lsu_axi_wlast),

    .lsu_axi_bvalid         (lsu_axi_bvalid),
    .lsu_axi_bready         (lsu_axi_bready),
    .lsu_axi_bresp          (lsu_axi_bresp_override),
    .lsu_axi_bid            (lsu_axi_bid),


    .lsu_axi_arvalid        (lsu_axi_arvalid),
    .lsu_axi_arready        (lsu_axi_arready),
    .lsu_axi_arid           (lsu_axi_arid),
    .lsu_axi_araddr         (lsu_axi_araddr),
    .lsu_axi_arregion       (lsu_axi_arregion),
    .lsu_axi_arlen          (lsu_axi_arlen),
    .lsu_axi_arsize         (lsu_axi_arsize),
    .lsu_axi_arburst        (lsu_axi_arburst),
    .lsu_axi_arlock         (lsu_axi_arlock),
    .lsu_axi_arcache        (lsu_axi_arcache),
    .lsu_axi_arprot         (lsu_axi_arprot),
    .lsu_axi_arqos          (lsu_axi_arqos),

    .lsu_axi_rvalid         (lsu_axi_rvalid),
    .lsu_axi_rready         (lsu_axi_rready),
    .lsu_axi_rid            (lsu_axi_rid),
    .lsu_axi_rdata          (lsu_axi_rdata),
    .lsu_axi_rresp          (lsu_axi_rresp_override),
    .lsu_axi_rlast          (lsu_axi_rlast),

    //-------------------------- IFU AXI signals--------------------------
    // AXI Write Channels
    .ifu_axi_awvalid        (ifu_axi_awvalid),
    .ifu_axi_awready        (ifu_axi_awready),
    .ifu_axi_awid           (ifu_axi_awid),
    .ifu_axi_awaddr         (ifu_axi_awaddr),
    .ifu_axi_awregion       (ifu_axi_awregion),
    .ifu_axi_awlen          (ifu_axi_awlen),
    .ifu_axi_awsize         (ifu_axi_awsize),
    .ifu_axi_awburst        (ifu_axi_awburst),
    .ifu_axi_awlock         (ifu_axi_awlock),
    .ifu_axi_awcache        (ifu_axi_awcache),
    .ifu_axi_awprot         (ifu_axi_awprot),
    .ifu_axi_awqos          (ifu_axi_awqos),

    .ifu_axi_wvalid         (ifu_axi_wvalid),
    .ifu_axi_wready         (ifu_axi_wready),
    .ifu_axi_wdata          (ifu_axi_wdata),
    .ifu_axi_wstrb          (ifu_axi_wstrb),
    .ifu_axi_wlast          (ifu_axi_wlast),

    .ifu_axi_bvalid         (ifu_axi_bvalid),
    .ifu_axi_bready         (ifu_axi_bready),
    .ifu_axi_bresp          (ifu_axi_bresp),
    .ifu_axi_bid            (ifu_axi_bid),

    .ifu_axi_arvalid        (ifu_axi_arvalid),
    .ifu_axi_arready        (ifu_axi_arready),
    .ifu_axi_arid           (ifu_axi_arid),
    .ifu_axi_araddr         (ifu_axi_araddr),
    .ifu_axi_arregion       (ifu_axi_arregion),
    .ifu_axi_arlen          (ifu_axi_arlen),
    .ifu_axi_arsize         (ifu_axi_arsize),
    .ifu_axi_arburst        (ifu_axi_arburst),
    .ifu_axi_arlock         (ifu_axi_arlock),
    .ifu_axi_arcache        (ifu_axi_arcache),
    .ifu_axi_arprot         (ifu_axi_arprot),
    .ifu_axi_arqos          (ifu_axi_arqos),

    .ifu_axi_rvalid         (ifu_axi_rvalid),
    .ifu_axi_rready         (ifu_axi_rready),
    .ifu_axi_rid            (ifu_axi_rid),
    .ifu_axi_rdata          (ifu_axi_rdata),
    .ifu_axi_rresp          (ifu_axi_rresp_override),
    .ifu_axi_rlast          (ifu_axi_rlast),

    //-------------------------- SB AXI signals--------------------------
    // AXI Write Channels
    .sb_axi_awvalid         (sb_axi_awvalid),
    .sb_axi_awready         (sb_axi_awready),
    .sb_axi_awid            (sb_axi_awid),
    .sb_axi_awaddr          (sb_axi_awaddr),
    .sb_axi_awregion        (sb_axi_awregion),
    .sb_axi_awlen           (sb_axi_awlen),
    .sb_axi_awsize          (sb_axi_awsize),
    .sb_axi_awburst         (sb_axi_awburst),
    .sb_axi_awlock          (sb_axi_awlock),
    .sb_axi_awcache         (sb_axi_awcache),
    .sb_axi_awprot          (sb_axi_awprot),
    .sb_axi_awqos           (sb_axi_awqos),

    .sb_axi_wvalid          (sb_axi_wvalid),
    .sb_axi_wready          (sb_axi_wready),
    .sb_axi_wdata           (sb_axi_wdata),
    .sb_axi_wstrb           (sb_axi_wstrb),
    .sb_axi_wlast           (sb_axi_wlast),

    .sb_axi_bvalid          (sb_axi_bvalid),
    .sb_axi_bready          (sb_axi_bready),
    .sb_axi_bresp           (sb_axi_bresp),
    .sb_axi_bid             (sb_axi_bid),


    .sb_axi_arvalid         (sb_axi_arvalid),
    .sb_axi_arready         (sb_axi_arready),
    .sb_axi_arid            (sb_axi_arid),
    .sb_axi_araddr          (sb_axi_araddr),
    .sb_axi_arregion        (sb_axi_arregion),
    .sb_axi_arlen           (sb_axi_arlen),
    .sb_axi_arsize          (sb_axi_arsize),
    .sb_axi_arburst         (sb_axi_arburst),
    .sb_axi_arlock          (sb_axi_arlock),
    .sb_axi_arcache         (sb_axi_arcache),
    .sb_axi_arprot          (sb_axi_arprot),
    .sb_axi_arqos           (sb_axi_arqos),

    .sb_axi_rvalid          (sb_axi_rvalid),
    .sb_axi_rready          (sb_axi_rready),
    .sb_axi_rid             (sb_axi_rid),
    .sb_axi_rdata           (sb_axi_rdata),
    .sb_axi_rresp           (sb_axi_rresp),
    .sb_axi_rlast           (sb_axi_rlast),

    //-------------------------- DMA AXI signals--------------------------
    // AXI Write Channels
    .dma_axi_awvalid        (dma_axi_awvalid),
    .dma_axi_awready        (dma_axi_awready),
    .dma_axi_awid           ('0),
    .dma_axi_awaddr         (lsu_axi_awaddr),
    .dma_axi_awsize         (lsu_axi_awsize),
    .dma_axi_awprot         (lsu_axi_awprot),
    .dma_axi_awlen          (lsu_axi_awlen),
    .dma_axi_awburst        (lsu_axi_awburst),


    .dma_axi_wvalid         (dma_axi_wvalid),
    .dma_axi_wready         (dma_axi_wready),
    .dma_axi_wdata          (lsu_axi_wdata),
    .dma_axi_wstrb          (lsu_axi_wstrb),
    .dma_axi_wlast          (lsu_axi_wlast),

    .dma_axi_bvalid         (dma_axi_bvalid),
    .dma_axi_bready         (dma_axi_bready),
    .dma_axi_bresp          (dma_axi_bresp),
    .dma_axi_bid            (),


    .dma_axi_arvalid        (dma_axi_arvalid),
    .dma_axi_arready        (dma_axi_arready),
    .dma_axi_arid           ('0),
    .dma_axi_araddr         (lsu_axi_araddr),
    .dma_axi_arsize         (lsu_axi_arsize),
    .dma_axi_arprot         (lsu_axi_arprot),
    .dma_axi_arlen          (lsu_axi_arlen),
    .dma_axi_arburst        (lsu_axi_arburst),

    .dma_axi_rvalid         (dma_axi_rvalid),
    .dma_axi_rready         (dma_axi_rready),
    .dma_axi_rid            (),
    .dma_axi_rdata          (dma_axi_rdata),
    .dma_axi_rresp          (dma_axi_rresp),
    .dma_axi_rlast          (dma_axi_rlast),
`endif
    .timer_int              (timer_int ),
    .extintsrc_req          (extintsrc_req ),

    .lsu_bus_clk_en         (1'b1  ),// Clock ratio b/w cpu core clk & AHB master interface
    .ifu_bus_clk_en         (1'b1  ),// Clock ratio b/w cpu core clk & AHB master interface
    .dbg_bus_clk_en         (1'b1  ),// Clock ratio b/w cpu core clk & AHB Debug master interface
    .dma_bus_clk_en         (1'b1  ),// Clock ratio b/w cpu core clk & AHB slave interface

    .trace_rv_i_insn_ip     (trace_rv_i_insn_ip),
    .trace_rv_i_address_ip  (trace_rv_i_address_ip),
    .trace_rv_i_valid_ip    (trace_rv_i_valid_ip),
    .trace_rv_i_exception_ip(trace_rv_i_exception_ip),
    .trace_rv_i_ecause_ip   (trace_rv_i_ecause_ip),
    .trace_rv_i_interrupt_ip(trace_rv_i_interrupt_ip),
    .trace_rv_i_tval_ip     (trace_rv_i_tval_ip),

    .jtag_tck               (jtag_tck),
    .jtag_tms               (jtag_tms),
    .jtag_tdi               (jtag_tdi),
    .jtag_trst_n            (jtag_trst_n),
    .jtag_tdo               (jtag_tdo),
    .jtag_tdoEn             (),

    .mpc_debug_halt_ack     (mpc_debug_halt_ack),
    .mpc_debug_halt_req     (mpc_debug_halt_req),
    .mpc_debug_run_ack      (mpc_debug_run_ack),
    .mpc_debug_run_req      (mpc_debug_run_req),
    .mpc_reset_run_req      (1'b1),             // Start running after reset
    .debug_brkpt_status     (debug_brkpt_status),

    .i_cpu_halt_req         (i_cpu_halt_req ),    // Async halt req to CPU
    .o_cpu_halt_ack         (o_cpu_halt_ack ),    // core response to halt
    .o_cpu_halt_status      (o_cpu_halt_status ), // 1'b1 indicates core is halted
    .i_cpu_run_req          (i_cpu_run_req ),     // Async restart req to CPU
    .o_debug_mode_status    (o_debug_mode_status),
    .o_cpu_run_ack          (o_cpu_run_ack ),     // Core response to run req

    .dec_tlu_perfcnt0       (),
    .dec_tlu_perfcnt1       (),
    .dec_tlu_perfcnt2       (),
    .dec_tlu_perfcnt3       (),

    .mem_clk                (el2_mem_export.clk),

    .iccm_clken             (el2_mem_export.iccm_clken),
    .iccm_wren_bank         (el2_mem_export.iccm_wren_bank),
    .iccm_addr_bank         (el2_mem_export.iccm_addr_bank),
    .iccm_bank_wr_data      (el2_mem_export.iccm_bank_wr_data),
    .iccm_bank_wr_ecc       (el2_mem_export.iccm_bank_wr_ecc),
    .iccm_bank_dout         (el2_mem_export.iccm_bank_dout),
    .iccm_bank_ecc          (el2_mem_export.iccm_bank_ecc),

    .dccm_clken             (el2_mem_export.dccm_clken),
    .dccm_wren_bank         (el2_mem_export.dccm_wren_bank),
    .dccm_addr_bank         (el2_mem_export.dccm_addr_bank),
    .dccm_wr_data_bank      (el2_mem_export.dccm_wr_data_bank),
    .dccm_wr_ecc_bank       (el2_mem_export.dccm_wr_ecc_bank),
    .dccm_bank_dout         (el2_mem_export.dccm_bank_dout),
    .dccm_bank_ecc          (el2_mem_export.dccm_bank_ecc),

    .ic_tag_clken_final         (el2_mem_export.ic_tag_clken_final),
    .ic_tag_wren_q              (el2_mem_export.ic_tag_wren_q),
    .ic_tag_wren_biten_vec      (el2_mem_export.ic_tag_wren_biten_vec),
    .ic_tag_wr_data             (el2_mem_export.ic_tag_wr_data),
    .ic_rw_addr_q               (el2_mem_export.ic_rw_addr_q),
    .ic_tag_data_raw_packed_pre (el2_mem_export.ic_tag_data_raw_packed_pre),
    .ic_tag_data_raw_pre        (el2_mem_export.ic_tag_data_raw_pre),
    .ic_b_sb_wren               (el2_mem_export.ic_b_sb_wren),
    .ic_b_sb_bit_en_vec         (el2_mem_export.ic_b_sb_bit_en_vec),
    .ic_sb_wr_data              (el2_mem_export.ic_sb_wr_data),
    .ic_rw_addr_bank_q          (el2_mem_export.ic_rw_addr_bank_q),
    .wb_packeddout_pre          (el2_mem_export.wb_packeddout_pre),
    .ic_bank_way_clken_final    (el2_mem_export.ic_bank_way_clken_final),
    .ic_bank_way_clken_final_up (el2_mem_export.ic_bank_way_clken_final_up),
    .wb_dout_pre_up             (el2_mem_export.wb_dout_pre_up),

    .iccm_ecc_single_error      (),
    .iccm_ecc_double_error      (),
    .dccm_ecc_single_error      (),
    .dccm_ecc_double_error      (),
    .dccm_write_readback_error  (),

// `ifdef RV_LOCKSTEP_ENABLE
//     .shadow_core_trace_rv_i_insn_ip      (shadow_core_trace_rv_i_insn_ip),
//     .shadow_core_trace_rv_i_address_ip   (shadow_core_trace_rv_i_address_ip),
//     .shadow_core_trace_rv_i_valid_ip     (shadow_core_trace_rv_i_valid_ip),
//     .shadow_core_trace_rv_i_exception_ip (shadow_core_trace_rv_i_exception_ip),
//     .shadow_core_trace_rv_i_ecause_ip    (shadow_core_trace_rv_i_ecause_ip),
//     .shadow_core_trace_rv_i_interrupt_ip (shadow_core_trace_rv_i_interrupt_ip),
//     .shadow_core_trace_rv_i_tval_ip      (shadow_core_trace_rv_i_tval_ip),

//     .disable_corruption_detection_i (disable_corruption_detection_i),
//     .lockstep_err_injection_en_i    (lockstep_err_injection_en_i),
//     .corruption_detected_o          (corruption_detected_o),
// `endif

    .soft_int               (soft_int),
    .core_id                ('0),
    .scan_mode              (1'b0),        // To enable scan mode
    .mbist_mode             (1'b0),        // to enable mbist

    .dmi_core_enable        (dmi_core_enable),
    .dmi_uncore_enable      (),
    .dmi_uncore_en          (),
    .dmi_uncore_wr_en       (),
    .dmi_uncore_addr        (),
    .dmi_uncore_wdata       (),
    .dmi_uncore_rdata       (),
    .dmi_active             ()
);

// ------------------------------------------------------------------
// JTAG
// ------------------------------------------------------------------
`ifdef RV_OPENOCD_TEST
jtagdpi #(
    .Name           ("jtag0"),
    .ListenPort     (5000)
) jtagdpi (
    .clk_i          (core_clk),
    .rst_ni         (rst_l),
    .jtag_tck       (jtag_tck),
    .jtag_tms       (jtag_tms),
    .jtag_tdi       (jtag_tdi),
    .jtag_tdo       (jtag_tdo),
    .jtag_trst_n    (jtag_trst_n),
    .jtag_srst_n    ()
);
`else
  assign jtag_tck    = 1'b0;
  assign jtag_tms    = 1'b0;
  assign jtag_tdi    = 1'b0;
  assign jtag_trst_n = 1'b1;
`endif

// ------------------------------------------------------------------
// Mailbox
// ------------------------------------------------------------------
localparam [31:0] mem_mailbox = 32'hD0580000;

logic         mailbox_write;
logic [63:0]  mailbox_data;

`ifdef RV_BUILD_AHB_LITE
  always_ff @(posedge core_clk)
    mailbox_write <= lmem.HSEL && lmem.HREADY && lmem.HADDR == mem_mailbox && rst_l_combined;
  assign mailbox_data  = lmem.HWDATA;
`endif

`ifdef RV_BUILD_AXI4
  assign mailbox_write = lmem.awvalid && lmem.awaddr == mem_mailbox && rst_l_combined;
  assign mailbox_data  = lmem.wdata;
`endif

// Console
integer console_fd;
logic   console_lf;

initial begin
  console_fd = $fopen("console.log", "w");
  console_lf = '1;
end

always @(negedge core_clk) begin
  if (mailbox_write && mailbox_data[7:0] > 8'h05 && mailbox_data[7:0] < 8'h7F) begin
    if (console_lf) begin
      $fwrite(console_fd,"[%0t ns] %c", $time, mailbox_data[7:0]);
      $write("[%0t ns] %c", $time, mailbox_data[7:0]);
    end else begin
      $fwrite(console_fd,"%c", mailbox_data[7:0]);
      $write("%c", mailbox_data[7:0]);
    end
    console_lf <= (mailbox_data[7:0] == 8'h0A);
  end
end

// End of test monitor
always @(negedge core_clk) begin
  if (mailbox_write && (mailbox_data[7:0] == 8'hFF)) begin
    $display("[%0t ns] TEST_PASSED",$time);
    //$display("[%0t ns] \nFinished : minstret = %0d, mcycle = %0d",$time, `DEC.tlu.minstretl[31:0],`DEC.tlu.mcyclel[31:0]);
    //$display("[%0t ns] See \"exec.log\" for execution trace with register updates..\n",$time);
    // OpenOCD test breaks if simulation closes the TCP connection first.
    // This delay allows OpenOCD to close the connection before the #finish.
    #15000;
    $finish;
  end
  else if(mailbox_write && mailbox_data[7:0] == 8'h01) begin
    $display("[%0t ns] TEST_FAILED",$time);
    `ifdef TB_SILENT_FAIL
        $finish;
    `else
        $fatal;
    `endif // TB_SILENT_FAIL
  end
end

// System control commands
// TODO
assign rst_l_cmd     = '1;
assign extrinsic_req = '0;
assign nmi_int       = '0;
assign timer_int     = '0;
assign soft_int      = '0;

// ------------------------------------------------------------------
// Memory preload
// ------------------------------------------------------------------

`include "ccm_macros.svh"

initial begin
    string hex_file = "program.hex";
    $value$plusargs("hex=%s", hex_file);

    $dumpfile("dump.vcd");
    $dumpvars(0, tb_top);

    $display("Loading program from '%s'", hex_file);
    $readmemh(hex_file, lmem.mem);
    $readmemh(hex_file, imem.mem);
    preload_dccm();
    preload_iccm();
end

// ============================================================================

endmodule
