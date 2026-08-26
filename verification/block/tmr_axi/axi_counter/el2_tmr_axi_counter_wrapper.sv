module el2_tmr_axi_counter_wrapper
  import el2_mubi_pkg::*;
# (
  localparam unsigned AddrWidth = 32,
  localparam unsigned DataWidth = 64,
  localparam unsigned IdWidth   = 8
)
(
  input  logic      clk_i,
  input  logic      rst_ni,

  // Subordinate AXI port
  input  logic                     s_axi_awvalid_i,
  output logic                     s_axi_awready_o,
  input  logic [IdWidth-1:0]       s_axi_awid_i,
  input  logic [AddrWidth-1:0]     s_axi_awaddr_i,
  input  logic [3:0]               s_axi_awregion_i,
  input  logic [7:0]               s_axi_awlen_i,
  input  logic [2:0]               s_axi_awsize_i,
  input  logic [1:0]               s_axi_awburst_i,
  input  logic                     s_axi_awlock_i,
  input  logic [3:0]               s_axi_awcache_i,
  input  logic [2:0]               s_axi_awprot_i,
  input  logic [3:0]               s_axi_awqos_i,

  input  logic                     s_axi_wvalid_i,
  output logic                     s_axi_wready_o,
  input  logic [DataWidth-1:0]     s_axi_wdata_i,
  input  logic [DataWidth/8-1:0]   s_axi_wstrb_i,
  input  logic                     s_axi_wlast_i,

  output logic                     s_axi_bvalid_o,
  input  logic                     s_axi_bready_i,
  output logic [1:0]               s_axi_bresp_o,
  output logic [IdWidth-1:0]       s_axi_bid_o,

  input  logic                     s_axi_arvalid_i,
  output logic                     s_axi_arready_o,
  input  logic [IdWidth-1:0]       s_axi_arid_i,
  input  logic [AddrWidth-1:0]     s_axi_araddr_i,
  input  logic [3:0]               s_axi_arregion_i,
  input  logic [7:0]               s_axi_arlen_i,
  input  logic [2:0]               s_axi_arsize_i,
  input  logic [1:0]               s_axi_arburst_i,
  input  logic                     s_axi_arlock_i,
  input  logic [3:0]               s_axi_arcache_i,
  input  logic [2:0]               s_axi_arprot_i,
  input  logic [3:0]               s_axi_arqos_i,

  output logic                     s_axi_rvalid_o,
  input  logic                     s_axi_rready_i,
  output logic [IdWidth-1:0]       s_axi_rid_o,
  output logic [DataWidth-1:0]     s_axi_rdata_o,
  output logic [1:0]               s_axi_rresp_o,
  output logic                     s_axi_rlast_o,

  // Manager AXI port
  output logic                     m_axi_awvalid_o,
  input  logic                     m_axi_awready_i,
  output logic [IdWidth-1:0]       m_axi_awid_o,
  output logic [AddrWidth-1:0]     m_axi_awaddr_o,
  output logic [3:0]               m_axi_awregion_o,
  output logic [7:0]               m_axi_awlen_o,
  output logic [2:0]               m_axi_awsize_o,
  output logic [1:0]               m_axi_awburst_o,
  output logic                     m_axi_awlock_o,
  output logic [3:0]               m_axi_awcache_o,
  output logic [2:0]               m_axi_awprot_o,
  output logic [3:0]               m_axi_awqos_o,

  output logic                     m_axi_wvalid_o,
  input  logic                     m_axi_wready_i,
  output logic [DataWidth-1:0]     m_axi_wdata_o,
  output logic [DataWidth/8-1:0]   m_axi_wstrb_o,
  output logic                     m_axi_wlast_o,

  input  logic                     m_axi_bvalid_i,
  output logic                     m_axi_bready_o,
  input  logic [1:0]               m_axi_bresp_i,
  input  logic [IdWidth-1:0]       m_axi_bid_i,

  output logic                     m_axi_arvalid_o,
  input  logic                     m_axi_arready_i,
  output logic [IdWidth-1:0]       m_axi_arid_o,
  output logic [AddrWidth-1:0]     m_axi_araddr_o,
  output logic [3:0]               m_axi_arregion_o,
  output logic [7:0]               m_axi_arlen_o,
  output logic [2:0]               m_axi_arsize_o,
  output logic [1:0]               m_axi_arburst_o,
  output logic                     m_axi_arlock_o,
  output logic [3:0]               m_axi_arcache_o,
  output logic [2:0]               m_axi_arprot_o,
  output logic [3:0]               m_axi_arqos_o,

  input  logic                     m_axi_rvalid_i,
  output logic                     m_axi_rready_o,
  input  logic [IdWidth-1:0]       m_axi_rid_i,
  input  logic [DataWidth-1:0]     m_axi_rdata_i,
  input  logic [1:0]               m_axi_rresp_i,
  input  logic                     m_axi_rlast_i,

  // Control and status
  input  el2_mubi_t clear_i,      // Reset for transaction counters
  output el2_mubi_t pending_o,    // Asserted when a transaction is pending

  output el2_mubi_t ecc_error_o,  // ECC correctable error occurred
  output el2_mubi_t ecc_fatal_o   // ECC uncorrectable error occurred
);

  // Connect AXI busses
  assign m_axi_awvalid_o  = s_axi_awvalid_i; 
  assign s_axi_awready_o  = m_axi_awready_i; 
  assign m_axi_awid_o     = s_axi_awid_i; 
  assign m_axi_awaddr_o   = s_axi_awaddr_i; 
  assign m_axi_awregion_o = s_axi_awregion_i; 
  assign m_axi_awlen_o    = s_axi_awlen_i; 
  assign m_axi_awsize_o   = s_axi_awsize_i; 
  assign m_axi_awburst_o  = s_axi_awburst_i; 
  assign m_axi_awlock_o   = s_axi_awlock_i; 
  assign m_axi_awcache_o  = s_axi_awcache_i; 
  assign m_axi_awprot_o   = s_axi_awprot_i; 
  assign m_axi_awqos_o    = s_axi_awqos_i; 

  assign m_axi_wvalid_o   = s_axi_wvalid_i; 
  assign s_axi_wready_o   = m_axi_wready_i; 
  assign m_axi_wdata_o    = s_axi_wdata_i; 
  assign m_axi_wstrb_o    = s_axi_wstrb_i; 
  assign m_axi_wlast_o    = s_axi_wlast_i; 

  assign s_axi_bvalid_o   = m_axi_bvalid_i; 
  assign m_axi_bready_o   = s_axi_bready_i; 
  assign s_axi_bresp_o    = m_axi_bresp_i; 
  assign s_axi_bid_o      = m_axi_bid_i; 

  assign m_axi_arvalid_o  = s_axi_arvalid_i; 
  assign s_axi_arready_o  = m_axi_arready_i; 
  assign m_axi_arid_o     = s_axi_arid_i; 
  assign m_axi_araddr_o   = s_axi_araddr_i; 
  assign m_axi_arregion_o = s_axi_arregion_i; 
  assign m_axi_arlen_o    = s_axi_arlen_i; 
  assign m_axi_arsize_o   = s_axi_arsize_i; 
  assign m_axi_arburst_o  = s_axi_arburst_i; 
  assign m_axi_arlock_o   = s_axi_arlock_i; 
  assign m_axi_arcache_o  = s_axi_arcache_i; 
  assign m_axi_arprot_o   = s_axi_arprot_i; 
  assign m_axi_arqos_o    = s_axi_arqos_i; 

  assign s_axi_rvalid_o   = m_axi_rvalid_i; 
  assign m_axi_rready_o   = s_axi_rready_i; 
  assign s_axi_rid_o      = m_axi_rid_i; 
  assign s_axi_rdata_o    = m_axi_rdata_i; 
  assign s_axi_rresp_o    = m_axi_rresp_i; 
  assign s_axi_rlast_o    = m_axi_rlast_i; 

  // Instantiate the transaction counter
  el2_tmr_axi_counter u_axi_counter (
    .axi_awvalid_i (m_axi_awvalid_o),
    .axi_awready_i (m_axi_awready_i),

    .axi_wvalid_i  (m_axi_wvalid_o),
    .axi_wready_i  (m_axi_wready_i),
    .axi_wlast_i   (m_axi_wlast_o),

    .axi_bvalid_i  (m_axi_bvalid_i),
    .axi_bready_i  (m_axi_bready_o),

    .axi_arvalid_i (m_axi_arvalid_o),
    .axi_arready_i (m_axi_arready_i),

    .axi_rvalid_i  (m_axi_rvalid_i),
    .axi_rready_i  (m_axi_rready_o),
    .axi_rlast_i   (m_axi_rlast_i),

    .*
  );

endmodule
