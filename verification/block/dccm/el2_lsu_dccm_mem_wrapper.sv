module el2_lsu_dccm_mem_wrapper
  import el2_pkg::*;
#(
    `include "el2_param.vh"
)
(
    input logic clk,
    input logic active_clk,
    input logic rst_l,
    input logic clk_override,

    input logic dccm_wren,
    input logic dccm_rden,
    input logic [pt.DCCM_BITS-1:0] dccm_wr_addr_lo,
    input logic [pt.DCCM_BITS-1:0] dccm_wr_addr_hi,
    input logic [pt.DCCM_BITS-1:0] dccm_rd_addr_lo,
    input logic [pt.DCCM_BITS-1:0] dccm_rd_addr_hi,
    input logic [pt.DCCM_FDATA_WIDTH-1:0] dccm_wr_data_lo,
    input logic [pt.DCCM_FDATA_WIDTH-1:0] dccm_wr_data_hi,

    // el2_dccm_ext_in_pkt_t
    input logic dccm_ext_in_pkt_TEST1,
    input logic dccm_ext_in_pkt_RME,
    input logic [3:0] dccm_ext_in_pkt_RM,
    input logic dccm_ext_in_pkt_LS,
    input logic dccm_ext_in_pkt_DS,
    input logic dccm_ext_in_pkt_SD,
    input logic dccm_ext_in_pkt_TEST_RNM,
    input logic dccm_ext_in_pkt_BC1,
    input logic dccm_ext_in_pkt_BC2,

    output logic [pt.DCCM_FDATA_WIDTH-1:0] dccm_rd_data_lo,
    output logic [pt.DCCM_FDATA_WIDTH-1:0] dccm_rd_data_hi,

    input logic scan_mode
);

  // Pack dccm_ext_in_pkt
  el2_dccm_ext_in_pkt_t [pt.DCCM_NUM_BANKS-1:0] dccm_ext_in_pkt;

  for (genvar i = 0; i < pt.DCCM_NUM_BANKS; i++) begin
      assign dccm_ext_in_pkt[i].TEST1    = dccm_ext_in_pkt_TEST1;
      assign dccm_ext_in_pkt[i].RME      = dccm_ext_in_pkt_RME;
      assign dccm_ext_in_pkt[i].RM       = dccm_ext_in_pkt_RM;
      assign dccm_ext_in_pkt[i].LS       = dccm_ext_in_pkt_LS;
      assign dccm_ext_in_pkt[i].DS       = dccm_ext_in_pkt_DS;
      assign dccm_ext_in_pkt[i].SD       = dccm_ext_in_pkt_SD;
      assign dccm_ext_in_pkt[i].TEST_RNM = dccm_ext_in_pkt_TEST_RNM;
      assign dccm_ext_in_pkt[i].BC1      = dccm_ext_in_pkt_BC1;
      assign dccm_ext_in_pkt[i].BC2      = dccm_ext_in_pkt_BC2;
  end

  el2_lsu_dccm_mem mem (.*);

endmodule
