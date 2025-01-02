module el2_ifu_ic_tag_wrapper
  import el2_pkg::*;
#(
    `include "el2_param.vh"
) (
    input logic clk,
    input logic active_clk,
    input logic rst_l,
    input logic clk_override,
    input logic dec_tlu_core_ecc_disable,

    input logic [31:3] ic_rw_addr,

    input logic [pt.ICACHE_NUM_WAYS-1:0] ic_wr_en,      // way
    input logic [pt.ICACHE_NUM_WAYS-1:0] ic_tag_valid,
    input logic                          ic_rd_en,

    input logic [  pt.ICACHE_INDEX_HI:3] ic_debug_addr,       // Read/Write addresss to the Icache.
    input logic                          ic_debug_rd_en,      // Icache debug rd
    input logic                          ic_debug_wr_en,      // Icache debug wr
    input logic                          ic_debug_tag_array,  // Debug tag array
    input logic [pt.ICACHE_NUM_WAYS-1:0] ic_debug_way,        // Debug way. Rd or Wr.

    // unpack el2_mem_if.veer_icache_tag
    output logic [pt.ICACHE_NUM_WAYS-1:0] ic_tag_clken_final,
    output logic [pt.ICACHE_NUM_WAYS-1:0] ic_tag_wren_q,
    output logic [(26*pt.ICACHE_NUM_WAYS)-1 : 0] ic_tag_wren_biten_vec,
    output logic [25:0] ic_tag_wr_data,
    output logic [pt.ICACHE_INDEX_HI:pt.ICACHE_TAG_INDEX_LO] ic_rw_addr_q,
    input logic [(26*pt.ICACHE_NUM_WAYS)-1 : 0] ic_tag_data_raw_packed_pre,
    input logic [pt.ICACHE_NUM_WAYS-1:0][25:0] ic_tag_data_raw_pre,
    // end unpack

    output logic [25:0] ictag_debug_rd_data,
    input  logic [70:0] ic_debug_wr_data,     // Debug wr cache.

    output logic [pt.ICACHE_NUM_WAYS-1:0] ic_rd_hit,
    output logic                          ic_tag_perr,
    // Excluding scan_mode from coverage as its usage is determined by the integrator of the VeeR core.
    /*pragma coverage off*/
    input  logic                          scan_mode
    /*pragma coverage on*/
);

  el2_mem_if local_icache_export ();

  assign ic_tag_clken_final = local_icache_export.ic_tag_clken_final;
  assign ic_tag_wren_q = local_icache_export.ic_tag_wren_q;
  assign ic_tag_wren_biten_vec = local_icache_export.ic_tag_wren_biten_vec;
  assign ic_tag_wr_data = local_icache_export.ic_tag_wr_data;
  assign ic_rw_addr_q = local_icache_export.ic_rw_addr_q;
  assign local_icache_export.ic_tag_data_raw_packed_pre = ic_tag_data_raw_packed_pre;
  assign local_icache_export.ic_tag_data_raw_pre = ic_tag_data_raw_pre;

  EL2_IC_TAG #(
      .pt(pt)
  ) el2_ic_tag_inst (
      .*,
      .icache_export(local_icache_export.veer_icache_tag)
  );

endmodule
