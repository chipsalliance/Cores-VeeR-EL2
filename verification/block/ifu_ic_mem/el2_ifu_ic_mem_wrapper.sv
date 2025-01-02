module el2_ifu_ic_mem_wrapper
  import el2_pkg::*;
#(
    `include "el2_param.vh"
) (
    input logic                                   clk,                // Clock only while core active.  Through one clock header.  For flops with    second clock header built in.  Connected to ACTIVE_L2CLK.
    input logic                                   active_clk,         // Clock only while core active.  Through two clock headers. For flops without second clock header built in.
    input logic rst_l,  // reset, active low
    input logic clk_override,  // Override non-functional clock gating
    input logic dec_tlu_core_ecc_disable,  // Disable ECC checking

    input logic [31:1] ic_rw_addr,
    input logic [pt.ICACHE_NUM_WAYS-1:0] ic_wr_en,  // Which way to write
    input logic ic_rd_en,  // Read enable
    input logic [pt.ICACHE_INDEX_HI:3] ic_debug_addr,  // Read/Write addresss to the Icache.
    input logic ic_debug_rd_en,  // Icache debug rd
    input logic ic_debug_wr_en,  // Icache debug wr
    input logic ic_debug_tag_array,  // Debug tag array
    input logic [pt.ICACHE_NUM_WAYS-1:0] ic_debug_way,  // Debug way. Rd or Wr.
    input logic [63:0] ic_premux_data,  // Premux data to be muxed with each way of the Icache.
    input logic ic_sel_premux_data,  // Select the pre_muxed data

    input logic [pt.ICACHE_BANKS_WAY-1:0][70:0] ic_wr_data,  // Data to fill to the Icache. With ECC
    output logic [63:0]                           ic_rd_data ,        // Data read from Icache. 2x64bits + parity bits. F2 stage. With ECC
    output logic [70:0]                           ic_debug_rd_data ,  // Data read from Icache. 2x64bits + parity bits. F2 stage. With ECC
    output logic [25:0] ictag_debug_rd_data,  // Debug icache tag.
    input logic [70:0] ic_debug_wr_data,  // Debug wr cache.

    output logic [pt.ICACHE_BANKS_WAY-1:0] ic_eccerr,  // ecc error per bank
    output logic [pt.ICACHE_BANKS_WAY-1:0] ic_parerr,  // ecc error per bank
    input logic [pt.ICACHE_NUM_WAYS-1:0]          ic_tag_valid,       // Valid from the I$ tag valid outside (in flops).

    // unpack
    output ic_clk,

    // data
    output logic [pt.ICACHE_BANKS_WAY-1:0][     pt.ICACHE_NUM_WAYS-1:0] ic_b_sb_wren,
    output logic [pt.ICACHE_BANKS_WAY-1:0][(71*pt.ICACHE_NUM_WAYS)-1:0] ic_b_sb_bit_en_vec,

    output logic [pt.ICACHE_BANKS_WAY-1:0][70:0] ic_sb_wr_data,
    output logic [pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_INDEX_HI : pt.ICACHE_DATA_INDEX_LO] ic_rw_addr_bank_q,
    output logic [pt.ICACHE_BANKS_WAY-1:0] ic_bank_way_clken_final,
    output logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0] ic_bank_way_clken_final_up,
    input logic [pt.ICACHE_BANKS_WAY-1:0][(71*pt.ICACHE_NUM_WAYS)-1:0] wb_packeddout_pre,
    input logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0][71-1:0] wb_dout_pre_up,

    // tag
    output logic [pt.ICACHE_BANKS_WAY-1:0] ic_tag_clken_final,
    output logic [pt.ICACHE_NUM_WAYS-1:0] ic_tag_wren_q,
    output logic [(26*pt.ICACHE_NUM_WAYS)-1 : 0] ic_tag_wren_biten_vec,
    output logic [25:0] ic_tag_wr_data,
    output logic [pt.ICACHE_INDEX_HI:pt.ICACHE_TAG_INDEX_LO] ic_rw_addr_q,
    input logic [(26*pt.ICACHE_NUM_WAYS)-1 : 0] ic_tag_data_raw_packed_pre,
    input logic [pt.ICACHE_NUM_WAYS-1:0][25:0] ic_tag_data_raw_pre,
    // end unpack

    output logic [pt.ICACHE_NUM_WAYS-1:0] ic_rd_hit,    // ic_rd_hit[3:0]
    output logic                          ic_tag_perr,  // Tag Parity error
    // Excluding scan_mode from coverage as its usage is determined by the integrator of the VeeR core.
    /*pragma coverage off*/
    input  logic                          scan_mode     // Flop scan mode control
    /*pragma coverage on*/
);

  el2_mem_if local_icache_export ();

  // unpack
  assign ic_clk = local_icache_export.clk;
  // data
  assign ic_b_sb_wren = local_icache_export.ic_b_sb_wren;
  assign ic_b_sb_bit_en_vec = local_icache_export.ic_b_sb_bit_en_vec;
  assign ic_sb_wr_data = local_icache_export.ic_sb_wr_data;
  assign ic_rw_addr_bank_q = local_icache_export.ic_rw_addr_bank_q;
  assign ic_bank_way_clken_final = local_icache_export.ic_bank_way_clken_final;
  assign ic_bank_way_clken_final_up = local_icache_export.ic_bank_way_clken_final_up;
  assign local_icache_export.wb_packeddout_pre = wb_packeddout_pre;
  assign local_icache_export.wb_dout_pre_up = wb_dout_pre_up;
  // tag
  assign ic_tag_clken_final = local_icache_export.ic_tag_clken_final;
  assign ic_tag_wren_q = local_icache_export.ic_tag_wren_q;
  assign ic_tag_wren_biten_vec = local_icache_export.ic_tag_wren_biten_vec;
  assign ic_tag_wr_data = local_icache_export.ic_tag_wr_data;
  assign ic_rw_addr_q = local_icache_export.ic_rw_addr_q;
  assign local_icache_export.ic_tag_data_raw_packed_pre = ic_tag_data_raw_packed_pre;
  assign local_icache_export.ic_tag_data_raw_pre = ic_tag_data_raw_pre;

  el2_ifu_ic_mem #(
      .pt(pt)
  ) el2_ifu_ic_mem_inst (
      .*,
      .icache_export(local_icache_export.veer_icache_src)
  );

endmodule
