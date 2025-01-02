module el2_ifu_ic_data_wrapper
  import el2_pkg::*;
#(
    `include "el2_param.vh"
) (
    input logic clk,
    input logic active_clk,
    input logic rst_l,
    input logic clk_override,

    input logic [                  31:1] ic_rw_addr,
    input logic [pt.ICACHE_NUM_WAYS-1:0] ic_wr_en,
    input logic                          ic_rd_en,    // Read enable

    input logic [pt.ICACHE_BANKS_WAY-1:0][70:0] ic_wr_data,  // Data to fill to the Icache. With ECC
    output logic [63:0]                             ic_rd_data ,                                 // Data read from Icache. 2x64bits + parity bits. F2 stage. With ECC
    input logic [70:0] ic_debug_wr_data,  // Debug wr cache.
    output logic [70:0]                             ic_debug_rd_data ,  // Data read from Icache. 2x64bits + parity bits. F2 stage. With ECC
    output logic [pt.ICACHE_BANKS_WAY-1:0] ic_parerr,
    output logic [pt.ICACHE_BANKS_WAY-1:0] ic_eccerr,  // ecc error per bank
    input logic [pt.ICACHE_INDEX_HI:3] ic_debug_addr,  // Read/Write addresss to the Icache.
    input logic ic_debug_rd_en,  // Icache debug rd
    input logic ic_debug_wr_en,  // Icache debug wr
    input logic ic_debug_tag_array,  // Debug tag array
    input logic [pt.ICACHE_NUM_WAYS-1:0] ic_debug_way,  // Debug way. Rd or Wr.
    input logic [63:0] ic_premux_data,  // Premux data to be muxed with each way of the Icache.
    input logic ic_sel_premux_data,  // Select the pre_muxed data

    input logic [pt.ICACHE_NUM_WAYS-1:0] ic_rd_hit,

    //unpack
    output logic [pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_NUM_WAYS-1:0] ic_b_sb_wren,
    output logic [pt.ICACHE_BANKS_WAY-1:0][(71*pt.ICACHE_NUM_WAYS)-1:0] ic_b_sb_bit_en_vec,
    output logic [pt.ICACHE_BANKS_WAY-1:0][70:0] ic_sb_wr_data,
    output logic [pt.ICACHE_BANKS_WAY-1:0][pt.ICACHE_INDEX_HI : pt.ICACHE_DATA_INDEX_LO] ic_rw_addr_bank_q,
    output logic [pt.ICACHE_BANKS_WAY-1:0] ic_bank_way_clken_final,
    output logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0] ic_bank_way_clken_final_up,
    input logic [pt.ICACHE_BANKS_WAY-1:0][(71*pt.ICACHE_NUM_WAYS)-1:0] wb_packeddout_pre,
    input logic [pt.ICACHE_NUM_WAYS-1:0][pt.ICACHE_BANKS_WAY-1:0][71-1:0] wb_dout_pre_up,
    //end unpack

    // Excluding scan_mode from coverage as its usage is determined by the integrator of the VeeR core.
    /*pragma coverage off*/
    input logic scan_mode
    /*pragma coverage on*/
);

  el2_mem_if local_icache_export ();


  assign ic_b_sb_wren = local_icache_export.ic_b_sb_wren;
  assign ic_b_sb_bit_en_vec = local_icache_export.ic_b_sb_bit_en_vec;
  assign ic_sb_wr_data = local_icache_export.ic_sb_wr_data;
  assign ic_rw_addr_bank_q = local_icache_export.ic_rw_addr_bank_q;
  assign ic_bank_way_clken_final = local_icache_export.ic_bank_way_clken_final;
  assign ic_bank_way_clken_final_up = local_icache_export.ic_bank_way_clken_final_up;
  assign local_icache_export.wb_packeddout_pre = wb_packeddout_pre;
  assign local_icache_export.wb_dout_pre_up = wb_dout_pre_up;

  EL2_IC_DATA #(
      .pt(pt)
  ) el2_ic_data_inst (
      .*,
      .icache_export(local_icache_export.veer_icache_data)
  );

endmodule
