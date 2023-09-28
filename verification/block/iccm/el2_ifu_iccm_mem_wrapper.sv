// Copyright (c) 2023 Antmicro
// SPDX-License-Identifier: Apache-2.0

module el2_ifu_iccm_mem_wrapper
    import el2_pkg::*;
#(
    `include "el2_param.vh"
)(
    input logic clk,
    input logic active_clk,
    input logic rst_l,
    input logic clk_override,

    input logic iccm_wren,
    input logic iccm_rden,
    input logic [pt.ICCM_BITS-1:1] iccm_rw_addr,
    input logic iccm_buf_correct_ecc,
    input logic iccm_correction_state,
    input logic [2:0] iccm_wr_size,
    input logic [77:0] iccm_wr_data,

    // Unwrapped iccm_ext_in_pkt
    input logic iccm_ext_in_pkt_TEST1,
    input logic iccm_ext_in_pkt_RME,
    input logic [3:0] iccm_ext_in_pkt_RM,
    input logic iccm_ext_in_pkt_LS,
    input logic iccm_ext_in_pkt_DS,
    input logic iccm_ext_in_pkt_SD,
    input logic iccm_ext_in_pkt_TEST_RNM,
    input logic iccm_ext_in_pkt_BC1,
    input logic iccm_ext_in_pkt_BC2,

    output logic [63:0] iccm_rd_data,
    output logic [77:0] iccm_rd_data_ecc,
    input logic scan_mode
);

    // Pack iccm_ext_in_pkt
    el2_ccm_ext_in_pkt_t [pt.ICCM_NUM_BANKS-1:0] iccm_ext_in_pkt;

    for (genvar i=0; i<pt.ICCM_NUM_BANKS; i++) begin
        assign iccm_ext_in_pkt[i].TEST1 = iccm_ext_in_pkt_TEST1;
        assign iccm_ext_in_pkt[i].RME = iccm_ext_in_pkt_RME;
        assign iccm_ext_in_pkt[i].RM = iccm_ext_in_pkt_RM;
        assign iccm_ext_in_pkt[i].LS = iccm_ext_in_pkt_LS;
        assign iccm_ext_in_pkt[i].DS = iccm_ext_in_pkt_DS;
        assign iccm_ext_in_pkt[i].SD = iccm_ext_in_pkt_SD;
        assign iccm_ext_in_pkt[i].TEST_RNM = iccm_ext_in_pkt_TEST_RNM;
        assign iccm_ext_in_pkt[i].BC1 = iccm_ext_in_pkt_BC1;
        assign iccm_ext_in_pkt[i].BC2 = iccm_ext_in_pkt_BC2;
    end

    // The ICCM module
    el2_ifu_iccm_mem mem (.*);

endmodule
