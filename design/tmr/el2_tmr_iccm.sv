// Copyright 2026 Antmicro <www.antmicro.com>
// //
// // SPDX-License-Identifier: Apache-2.0
//
//
`ifdef RV_TRIPLE_MODULAR_REDUNDANCY_ENABLE
module el2_tmr_iccm
  import el2_pkg::*;
  import el2_mubi_pkg::*;
#(
    `include "el2_param.vh"
) (
    input  logic free_l2clk,
    input  logic rst_l,

    // ICCM
    output logic [pt.ICCM_BITS-1:1]     iccm_rw_addr,
    output logic                        iccm_wren,
    output logic                        iccm_rden,
    output logic [2:0]                  iccm_wr_size,
    output logic [77:0]                 iccm_wr_data,
    output logic                        iccm_buf_correct_ecc,
    output logic                        iccm_correction_state,

    input  logic [77:0]                 iccm_rd_data_ecc,

    // ICCM ECC status
    output logic                 iccm_ecc_single_error,
    output logic                 iccm_ecc_double_error,

    // ICCM TMR
    input  logic [pt.ICCM_BITS-1:1] iccm_rw_addr_veer[3],
    input  logic                    iccm_wren_veer[3],
    input  logic                    iccm_rden_veer[3],
    input  logic [2:0]              iccm_wr_size_veer[3],
    input  logic [77:0]             iccm_wr_data_veer[3],
    input  logic                    iccm_buf_correct_ecc_veer[3],
    input  logic                    iccm_correction_state_veer[3],

    output logic [77:0]             iccm_rd_data_ecc_veer[3],

    // ICCM ECC status
    input  logic                 iccm_ecc_single_error_veer[3],
    input  logic                 iccm_ecc_double_error_veer[3],

    // Fault inputs
    input  el2_mubi_pkg::el2_mubi_t iccm_fault_d[3],
    // Fault outputs
    output el2_mubi_pkg::el2_mubi_t iccm_fault_q[3],
    // Fault clear inputs
    input  el2_mubi_pkg::el2_mubi_t iccm_fault_clr[3]
);

  // ......................................................

  el2_mubi_t enable[3];

  el2_mubi_t fault_iccm_rw_addr[3];
  el2_mubi_t fault_iccm_wr_data[3];
  el2_mubi_t fault_iccm_wr_size[3];
  el2_mubi_t fault_iccm_ctl_bundle[3];

  el2_mubi_t crit_iccm_rw_addr;
  el2_mubi_t crit_iccm_wr_data;
  el2_mubi_t crit_iccm_wr_size;
  el2_mubi_t crit_iccm_ctl_bundle;

  el2_mubi_t crit_any;

  // ......................................................

  el2_tmr_voter #(.Width(pt.ICCM_BITS-1)) x_voter_rw_addr (
    .in_a     (iccm_rw_addr_veer[0]),
    .in_b     (iccm_rw_addr_veer[1]),
    .in_c     (iccm_rw_addr_veer[2]),

    .en_a     (enable[0]),
    .en_b     (enable[1]),
    .en_c     (enable[2]),

    .out      (iccm_rw_addr),

    .fault_a  (fault_iccm_rw_addr[0]),
    .fault_b  (fault_iccm_rw_addr[1]),
    .fault_c  (fault_iccm_rw_addr[2]),

    .critical (crit_iccm_rw_addr)
  );

  el2_tmr_voter #(.Width($bits(iccm_wr_data))) x_voter_wr_data (
    .in_a     (iccm_wr_data_veer[0]),
    .in_b     (iccm_wr_data_veer[1]),
    .in_c     (iccm_wr_data_veer[2]),

    .en_a     (enable[0]),
    .en_b     (enable[1]),
    .en_c     (enable[2]),

    .out      (iccm_wr_data),

    .fault_a  (fault_iccm_wr_data[0]),
    .fault_b  (fault_iccm_wr_data[1]),
    .fault_c  (fault_iccm_wr_data[2]),

    .critical (crit_iccm_wr_data)
  );

  el2_tmr_voter #(.Width($bits(iccm_wr_size))) x_voter_wr_size (
    .in_a     (iccm_wr_size_veer[0]),
    .in_b     (iccm_wr_size_veer[1]),
    .in_c     (iccm_wr_size_veer[2]),

    .en_a     (enable[0]),
    .en_b     (enable[1]),
    .en_c     (enable[2]),

    .out      (iccm_wr_size),

    .fault_a  (fault_iccm_wr_size[0]),
    .fault_b  (fault_iccm_wr_size[1]),
    .fault_c  (fault_iccm_wr_size[2]),

    .critical (crit_iccm_wr_size)
  );

  // ......................................................

  // Bundle single-bit control signals togeather
  typedef struct packed {
    logic wren;
    logic rden;
    logic buf_correct_ecc;
    logic correction_state;
    logic ecc_single_error;
    logic ecc_double_error;
  } iccm_ctl_bundle_t;

  iccm_ctl_bundle_t iccm_ctl_bundle;
  iccm_ctl_bundle_t iccm_ctl_bundle_veer[3];

  generate for (genvar i=0; i<3; i=i+1) begin : ctl_bundle
    always_comb begin
      iccm_ctl_bundle_veer[i].wren             = iccm_wren_veer[i];
      iccm_ctl_bundle_veer[i].rden             = iccm_rden_veer[i];
      iccm_ctl_bundle_veer[i].buf_correct_ecc  = iccm_buf_correct_ecc_veer[i];
      iccm_ctl_bundle_veer[i].correction_state = iccm_correction_state_veer[i];
      iccm_ctl_bundle_veer[i].ecc_single_error = iccm_ecc_single_error_veer[i];
      iccm_ctl_bundle_veer[i].ecc_double_error = iccm_ecc_double_error_veer[i];
    end
  end endgenerate

  always_comb begin
    iccm_wren             = iccm_ctl_bundle.wren & mubi_check_false(crit_any);
    iccm_rden             = iccm_ctl_bundle.rden & mubi_check_false(crit_any);
    iccm_buf_correct_ecc  = iccm_ctl_bundle.buf_correct_ecc;
    iccm_correction_state = iccm_ctl_bundle.correction_state;
    iccm_ecc_single_error = iccm_ctl_bundle.ecc_single_error;
    iccm_ecc_double_error = iccm_ctl_bundle.ecc_double_error;
  end

  el2_tmr_voter #(.Width($bits(iccm_ctl_bundle_t))) x_voter_ctl_bundle (
    .in_a     (iccm_ctl_bundle_veer[0]),
    .in_b     (iccm_ctl_bundle_veer[1]),
    .in_c     (iccm_ctl_bundle_veer[2]),

    .en_a     (enable[0]),
    .en_b     (enable[1]),
    .en_c     (enable[2]),

    .out      (iccm_ctl_bundle),

    .fault_a  (fault_iccm_ctl_bundle[0]),
    .fault_b  (fault_iccm_ctl_bundle[1]),
    .fault_c  (fault_iccm_ctl_bundle[2]),

    .critical (crit_iccm_ctl_bundle)
  );

  // ......................................................

  // Fault aggregation and registers
  generate for (genvar i=0; i<3; i=i+1) begin : fault
    el2_mubi_t  fault_l0;
    el2_mubi_t  fault_l1;
    el2_mubi_t  fault_any;

    assign fault_l0  = mubi_or(fault_iccm_rw_addr[i], fault_iccm_wr_data[i]);
    assign fault_l1  = mubi_or(fault_iccm_wr_size[i], fault_iccm_ctl_bundle[i]);
    assign fault_any = mubi_or3(iccm_fault_d[i], fault_l0, fault_l1);

    always_ff @(posedge free_l2clk or negedge rst_l) begin
      if (!rst_l) begin
        iccm_fault_q[i] <= El2MuBiFalse;
      end else begin
        if (mubi_check_true(iccm_fault_clr[i])) begin
          iccm_fault_q[i] <= El2MuBiFalse;
        end else begin
          iccm_fault_q[i] <= mubi_or(iccm_fault_q[i], fault_any);
        end
      end
    end

    assign enable[i] = mubi_not(iccm_fault_q[i]);

  end endgenerate

  // Critical fault aggregation
  el2_mubi_t crit_l0;
  el2_mubi_t crit_l1;

  assign crit_l0  = mubi_or(crit_iccm_rw_addr, crit_iccm_wr_data);
  assign crit_l1  = mubi_or(crit_iccm_wr_size, crit_iccm_ctl_bundle);
  assign crit_any = mubi_or(crit_l0, crit_l1);

  // ......................................................

  // Propagate response to cores
  generate for (genvar i=0; i<3; i=i+1) begin : resp
    assign iccm_rd_data_ecc_veer[i] = iccm_rd_data_ecc;
  end endgenerate

endmodule
`endif
