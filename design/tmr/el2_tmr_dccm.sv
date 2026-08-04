// Copyright 2026 Antmicro <www.antmicro.com>
// //
// // SPDX-License-Identifier: Apache-2.0
//
`ifdef RV_TRIPLE_MODULAR_REDUNDANCY_ENABLE
module el2_tmr_dccm
  import el2_pkg::*;
  import el2_mubi_pkg::*;
#(
    `include "el2_param.vh"
) (
    input  logic free_l2clk,
    input  logic rst_l,

    // DCCM
    output logic                            dccm_wren,
    output logic                            dccm_rden,
    output logic [pt.DCCM_BITS-1:0]         dccm_wr_addr_lo,
    output logic [pt.DCCM_BITS-1:0]         dccm_wr_addr_hi,
    output logic [pt.DCCM_BITS-1:0]         dccm_rd_addr_lo,
    output logic [pt.DCCM_BITS-1:0]         dccm_rd_addr_hi,
    output logic [pt.DCCM_FDATA_WIDTH-1:0]  dccm_wr_data_lo,
    output logic [pt.DCCM_FDATA_WIDTH-1:0]  dccm_wr_data_hi,

    input logic [pt.DCCM_FDATA_WIDTH-1:0]   dccm_rd_data_lo,
    input logic [pt.DCCM_FDATA_WIDTH-1:0]   dccm_rd_data_hi,

    // DCCM ECC status
    output logic                 dccm_ecc_single_error,
    output logic                 dccm_ecc_double_error,

    // DCCM TMR
    input  logic                           dccm_wren_veer[3],
    input  logic                           dccm_rden_veer[3],
    input  logic [pt.DCCM_BITS-1:0]        dccm_wr_addr_lo_veer[3],
    input  logic [pt.DCCM_BITS-1:0]        dccm_wr_addr_hi_veer[3],
    input  logic [pt.DCCM_BITS-1:0]        dccm_rd_addr_lo_veer[3],
    input  logic [pt.DCCM_BITS-1:0]        dccm_rd_addr_hi_veer[3],
    input  logic [pt.DCCM_FDATA_WIDTH-1:0] dccm_wr_data_lo_veer[3],
    input  logic [pt.DCCM_FDATA_WIDTH-1:0] dccm_wr_data_hi_veer[3],

    output logic [pt.DCCM_FDATA_WIDTH-1:0] dccm_rd_data_lo_veer[3],
    output logic [pt.DCCM_FDATA_WIDTH-1:0] dccm_rd_data_hi_veer[3],

    // DCCM ECC status
    output logic dccm_ecc_single_error_veer[3],
    output logic dccm_ecc_double_error_veer[3],

    // Fault inputs
    input  el2_mubi_pkg::el2_mubi_t dccm_fault_d[3],
    // Fault outputs
    output el2_mubi_pkg::el2_mubi_t dccm_fault_q[3],
    // Fault clear inputs
    input  el2_mubi_pkg::el2_mubi_t dccm_fault_clr[3]
);

  // ......................................................

  el2_mubi_t enable[3];

  el2_mubi_t fault_dccm_wr_addr_lo[3];
  el2_mubi_t fault_dccm_wr_addr_hi[3];
  el2_mubi_t fault_dccm_rd_addr_lo[3];
  el2_mubi_t fault_dccm_rd_addr_hi[3];
  el2_mubi_t fault_dccm_wr_data_lo[3];
  el2_mubi_t fault_dccm_wr_data_hi[3];
  el2_mubi_t fault_dccm_ctl_bundle[3];

  el2_mubi_t crit_dccm_wr_addr_lo;
  el2_mubi_t crit_dccm_wr_addr_hi;
  el2_mubi_t crit_dccm_rd_addr_lo;
  el2_mubi_t crit_dccm_rd_addr_hi;
  el2_mubi_t crit_dccm_wr_data_lo;
  el2_mubi_t crit_dccm_wr_data_hi;
  el2_mubi_t crit_dccm_ctl_bundle;

  el2_mubi_t crit_any;

  // ......................................................

  el2_tmr_voter #(.Width(pt.DCCM_BITS)) x_voter_wr_addr_lo (
    .in_a     (dccm_wr_addr_lo_veer[0]),
    .in_b     (dccm_wr_addr_lo_veer[1]),
    .in_c     (dccm_wr_addr_lo_veer[2]),

    .en_a     (enable[0]),
    .en_b     (enable[1]),
    .en_c     (enable[2]),

    .out      (dccm_wr_addr_lo),

    .fault_a  (fault_dccm_wr_addr_lo[0]),
    .fault_b  (fault_dccm_wr_addr_lo[1]),
    .fault_c  (fault_dccm_wr_addr_lo[2]),

    .critical (crit_dccm_wr_addr_lo)
  );

  el2_tmr_voter #(.Width(pt.DCCM_BITS)) x_voter_wr_addr_hi (
    .in_a     (dccm_wr_addr_hi_veer[0]),
    .in_b     (dccm_wr_addr_hi_veer[1]),
    .in_c     (dccm_wr_addr_hi_veer[2]),

    .en_a     (enable[0]),
    .en_b     (enable[1]),
    .en_c     (enable[2]),

    .out      (dccm_wr_addr_hi),

    .fault_a  (fault_dccm_wr_addr_hi[0]),
    .fault_b  (fault_dccm_wr_addr_hi[1]),
    .fault_c  (fault_dccm_wr_addr_hi[2]),

    .critical (crit_dccm_wr_addr_hi)
  );

  el2_tmr_voter #(.Width(pt.DCCM_BITS)) x_voter_rd_addr_lo (
    .in_a     (dccm_rd_addr_lo_veer[0]),
    .in_b     (dccm_rd_addr_lo_veer[1]),
    .in_c     (dccm_rd_addr_lo_veer[2]),

    .en_a     (enable[0]),
    .en_b     (enable[1]),
    .en_c     (enable[2]),

    .out      (dccm_rd_addr_lo),

    .fault_a  (fault_dccm_rd_addr_lo[0]),
    .fault_b  (fault_dccm_rd_addr_lo[1]),
    .fault_c  (fault_dccm_rd_addr_lo[2]),

    .critical (crit_dccm_rd_addr_lo)
  );

  el2_tmr_voter #(.Width(pt.DCCM_BITS)) x_voter_rd_addr_hi (
    .in_a     (dccm_rd_addr_hi_veer[0]),
    .in_b     (dccm_rd_addr_hi_veer[1]),
    .in_c     (dccm_rd_addr_hi_veer[2]),

    .en_a     (enable[0]),
    .en_b     (enable[1]),
    .en_c     (enable[2]),

    .out      (dccm_rd_addr_hi),

    .fault_a  (fault_dccm_rd_addr_hi[0]),
    .fault_b  (fault_dccm_rd_addr_hi[1]),
    .fault_c  (fault_dccm_rd_addr_hi[2]),

    .critical (crit_dccm_rd_addr_hi)
  );

  el2_tmr_voter #(.Width(pt.DCCM_FDATA_WIDTH)) x_voter_wr_data_lo (
    .in_a     (dccm_wr_data_lo_veer[0]),
    .in_b     (dccm_wr_data_lo_veer[1]),
    .in_c     (dccm_wr_data_lo_veer[2]),

    .en_a     (enable[0]),
    .en_b     (enable[1]),
    .en_c     (enable[2]),

    .out      (dccm_wr_data_lo),

    .fault_a  (fault_dccm_wr_data_lo[0]),
    .fault_b  (fault_dccm_wr_data_lo[1]),
    .fault_c  (fault_dccm_wr_data_lo[2]),

    .critical (crit_dccm_wr_data_lo)
  );

  el2_tmr_voter #(.Width(pt.DCCM_FDATA_WIDTH)) x_voter_wr_data_hi (
    .in_a     (dccm_wr_data_hi_veer[0]),
    .in_b     (dccm_wr_data_hi_veer[1]),
    .in_c     (dccm_wr_data_hi_veer[2]),

    .en_a     (enable[0]),
    .en_b     (enable[1]),
    .en_c     (enable[2]),

    .out      (dccm_wr_data_hi),

    .fault_a  (fault_dccm_wr_data_hi[0]),
    .fault_b  (fault_dccm_wr_data_hi[1]),
    .fault_c  (fault_dccm_wr_data_hi[2]),

    .critical (crit_dccm_wr_data_hi)
  );

  // ......................................................

  // Bundle single-bit control signals togeather
  typedef struct packed {
    logic wren;
    logic rden;
  } dccm_ctl_bundle_t;

  dccm_ctl_bundle_t dccm_ctl_bundle;
  dccm_ctl_bundle_t dccm_ctl_bundle_veer[3];

  generate for (genvar i=0; i<3; i=i+1) begin : ctl_bundle
    always_comb begin
      dccm_ctl_bundle_veer[i].wren = dccm_wren_veer[i];
      dccm_ctl_bundle_veer[i].rden = dccm_rden_veer[i];
    end
  end endgenerate

  always_comb begin
    dccm_wren = dccm_ctl_bundle.wren & mubi_check_false(crit_any);
    dccm_rden = dccm_ctl_bundle.rden & mubi_check_false(crit_any);
  end

  el2_tmr_voter #(.Width($bits(dccm_ctl_bundle_t))) x_voter_ctl_bundle (
    .in_a     (dccm_ctl_bundle_veer[0]),
    .in_b     (dccm_ctl_bundle_veer[1]),
    .in_c     (dccm_ctl_bundle_veer[2]),

    .en_a     (enable[0]),
    .en_b     (enable[1]),
    .en_c     (enable[2]),

    .out      (dccm_ctl_bundle),

    .fault_a  (fault_dccm_ctl_bundle[0]),
    .fault_b  (fault_dccm_ctl_bundle[1]),
    .fault_c  (fault_dccm_ctl_bundle[2]),

    .critical (crit_dccm_ctl_bundle)
  );

  // ......................................................

  // Fault aggregation and registers
  generate for (genvar i=0; i<3; i=i+1) begin : fault
    el2_mubi_t  fault_l00;
    el2_mubi_t  fault_l01;
    el2_mubi_t  fault_l02;
    el2_mubi_t  fault_l0;
    el2_mubi_t  fault_l1;
    el2_mubi_t  fault_any;

    assign fault_l00 = mubi_or(fault_dccm_wr_addr_lo[i], fault_dccm_wr_addr_hi[i]);
    assign fault_l01 = mubi_or(fault_dccm_rd_addr_lo[i], fault_dccm_rd_addr_hi[i]);
    assign fault_l02 = mubi_or(fault_dccm_wr_data_lo[i], fault_dccm_wr_data_hi[i]);

    assign fault_l0  = mubi_or3(fault_l00,  fault_l01, fault_l02);
    assign fault_l1  = mubi_or(dccm_fault_d[i], fault_dccm_ctl_bundle[i]);

    assign fault_any = mubi_or(fault_l0, fault_l1);

    always_ff @(posedge free_l2clk or negedge rst_l) begin
      if (!rst_l) begin
        dccm_fault_q[i] <= El2MuBiFalse;
      end else begin
        if (mubi_check_true(dccm_fault_clr[i])) begin
          dccm_fault_q[i] <= El2MuBiFalse;
        end else begin
          dccm_fault_q[i] <= mubi_or(dccm_fault_q[i], fault_any);
        end
      end
    end

    assign enable[i] = mubi_not(dccm_fault_q[i]);

  end endgenerate

  // ......................................................

  // Critical fault aggregation
  el2_mubi_t  crit_l00;
  el2_mubi_t  crit_l01;
  el2_mubi_t  crit_l02;
  el2_mubi_t  crit_l03;
  el2_mubi_t  crit_l0;

  assign crit_l00 = mubi_or(crit_dccm_wr_addr_lo, crit_dccm_wr_addr_hi);
  assign crit_l01 = mubi_or(crit_dccm_rd_addr_lo, crit_dccm_rd_addr_hi);
  assign crit_l02 = mubi_or(crit_dccm_wr_data_lo, crit_dccm_wr_data_hi);

  assign crit_l0  = mubi_or3(crit_l00,  crit_l01, crit_l02);

  assign crit_any = mubi_or(crit_l0, crit_dccm_ctl_bundle);

  // ......................................................

  // Propagate response to cores
  generate for (genvar i=0; i<3; i=i+1) begin
    always_comb begin
      dccm_rd_data_lo_veer[i] = dccm_rd_data_lo;
      dccm_rd_data_hi_veer[i] = dccm_rd_data_hi;
    end
  end endgenerate

endmodule
`endif
