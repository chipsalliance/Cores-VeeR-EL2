// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Antmicro, Ltd. <www.antmicro.com>

/*
  This module monitors an AXI bus and reports whether there are any pending
  in-flight transactions.
*/
module el2_tmr_axi_counter
  import el2_mubi_pkg::*;
(
  input  logic     clk_i,
  input  logic     rst_ni,

  // AXI signals to monitor
  input  logic     axi_awvalid_i,
  input  logic     axi_awready_i,

  input  logic     axi_wvalid_i,
  input  logic     axi_wready_i,
  input  logic     axi_wlast_i,

  input  logic     axi_bvalid_i,
  input  logic     axi_bready_i,

  input  logic     axi_arvalid_i,
  input  logic     axi_arready_i,

  input  logic     axi_rvalid_i,
  input  logic     axi_rready_i,
  input  logic     axi_rlast_i,

  // Control and status
  input  el2_mubi_t clear_i,      // Reset for transaction counters
  output el2_mubi_t pending_o,    // Asserted when a transaction is pending

  output el2_mubi_t ecc_error_o,  // ECC correctable error occurred
  output el2_mubi_t ecc_fatal_o   // ECC uncorrectable error occurred
);

  // ......................................................

  // Detect first W beat
  logic axi_wfirst_n;
  logic axi_wfirst_n_next;

  always_comb begin
    axi_wfirst_n_next = axi_wfirst_n;
    if (axi_wvalid_i & axi_wready_i) begin
      axi_wfirst_n_next = ~axi_wlast_i;
    end
  end

  rvdff #(.WIDTH(1)) dff_wfirst (
    .clk   (clk_i),
    .rst_l (rst_ni),
    .din   (axi_wfirst_n_next),
    .dout  (axi_wfirst_n)
  );

  // ......................................................

  // Transaction counters
  logic [7:0]  aw_count;
  logic [7:0]  w_count;
  logic [7:0]  ar_count;

  logic aw_ecc_error;
  logic w_ecc_error;
  logic ar_ecc_error;

  logic aw_ecc_fatal;
  logic w_ecc_fatal;
  logic ar_ecc_fatal;

  el2_ecc_counter_8 u_aw_count (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),

    .inc_i   (axi_awvalid_i & axi_awready_i),
    .dec_i   (axi_bvalid_i  & axi_bready_i),
    .clr_i   (mubi_check_true(clear_i)),

    .cnt_o   (aw_count),

    .ecc_error_o (aw_ecc_error),
    .ecc_fatal_o (aw_ecc_fatal)
  );

  el2_ecc_counter_8 u_w_count (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),

    .inc_i   (axi_wvalid_i  & axi_wready_i & ~axi_wfirst_n),
    .dec_i   (axi_bvalid_i  & axi_bready_i),
    .clr_i   (mubi_check_true(clear_i)),

    .cnt_o   (w_count),

    .ecc_error_o (w_ecc_error),
    .ecc_fatal_o (w_ecc_fatal)
  );

  el2_ecc_counter_8 u_ar_count (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),

    .inc_i   (axi_arvalid_i & axi_arready_i),
    .dec_i   (axi_rvalid_i  & axi_rready_i & axi_rlast_i),
    .clr_i   (mubi_check_true(clear_i)),

    .cnt_o   (ar_count),

    .ecc_error_o (ar_ecc_error),
    .ecc_fatal_o (ar_ecc_fatal)
  );

  // ......................................................

  // Pending signal
  assign pending_o   = mubi_or3(mubi_from_bool(aw_count != '0),
                                mubi_from_bool(w_count  != '0),
                                mubi_from_bool(ar_count != '0));

  // Error signals
  assign ecc_error_o = mubi_or3(mubi_from_bool(aw_ecc_error),
                                mubi_from_bool(w_ecc_error),
                                mubi_from_bool(ar_ecc_error));

  assign ecc_fatal_o = mubi_or3(mubi_from_bool(aw_ecc_fatal),
                                mubi_from_bool(w_ecc_fatal),
                                mubi_from_bool(ar_ecc_fatal));

endmodule
