// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Antmicro, Ltd. <www.antmicro.com>

/*
  The module implements an 8-bit counter protected with ECC SECDED code.
  The counter can count up, down and be cleared synchronously.
*/
module el2_ecc_counter_8 (
  input  logic       clk_i,      // Clock
  input  logic       rst_ni,     // Async. reset

  input  logic       inc_i,      // Increment
  input  logic       dec_i,      // Decrement
  input  logic       clr_i,      // Clear

  output logic [7:0] cnt_o,      // Count value

  output logic       ecc_error_o,  // ECC correctable error occurred
  output logic       ecc_fatal_o   // ECC uncorrectable error occurred
);

  logic [12:0] storage;
  logic [12:0] storage_next;

  logic [ 7:0] count;
  logic [ 7:0] count_next;

  // Counting logic
  always_comb begin
    count_next = count;

    if (clr_i) begin
      count_next = '0;
    end else begin
      if ( inc_i & ~dec_i) begin
        count_next = count + 1'b1;
      end
      if (~inc_i &  dec_i) begin
        count_next = count - 1'b1;
      end
    end
  end

  // ECC encoder
  el2_secded_13_8_enc u_ecc_enc (
    .data_i (count_next),
    .data_o (storage_next)
  );

  // Storage
  rvdff #(.WIDTH($bits(storage))) dff_storage (
    .clk   (clk_i),
    .rst_l (rst_ni),
    .din   (storage_next),
    .dout  (storage)
  );

  // ECC decoder
  logic [4:0] ecc_syndrome_nc;
  logic [1:0] ecc_error;

  el2_secded_13_8_dec u_ecc_dec (
    .data_i     (storage),
    .data_o     (count),
    .syndrome_o (ecc_syndrome_nc),
    .err_o      (ecc_error)
  );

  // Count and correctable error are output directly
  assign cnt_o       = count;
  assign ecc_error_o = ecc_error[0];

  // Uncorrectable error is latched
  logic ecc_fatal;
  logic ecc_fatal_next;

  always_comb begin
    ecc_fatal_next = ecc_fatal;
    if (clr_i) begin
      ecc_fatal_next = '0;
    end else if (ecc_error[1]) begin
      ecc_fatal_next = '1;
    end
  end

  rvdff #(.WIDTH(1)) dff_ecc_fatal (
    .clk   (clk_i),
    .rst_l (rst_ni),
    .din   (ecc_fatal_next),
    .dout  (ecc_fatal)
  );

  assign ecc_fatal_o = ecc_fatal | ecc_error[1];

endmodule
