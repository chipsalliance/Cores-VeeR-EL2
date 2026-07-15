//
// Copyright (c) 2026 Antmicro
// SPDX-License-Identifier: Apache-2.0

module el2_tmr_voter # (
  parameter unsigned Width = 1  // Signal width
) (
  input  logic clk_i,
  input  logic rst_ni,

  // Inputs to the voter
  input  logic [Width-1:0] in_a,
  input  logic [Width-1:0] in_b,
  input  logic [Width-1:0] in_c,

  // Input enable
  input  el2_mubi_pkg::el2_mubi_t en_a,
  input  el2_mubi_pkg::el2_mubi_t en_b,
  input  el2_mubi_pkg::el2_mubi_t en_c,

  // Majority voter output
  output logic [Width-1:0] out,

  // Fault indicators
  output el2_mubi_pkg::el2_mubi_t fault_a,
  output el2_mubi_pkg::el2_mubi_t fault_b,
  output el2_mubi_pkg::el2_mubi_t fault_c
);
  import el2_mubi_pkg::*;

  // Comparators
  el2_mubi_t cmp_ab;
  el2_mubi_t cmp_bc;
  el2_mubi_t cmp_ca;

  always_comb begin
    cmp_ab = mubi_from_bool(in_a === in_b);
    cmp_bc = mubi_from_bool(in_b === in_c);
    cmp_ca = mubi_from_bool(in_c === in_a);
  end

  // Mux selectors
  el2_mubi_t sel_a;
  el2_mubi_t sel_b;
  el2_mubi_t sel_c;

  // Voting and fault detection
  always_comb begin

    // Majority voting
    if (mubi_check_true(mubi_and3(en_a, en_b, en_c))) begin

      // A is faulty
      if (mubi_check_true(mubi_and3(mubi_not(cmp_ab), cmp_bc, mubi_not(cmp_ca)))) begin
        fault_a = El2MuBiTrue;
        fault_b = El2MuBiFalse;
        fault_c = El2MuBiFalse;

        sel_a   = El2MuBiFalse;
        sel_b   = El2MuBiTrue;
        sel_c   = El2MuBiFalse;

      // B is faulty
      end else if (mubi_check_true(mubi_and3(mubi_not(cmp_ab), mubi_not(cmp_bc), cmp_ca))) begin
        fault_a = El2MuBiFalse;
        fault_b = El2MuBiTrue;
        fault_c = El2MuBiFalse;

        sel_a   = El2MuBiFalse;
        sel_b   = El2MuBiFalse;
        sel_c   = El2MuBiTrue;

      // C is faulty
      end else if (mubi_check_true(mubi_and3(cmp_ab, mubi_not(cmp_bc), mubi_not(cmp_ca)))) begin
        fault_a = El2MuBiFalse;
        fault_b = El2MuBiFalse;
        fault_c = El2MuBiTrue;

        sel_a   = El2MuBiTrue;
        sel_b   = El2MuBiFalse;
        sel_c   = El2MuBiFalse;

      // Complete disagreement
      end else if (mubi_check_true(mubi_and3(mubi_not(cmp_ab), mubi_not(cmp_bc), mubi_not(cmp_ca)))) begin
        fault_a = El2MuBiTrue;
        fault_b = El2MuBiTrue;
        fault_c = El2MuBiTrue;

        sel_a   = El2MuBiFalse;
        sel_b   = El2MuBiFalse;
        sel_c   = El2MuBiFalse;

      // Complete agreement
      end else begin
        fault_a = El2MuBiFalse;
        fault_b = El2MuBiFalse;
        fault_c = El2MuBiFalse;

        sel_a   = El2MuBiTrue;
        sel_b   = El2MuBiFalse;
        sel_c   = El2MuBiFalse;

      end

    // A is disabled
    end else if (mubi_check_true(mubi_and3(mubi_not(en_a), en_b, en_c))) begin

      // B and C mismatch
      if (mubi_check_false(cmp_bc)) begin
        fault_a = El2MuBiFalse;
        fault_b = El2MuBiTrue;
        fault_c = El2MuBiTrue;

        sel_a   = El2MuBiFalse;
        sel_b   = El2MuBiFalse;
        sel_c   = El2MuBiFalse;

      // Agreement
      end else begin
        fault_a = El2MuBiFalse;
        fault_b = El2MuBiFalse;
        fault_c = El2MuBiFalse;

        sel_a   = El2MuBiFalse;
        sel_b   = El2MuBiTrue;
        sel_c   = El2MuBiFalse;
      end

    // B is disabled
    end else if (mubi_check_true(mubi_and3(en_a, mubi_not(en_b), en_c))) begin

      // C and A mismatch
      if (mubi_check_false(cmp_ca)) begin
        fault_a = El2MuBiTrue;
        fault_b = El2MuBiFalse;
        fault_c = El2MuBiTrue;

        sel_a   = El2MuBiFalse;
        sel_b   = El2MuBiFalse;
        sel_c   = El2MuBiFalse;

      // Agreement
      end else begin
        fault_a = El2MuBiFalse;
        fault_b = El2MuBiFalse;
        fault_c = El2MuBiFalse;

        sel_a   = El2MuBiFalse;
        sel_b   = El2MuBiFalse;
        sel_c   = El2MuBiTrue;
      end

    // C is disabled
    end else if (mubi_check_true(mubi_and3(en_a, en_b, mubi_not(en_c)))) begin

      // A and B mismatch
      if (mubi_check_false(cmp_ab)) begin
        fault_a = El2MuBiTrue;
        fault_b = El2MuBiTrue;
        fault_c = El2MuBiFalse;

        sel_a   = El2MuBiFalse;
        sel_b   = El2MuBiFalse;
        sel_c   = El2MuBiFalse;

      // Agreement
      end else begin
        fault_a = El2MuBiFalse;
        fault_b = El2MuBiFalse;
        fault_c = El2MuBiFalse;

        sel_a   = El2MuBiTrue;
        sel_b   = El2MuBiFalse;
        sel_c   = El2MuBiFalse;
      end

    // Two or more inputs are disabled
    end else begin
      fault_a = en_a;
      fault_b = en_b;
      fault_c = en_c;

      sel_a   = El2MuBiFalse;
      sel_b   = El2MuBiFalse;
      sel_c   = El2MuBiFalse;

    end

  end

  // Output multiplexer
  always_comb begin
    out = '0;

    if (mubi_check_true(sel_a)) begin
      out |= in_a;
    end
    if (mubi_check_true(sel_b)) begin
      out |= in_b;
    end
    if (mubi_check_true(sel_c)) begin
      out |= in_c;
    end
  end

endmodule
