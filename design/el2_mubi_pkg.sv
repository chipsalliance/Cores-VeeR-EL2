// Implementation derived from https://github.com/lowRISC/opentitan/blob/891c6079b2f19650f2bb6d248c28ea4cfbd746d2/hw/ip/prim/rtl/prim_mubi_pkg.sv#L31

package el2_mubi_pkg;

  // Multibit feature without DCLS feature enabled
  // doesn't apply any encoding to the logic
`ifdef RV_LOCKSTEP_ENABLE
  parameter int El2MuBiWidth = `RV_MUBI_WIDTH;
`else
  parameter int El2MuBiWidth = 1;
`endif

  typedef logic [El2MuBiWidth-1:0] el2_mubi_t;

`ifdef RV_LOCKSTEP_ENABLE
  parameter el2_mubi_t El2MuBiTrue = `RV_MUBI_TRUE;
  parameter el2_mubi_t El2MuBiFalse = `RV_MUBI_FALSE;
`else
  parameter el2_mubi_t El2MuBiTrue = 1'b1;
  parameter el2_mubi_t El2MuBiFalse = 1'b0;
`endif

  function automatic el2_mubi_t mubi_check_invalid(el2_mubi_t val);
    return (val inside {El2MuBiTrue, El2MuBiFalse}) ? El2MuBiFalse : El2MuBiTrue;
  endfunction : mubi_check_invalid

  function automatic logic mubi_check_true(el2_mubi_t val);
    return val == El2MuBiTrue;
  endfunction : mubi_check_true

  function automatic logic mubi_check_false(el2_mubi_t val);
    return val == El2MuBiFalse;
  endfunction : mubi_check_false

  function automatic el2_mubi_t mubi_from_bool(logic val);
    return val == 0 ? El2MuBiFalse : El2MuBiTrue;
  endfunction : mubi_from_bool

  // Performs a logical OR operation between two multibit values.
  function automatic el2_mubi_t mubi_or(el2_mubi_t a, el2_mubi_t b);
    logic [El2MuBiWidth-1:0] a_in, b_in, out;
    a_in = a;
    b_in = b;
    for (int k = 0; k < El2MuBiWidth; k++) begin
      out[k] = El2MuBiTrue[k] ? a_in[k] || b_in[k] : a_in[k] && b_in[k];
    end
    return el2_mubi_t'(out);
  endfunction : mubi_or

  // Performs a logical AND operation between two multibit values.
  function automatic el2_mubi_t mubi_and(el2_mubi_t a, el2_mubi_t b);
    logic [El2MuBiWidth-1:0] a_in, b_in, act_in, out;
    a_in = a;
    b_in = b;
    for (int k = 0; k < El2MuBiWidth; k++) begin
      out[k] = El2MuBiTrue[k] ? a_in[k] && b_in[k] : a_in[k] || b_in[k];
    end
    return el2_mubi_t'(out);
  endfunction : mubi_and

endpackage
