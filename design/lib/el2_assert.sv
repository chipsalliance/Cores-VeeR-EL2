// Implementation derived from https://github.com/lowRISC/opentitan/blob/891c6079b2f19650f2bb6d248c28ea4cfbd746d2/hw/ip/prim/rtl/prim_assert.sv#L48

// Static assertions for checks inside SV packages. If the conditions is not true, this will
// trigger an error during elaboration.
`define ASSERT_STATIC_IN_PACKAGE(__name, __prop)              \
  function automatic bit assert_static_in_package_``__name(); \
    bit unused_bit [((__prop) ? 1 : -1)];                     \
    unused_bit = '{default: 1'b0};                            \
    return unused_bit[0];                                     \
  endfunction
