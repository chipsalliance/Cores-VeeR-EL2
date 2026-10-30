// Copyright 2026 Antmicro <www.antmicro.com>
// SPDX-License-Identifier: Apache-2.0

`ifdef RV_TRIPLE_MODULAR_REDUNDANCY_ENABLE
package el2_tmr_pkg;
    typedef enum logic [8:0] {
    IDLE                          = 9'b110000110,
    HALT_CORES                    = 9'b001100011,
    READ_REG                      = 9'b011001111,
    SET_FLAG_RD                   = 9'b100111111,
    RESET_CPU                     = 9'b010101100,
    SET_FLAG_CC                   = 9'b101010001,
    WRITE_REG                     = 9'b001010110,
    SET_FLAG_SR                   = 9'b010010011,
    RESTART_CPU                   = 9'b100100000,
    SET_FLAG_CR                   = 9'b011110101,
    CLEAR_FLAG_ERR                = 9'b000001010,
    CLEAR_FLAG_RD                 = 9'b001111000,
    CLEAR_FLAG_CC                 = 9'b111110010,
    CLEAR_FLAG_SR                 = 9'b101001100,
    CLEAR_FLAG_CR                 = 9'b000000101
    } recovery_state_t;
endpackage
`endif
