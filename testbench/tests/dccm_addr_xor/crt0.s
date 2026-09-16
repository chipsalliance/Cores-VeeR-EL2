# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 Google LLC
#
# Author: Samip Modi (samipmodi@google.com)

#include "defines.h"

.section .text.init
.global _start
_start:
    // enable caching, except region 0xd
    li t0, 0x59555555
    csrw 0x7c0, t0

    la sp, STACK

    la t0, _trap_handler
    csrw mtvec, t0

    call main

    // Test Termination Point:
    // When main() completes all test phases and returns 0, execution enters _finish.
    // This is a terminal noreturn routine that signals completion to the testbench and
    // halts execution in an infinite branch-to-self loop.
.global _finish
.type _finish, @function
_finish:
    la t0, tohost
    li t1, 0xff
    sb t1, 0(t0) // DemoTB test termination
    li t1, 1
    sw t1, 0(t0) // Whisper test termination
    beq x0, x0, _finish
    .rept 10
    nop
    .endr
.size _finish, .-_finish

    // Multi-Phase Restart Trap Handler:
    // When an expected fault injection triggers an architectural ECC exception (mcause=0x5),
    // execution vectors here. After C trap_handler() verifies the CSR cause registers,
    // increments trap_count, and de-asserts the fault mailbox, it loops back via `j _start`.
    // Re-entering _start resets `sp` to STACK and calls main(), where `boot_phase++`
    // advances the test to the next fault injection phase without requiring an external reset.
.global _trap_handler
.type _trap_handler, @function
_trap_handler:
    // Immediately disable all fault injection via registers before any memory/stack access
    li t0, 0xd0580000
    li t1, 0xec          // DISABLE_DCCM_FAULT
    sb t1, 0(t0)
    li t1, 0xe8          // DISABLE_ICCM_FAULT
    sb t1, 0(t0)
    li t1, 0xe4          // DISABLE_ERROR_INJECTION
    sb t1, 0(t0)
    la sp, STACK         // Reset sp to top of clean stack
    call trap_handler
    j _start
.size _trap_handler, .-_trap_handler

.section .data.io
.global tohost
tohost: .word 0
