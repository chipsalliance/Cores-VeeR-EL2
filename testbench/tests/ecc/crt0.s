# SPDX-License-Identifier: Apache-2.0

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

.global _finish
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

.global _trap_handler
_trap_handler:
    call trap_handler
    j _start

.section .data.io
.global tohost
tohost: .word 0

