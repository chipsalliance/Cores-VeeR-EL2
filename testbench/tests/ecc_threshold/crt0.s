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
    bnez a0, 1f
    li t1, 0xff
    sb t1, 0(t0) // DemoTB test termination (PASS)
    li t1, 1
    sw t1, 0(t0) // Whisper test termination
    j 2f
1:
    li t1, 1
    sb t1, 0(t0) // DemoTB test termination (FAIL)
    sw t1, 0(t0) // Whisper test termination
2:
    beq x0, x0, _finish
    .rept 10
    nop
    .endr

.global _trap_handler
_trap_handler:
    addi sp, sp, -128
    sw ra, 0(sp)
    sw t0, 4(sp)
    sw t1, 8(sp)
    sw t2, 12(sp)
    sw t3, 16(sp)
    sw t4, 20(sp)
    sw t5, 24(sp)
    sw t6, 28(sp)
    sw a0, 32(sp)
    sw a1, 36(sp)
    sw a2, 40(sp)
    sw a3, 44(sp)
    sw a4, 48(sp)
    sw a5, 52(sp)
    sw a6, 56(sp)
    sw a7, 60(sp)
    call trap_handler
    lw ra, 0(sp)
    lw t0, 4(sp)
    lw t1, 8(sp)
    lw t2, 12(sp)
    lw t3, 16(sp)
    lw t4, 20(sp)
    lw t5, 24(sp)
    lw t6, 28(sp)
    lw a0, 32(sp)
    lw a1, 36(sp)
    lw a2, 40(sp)
    lw a3, 44(sp)
    lw a4, 48(sp)
    lw a5, 52(sp)
    lw a6, 56(sp)
    lw a7, 60(sp)
    addi sp, sp, 128
    mret

.section .data.io
.global tohost
tohost: .word 0
