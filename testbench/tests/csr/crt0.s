# SPDX-License-Identifier: Apache-2.0

.section .text.init
.global _start
_start:

        # Setup stack
        la sp, STACK

        # Hello
        lui a0,%hi(str_hello)
        addi a0,a0,%lo(str_hello)
        call printf

        # Print MISA
        lui a0,%hi(str_misa)
        addi a0,a0,%lo(str_misa)
        csrr a1, misa
        call printf

        # Check if the value is correct
        csrr t0, misa
        li t1, 0x40101104
        li a0, 1
        bne t0, t1, _finish

        # Success
        li a0, 0xff

.global _finish
_finish:
        la t0, tohost
        sb a0, 0(t0) # Signal testbench termination
        beq x0, x0, _finish
        .rept 10
        nop
        .endr

.section .text
str_hello:
        .string "Hello VeeR\n"
str_misa:
        .string "MISA = 0x%08X\n"

.section .data.io
.global tohost
tohost: .word 0

