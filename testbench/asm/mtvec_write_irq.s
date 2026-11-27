#include "common.s"

// An interrupt taken in the cycle a csrw mtvec commits must use the mtvec
// value that instruction wrote, not the old one. The soft interrupt is swept
// over a chain of writes that switch mtvec between a Direct-mode handler and
// a Vectored table, and each handler checks that it was entered through the
// vector that matches the mtvec it reads back.

.macro trial nops
    la x10, 1f
    csrw mtvec, x8
    li x2, 0x8
    csrw mie, x2
    li x2, TRIGGER_SOFT_INT
    li x3, STDOUT
    sw x2, 0(x3)
    .rept \nops
    nop
    .endr
    .rept 12
    csrw mtvec, x9
    csrw mtvec, x8
    .endr
    j fail
1:
.endm

.balign 256
direct_handler:
    csrr x6, mtvec
    bne x6, x8, fail
    j soft_int_done

.option push
.option norvc
.balign 256
vector_table:
    j fail
    j fail
    j fail
    j vectored_soft_int
.option pop

vectored_soft_int:
    csrr x6, mtvec
    bne x6, x9, fail
soft_int_done:
    csrw mie, zero
    li x2, 0x90 // clear the soft interrupt line
    li x3, STDOUT
    sw x2, 0(x3)
1:
    csrr x6, mip
    andi x6, x6, 0x8
    bnez x6, 1b
    csrw mepc, x10
    mret

main:
    la x8, direct_handler
    la x9, vector_table
    ori x9, x9, 1
    .irp n, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15
    trial \n
    .endr
    j _finish
