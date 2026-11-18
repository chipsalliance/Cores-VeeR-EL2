#include "common.s"

// mtval must hold the encoding of the instruction that trapped, not of a
// younger instruction that was stalled behind it in decode.
.balign 4
mtval_handler:
    csrr x6, mtval
    bne x6, x7, fail
    la x2, ok
    csrw mepc, x2
    mret

two_illegal:
    li x7, 0xffffffff
    .word 0xffffffff
    .word 0x00000000
    j fail

illegal_then_mret:
    li x7, 0xffffffff
    .word 0xffffffff
    mret
    j fail

main:
    la x2, mtval_handler
    csrw mtvec, x2
    call two_illegal
    call illegal_then_mret
    j _finish
