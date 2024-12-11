#include "defines.h"
#include "tb.h"

.section .text
.global _start
_start:
    // Clear minstret
    csrw minstret, zero
    csrw minstreth, zero

    // Enable Caches in MRAC
    li x2, 0x5f555555
    csrw 0x7c0, x2

    // global interrupt enable
    csrr x2, mstatus
    ori x2, x2, 0x8
    csrw mstatus, x2

    // set up mtvec
    la x2, exc_int_handler
    csrw mtvec, x2

    // Set up NMI handler address
    li x3, STDOUT
    ori x2, x2, LOAD_NMI_ADDR
    sw x2, 0(x3)

    j main

// Write 0xff to STDOUT for TB to terminate test.
_finish:
    li x3, STDOUT
    addi x5, x0, 0xff
    sb x5, 0(x3)
    beq x0, x0, _finish
.rept 100
    nop
.endr

// handler must be aligned to 256 bytes since it has to fit
// in the upper 24 bits of nmi handler address set testbench command
.balign 256
exc_int_handler:
    // disable all interrupt sources
    csrw mie, zero
    // reenable signaling of NMIs for subsequent NMIs
    csrw 0xBC0, zero // mdeau
    // compare CSRs with expected values
    csrr x2, mcause
    bne x2, x4, fail
    csrr x2, 0x7FF // mscause
    bne x2, x5, fail
    // set mepc to return from the test once we leave the handler
    la x2, ok
    csrw mepc, x2
    mret

// used for making sure we fail if we didn't jump to the exception/NMI handler
fail_if_not_serviced:
.rept 15
    nop
.endr
    // fail if interrupt didn't get serviced
    j fail

fail:
    // write 0x01 to STDOUT for TB to fail the test
    li x3, STDOUT
    addi x5, x0, 0x01
    sb x5, 0(x3)
    j fail

ok:
    ret