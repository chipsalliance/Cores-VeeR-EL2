# SPDX-License-Identifier: Apache-2.0

.section .text.init
.global _start
_start:

        # Setup stack
        la sp, STACK

        # Setup trap handler
        la t0, _trap_handler
        csrw mtvec, t0

        # Call main()
        call main

        # Map exit code: == 0 - success, != 0 - failure
        mv  a1, a0
        li  a0, 0xff
        beq a1, x0, _finish
        li  a0, 1 # fail

.global _finish
_finish:
        la t0, tohost
        sb a0, 0(t0) # Signal testbench termination
        beq x0, x0, _finish
        .rept 10
        nop
        .endr

.global _trap_handler
_trap_handler:
    call trap_handler
    j _start

.section .text.nmi
.align 4
_nmi:
    la t0, _trap_handler
    jr t0

.section .data.io
.global tohost
tohost: .word 0
