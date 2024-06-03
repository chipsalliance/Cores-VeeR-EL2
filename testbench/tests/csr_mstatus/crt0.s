# SPDX-License-Identifier: Apache-2.0

.section .text.init
.global _start
_start:

        # Setup stack
        la sp, STACK

        # Setup PMP
        # Region 0 TOR 0x00000000-0xFFFFFFFF RWX
        li t0, 0xFFFFFFFF
        csrw pmpaddr0, t0
        li t0, 0x0000000F
        csrw pmpcfg0, t0

        # Call main()
        call main

        # Map exit code: == 0 - success, != 0 - failure
        mv  a1, a0
        li  a0, 0xff # ok
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

.section .data.io
.global tohost
tohost: .word 0

