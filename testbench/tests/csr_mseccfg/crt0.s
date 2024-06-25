# SPDX-License-Identifier: Apache-2.0

.option norvc
.option nopic

.section .text.init
.align 4
.global _start
_start:

        # Setup stack
        la sp, STACK

        # Setup trap handler
        la t0, _trap_entry
        csrw mtvec, t0

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

.align 8
_trap_entry:
        # In this test no trap should happen. Trigger test failure if it does.
        la  a0, 1
        j   _finish

.section .data.io
.global tohost
tohost: .word 0

