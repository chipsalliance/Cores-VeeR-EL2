# SPDX-License-Identifier: Apache-2.0

.section .text.init
.global _start
_start:

        # Setup stack
        la sp, STACK

        # Setup trap handler
        la t0, _trap_handler
        csrw mtvec, t0

        # Enable External Interrupts (MIE.MEIE, bit 11)
        li t0, 0x800
        csrs mie, t0
        # Enable global interrupts (mstatus.MIE, bit 3)
        li t0, 0x8
        csrs mstatus, t0

        # Call main()
        call main

        # Map exit code: == 0 - success, != 0 - failure
        mv  a1, a0
        li  a0, 0xfe # ok (check for `corruption_detected_o` status)
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
        # Clear injection using t0 (x5) and t1 (x6)
        la t0, tohost
        li t1, 0x95
        sw t1, 0(t0)
        # Also clear injection using a0 (x10) and a1 (x11) in case t0/t1 was corrupted
        la a0, tohost
        li a1, 0x95
        sw a1, 0(a0)
        # Also clear injection using s0 (x8) and s1 (x9) in case both were corrupted
        la s0, tohost
        li s1, 0x95
        sw s1, 0(s0)

        # Wait for release to take effect in RTL
        .rept 10
        nop
        .endr

        # Now all registers are released! Trigger hardware reset:
        la t0, tohost
        li t1, 0x96
        sw t1, 0(t0)
1:      j 1b

.section .text.nmi
.align 4
_nmi:
    la t0, _trap_handler
    jr t0

.section .data.io
.global tohost
tohost: .word 0

