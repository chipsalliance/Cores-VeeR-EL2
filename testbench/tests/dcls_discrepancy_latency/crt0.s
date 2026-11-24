# SPDX-License-Identifier: Apache-2.0

.section .text.init
.global _start
_start:

        # Setup stack
        la sp, STACK

        # Mark tohost region 0xd (0xd0580000) as side-effect (mrac[27] = 1)
        # to prevent AXI write-buffer coalescing of consecutive mailbox stores,
        # and enable caching for .text region 0x8 (0x80000000, mrac[16] = 1).
        li t0, 0x08010000
        csrw 0x7c0, t0
        fence.i

        # Setup aligned trap vector table (supports both direct mode and
        # vectored mode when Case 64 forces mtvec_ff.dout[0] = 1 under
        # FAST_INTERRUPT_REDIRECT=0).
        la t0, _trap_vector_table
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
        fence
        beq x0, x0, _finish
        .rept 10
        nop
        .endr

.balign 64
.option push
.option norvc
.global _trap_vector_table
_trap_vector_table:
        .rept 16
        j _trap_handler
        .endr
.option pop

.balign 4
.global _trap_handler
_trap_handler:
        # Clear fault injection using byte stores (sb) across three independent
        # register pairs so even a forced bit-0 mismatch on t0 (x5) cannot raise
        # a misaligned side-effect store exception on tohost (0xd0580000).
        la t0, tohost
        li t1, 0x95
        sb t1, 0(t0)
        fence
        la a0, tohost
        li a1, 0x95
        sb a1, 0(a0)
        fence
        la s0, tohost
        li s1, 0x95
        sb s1, 0(s0)
        fence
        .rept 8
        nop
        .endr

        # Restore a valid DCCM stack pointer before entering C trap_handler()
        # in case the trap fired while testing x2 (sp).
        la sp, STACK

        # Call C trap handler (validates mcause/MEIP[2], logs result, and triggers reset)
        call trap_handler

        # Fallback reset if trap_handler returns
        la t0, tohost
        li t1, 0x96
        sb t1, 0(t0)
        fence
do_nothing:
        j do_nothing

.section .text.nmi
.align 4
_nmi:
    la t0, _trap_handler
    jr t0

.section .data.io
.global tohost
tohost: .word 0
