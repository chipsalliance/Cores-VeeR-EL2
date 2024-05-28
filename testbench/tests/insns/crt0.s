# SPDX-License-Identifier: Apache-2.0

.section .text.init
.global _start
_start:

        # Setup stack
        la sp, STACK

        # Setup trap handler
        la t0, _trap
        csrw mtvec, t0

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

_trap:

        # Push stuff
        addi sp, sp, -17*4

        sw ra, 0*4(sp)
        sw a0, 1*4(sp)
        sw a1, 2*4(sp)
        sw a2, 3*4(sp)
        sw a3, 4*4(sp)
        sw a4, 5*4(sp)
        sw a5, 6*4(sp)
        sw a6, 7*4(sp)
        sw a7, 8*4(sp)
        sw t0, 9*4(sp)
        sw t1, 10*4(sp)
        sw t2, 11*4(sp)
        sw t3, 12*4(sp)
        sw t4, 13*4(sp)
        sw t5, 14*4(sp)
        sw t6, 15*4(sp)

        call trap_handler

        # Advance mepc if the cause is not an external interrupt
        csrr t0, mcause
        li t1, 0x80000000
        and t0, t0, t1
        bne t0, x0, _is_irq

        csrr t0, mepc
        addi t0, t0, 4
        csrw mepc, t0

_is_irq:

        # Pop stuff
        lw ra, 0*4(sp)
        lw a0, 1*4(sp)
        lw a1, 2*4(sp)
        lw a2, 3*4(sp)
        lw a3, 4*4(sp)
        lw a4, 5*4(sp)
        lw a5, 6*4(sp)
        lw a6, 7*4(sp)
        lw a7, 8*4(sp)
        lw t0, 9*4(sp)
        lw t1, 10*4(sp)
        lw t2, 11*4(sp)
        lw t3, 12*4(sp)
        lw t4, 13*4(sp)
        lw t5, 14*4(sp)
        lw t6, 15*4(sp)

        addi sp, sp, 17*4

        mret

.section .data.io
.global tohost
tohost: .word 0

