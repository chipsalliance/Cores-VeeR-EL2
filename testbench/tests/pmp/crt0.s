# SPDX-License-Identifier: Apache-2.0

.option norvc
.option nopic

.section .text.init
.align 4
.global _start
_start:

        # Setup stack
        la sp, _stack_hi

        # Setup trap handler
        la t0, _trap_entry
        csrw mtvec, t0

        # Clear .bss
        la t0, _bss
        la t1, _data_end
bss:    sw x0, 0(t0)
        addi t0, t0, 4
        bne t0, t1, bss

        # Call main()
        call main

        # Map exit code: 0 - success, not 0 - failure
        mv  a1, a0
        li  a0, 0xff # ok
        beq a1, x0, _finish
        li  a0, 1 # fail

.global _finish
_finish:
        la t0, tohost
        sb a0, 0(t0) # Signal testbench termination, a0 holds the exit code
        beq x0, x0, _finish
        .rept 10
        nop
        .endr

.align 8
_trap_entry:

        # Push one reg
        addi sp, sp, -4
        sw t0, 0(sp)

        # Check for ECALL.U
        csrr t0, mcause
        addi t0, t0, -8
        bnez t0, _trap_not_ecall_u

        # Pop one reg
        lw t0, 0(sp)
        addi sp, sp, +4

        # "return" to the ucall
        j _ucall_ret

_trap_not_ecall_u:

        # Pop one reg
        # FIXME: Integrate pushing and popping
        lw t0, 0(sp)
        addi sp, sp, +4

        # Push stuff
        addi sp, sp, -35*4 # (32 regs + 3 CSRs)

        sw x0 ,  0*4(sp)
        sw x1 ,  1*4(sp)
        sw x2 ,  2*4(sp)
        sw x3 ,  3*4(sp)
        sw x4 ,  4*4(sp)
        sw x5 ,  5*4(sp)
        sw x6 ,  6*4(sp)
        sw x7 ,  7*4(sp)
        sw x8 ,  8*4(sp)
        sw x9 ,  9*4(sp)
        sw x10, 10*4(sp)
        sw x11, 11*4(sp)
        sw x12, 12*4(sp)
        sw x13, 13*4(sp)
        sw x14, 14*4(sp)
        sw x15, 15*4(sp)
        sw x16, 16*4(sp)
        sw x17, 17*4(sp)
        sw x18, 18*4(sp)
        sw x19, 19*4(sp)
        sw x20, 20*4(sp)
        sw x21, 21*4(sp)
        sw x22, 22*4(sp)
        sw x23, 23*4(sp)
        sw x24, 24*4(sp)
        sw x25, 25*4(sp)
        sw x26, 26*4(sp)
        sw x27, 27*4(sp)
        sw x28, 28*4(sp)
        sw x29, 29*4(sp)
        sw x30, 30*4(sp)
        sw x31, 31*4(sp)

        # push CSRs
        csrr t0, mepc
        sw t0, 32*4(sp)
        csrr t0, mcause
        sw t0, 33*4(sp)
        csrr t0, mtval
        sw t0, 34*4(sp)

        # Make a0 point to the stack frame which layout matches the fault struct
        mv a0, sp

        # Call trap handler
        call trap_handler

        # Advance mepc if the cause is not an external interrupt
        lw t0, 33*4(sp)
        li t1, 0x80000000
        and t0, t0, t1
        bne t0, x0, _trap_is_irq

        csrr t0, mepc
        addi t0, t0, 4
        csrw mepc, t0

_trap_is_irq:

        # Pop stuff
        lw x0 ,  0*4(sp)
        lw x1 ,  1*4(sp)
        lw x2 ,  2*4(sp)
        lw x3 ,  3*4(sp)
        lw x4 ,  4*4(sp)
        lw x5 ,  5*4(sp)
        lw x6 ,  6*4(sp)
        lw x7 ,  7*4(sp)
        lw x8 ,  8*4(sp)
        lw x9 ,  9*4(sp)
        lw x10, 10*4(sp)
        lw x11, 11*4(sp)
        lw x12, 12*4(sp)
        lw x13, 13*4(sp)
        lw x14, 14*4(sp)
        lw x15, 15*4(sp)
        lw x16, 16*4(sp)
        lw x17, 17*4(sp)
        lw x18, 18*4(sp)
        lw x19, 19*4(sp)
        lw x20, 20*4(sp)
        lw x21, 21*4(sp)
        lw x22, 22*4(sp)
        lw x23, 23*4(sp)
        lw x24, 24*4(sp)
        lw x25, 25*4(sp)
        lw x26, 26*4(sp)
        lw x27, 27*4(sp)
        lw x28, 28*4(sp)
        lw x29, 29*4(sp)
        lw x30, 30*4(sp)
        lw x31, 31*4(sp)

        addi sp, sp, 35*4

        # Return
        mret

.section .text
.global ucall
ucall:

        # Prologue
        addi sp, sp, -4*4
        sw ra, 0*4(sp)
        sw s0, 1*4(sp)
        sw s1, 2*4(sp)

        # Clear mstatus MPP
        csrr s0, mstatus
        li s1, 0xFFFFE7FF
        and s0, s0, s1
        csrw mstatus, s0
        # Set the call vector (first arg)
        csrw mepc, a0
        # Store the return address to proxy code in ra
        la ra, _ucall_proxy
        # Shift arguments a[n] <- a[n+1]
        mv a0, a1
        mv a1, a2
        mv a2, a3
        mv a3, a4
        mv a4, a5
        mv a5, a6
        mv a6, a7
        li a7, 0
        # Jump
        mret

_ucall_ret:

        # Epilogue
        lw ra, 0*4(sp)
        lw s0, 1*4(sp)
        lw s1, 2*4(sp)
        addi sp, sp, +4*4
        ret

_ucall_proxy:
        ecall


.global rv_setjmp_m
rv_setjmp_m:

        # Save PC
        sw s0, -4(sp)
        auipc s0, 0
        addi s0, s0, -4
        sw s0, 0(a0)
        lw s0, -4(sp)

        # Save context to the buffer pointed by a0
        # the first word is the PC
        sw x1 ,  1*4(a0)
        sw x2 ,  2*4(a0)
        sw x3 ,  3*4(a0)
        sw x4 ,  4*4(a0)
        sw x5 ,  5*4(a0)
        sw x6 ,  6*4(a0)
        sw x7 ,  7*4(a0)
        sw x8 ,  8*4(a0)
        sw x9 ,  9*4(a0)
        sw x10, 10*4(a0)
        sw x11, 11*4(a0)
        sw x12, 12*4(a0)
        sw x13, 13*4(a0)
        sw x14, 14*4(a0)
        sw x15, 15*4(a0)
        sw x16, 16*4(a0)
        sw x17, 17*4(a0)
        sw x18, 18*4(a0)
        sw x19, 19*4(a0)
        sw x20, 20*4(a0)
        sw x21, 21*4(a0)
        sw x22, 22*4(a0)
        sw x23, 23*4(a0)
        sw x24, 24*4(a0)
        sw x25, 25*4(a0)
        sw x26, 26*4(a0)
        sw x27, 27*4(a0)
        sw x28, 28*4(a0)
        sw x29, 29*4(a0)
        sw x30, 30*4(a0)
        sw x31, 31*4(a0)

        # Return the exit code set by rv_longjmp if any
        lw a0, 32*4(a0)
        ret

.global rv_longjmp_m
rv_longjmp_m:

        # Set return address
        lw s0, 0(a0)
        csrw mepc, s0

        # Set rv_setjmp exit code
        sw a1, 32*4(a0)

        # Make sure that we return to M mode
        csrr s0, mstatus
        li s1, 0x00001800
        or s0, s0, s1
        csrw mstatus, s0

        # Restore the context to what's pointed by a0
        lw x1 ,  1*4(a0)
        lw x2 ,  2*4(a0)
        lw x3 ,  3*4(a0)
        lw x4 ,  4*4(a0)
        lw x5 ,  5*4(a0)
        lw x6 ,  6*4(a0)
        lw x7 ,  7*4(a0)
        lw x8 ,  8*4(a0)
        lw x9 ,  9*4(a0)
        lw x10, 10*4(a0)
        lw x11, 11*4(a0)
        lw x12, 12*4(a0)
        lw x13, 13*4(a0)
        lw x14, 14*4(a0)
        lw x15, 15*4(a0)
        lw x16, 16*4(a0)
        lw x17, 17*4(a0)
        lw x18, 18*4(a0)
        lw x19, 19*4(a0)
        lw x20, 20*4(a0)
        lw x21, 21*4(a0)
        lw x22, 22*4(a0)
        lw x23, 23*4(a0)
        lw x24, 24*4(a0)
        lw x25, 25*4(a0)
        lw x26, 26*4(a0)
        lw x27, 27*4(a0)
        lw x28, 28*4(a0)
        lw x29, 29*4(a0)
        lw x30, 30*4(a0)
        lw x31, 31*4(a0)

        # Return
        mret

.section .data.io
.global tohost
tohost: .dword 0
.global fromhost
fromhost: .dword 0
