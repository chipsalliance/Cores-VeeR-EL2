/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * Copyright © 2020 Sebastian Meyer
 * Copyright 2023 Antmicro, Ltd. <www.antmicro.com>
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above
 *    copyright notice, this list of conditions and the following
 *    disclaimer in the documentation and/or other materials provided
 *    with the distribution.
 *
 * 3. Neither the name of the copyright holder nor the names of its
 *    contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
 * COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
 * OF THE POSSIBILITY OF SUCH DAMAGE.
 */

/* Derived from picolibc: picocrt/machine/riscv/crt0.c
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <setjmp.h>
#include "veer.h"
#include "fault.h"
#include "trap.h"


static const char *const names[NUM_REG] = {
        "zero", "ra",   "sp",   "gp",   "tp",   "t0",   "t1",   "t2",
        "s0/fp","s1",   "a0",   "a1",   "a2",   "a3",   "a4",   "a5",
#if NUM_REG > 16
        "a6",   "a7",   "s2",   "s3",   "s4",   "s5",   "s6",   "s7",
        "s8",   "s9",   "s10",  "s11",  "t3",   "t4",   "t5",   "t6",
#endif
};

static void __attribute__((used))
_ctrap(struct fault *fault)
{
        int r;
        printf("RISC-V fault\n");
        for (r = 0; r < NUM_REG; r++)
                printf("\tx%d %-5.5s%s 0x" FMT "\n", r, names[r], r < 10 ? " " : "", fault->r[r]);
        printf("\tmepc:     0x" FMT "\n", fault->mepc);
        printf("\tmcause:   0x" FMT "\n", fault->mcause);
        printf("\tmtval:    0x" FMT "\n", fault->mtval);

        fault_return(fault);
        exit(1);
}

void __attribute__((naked)) __section(".text.init") __attribute__((used)) __attribute((aligned(4)))
_trap(void)
{
#ifndef __clang__
        __asm__(".option	nopic");
#endif

        /* Build a known-working C environment */
	__asm__(".option	push\n"
                ".option	norelax\n"
                "la	        sp, FAULTSTACK\n"
                ".option	pop");

        /* Make space for saved registers */
        __asm__("addi   sp,sp,%0" :: "i" (-sizeof(struct fault)));

        /* Save registers on stack */
#define SAVE_REG(num)   \
        __asm__(SD"     x%0, %1(sp)" :: "i" (num), \
                "i" ((num) * sizeof(unsigned long) + offsetof(struct fault, r)))

#define SAVE_REGS_8(base) \
        SAVE_REG(base+0); SAVE_REG(base+1); SAVE_REG(base+2); SAVE_REG(base+3); \
        SAVE_REG(base+4); SAVE_REG(base+5); SAVE_REG(base+6); SAVE_REG(base+7)

        SAVE_REGS_8(0);
        SAVE_REGS_8(8);
#ifndef __riscv_32e
        SAVE_REGS_8(16);
        SAVE_REGS_8(24);
#endif

#define SAVE_CSR(name)  \
        __asm__("csrr   t0, "PASTE(name));\
        __asm__(SD"  t0, %0(sp)" :: "i" (offsetof(struct fault, name)))

        SAVE_CSR(mepc);
        SAVE_CSR(mcause);
        SAVE_CSR(mtval);

        /*
         * Pass pointer to saved registers in first parameter register
         */
        __asm__("mv     a0, sp");

        /* Enable FPU (just in case) */
#ifdef __riscv_flen
	__asm__("csrr	t0, mstatus\n"
                "li	t1, 8192\n"     	// 1 << 13 = 8192
                "or	t0, t1, t0\n"
                "csrw	mstatus, t0\n"
                "csrwi	fcsr, 0");
#endif
        __asm__("j      _ctrap");
}
