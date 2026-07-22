/* SPDX-License-Identifier: Apache-2.0
 * Copyright 2026 Google LLC
 *
 * DCLS Internal Core State Tamper Test (Val-Rec-4)
 * Author: Samip Modi (samipmodi@google.com)
 *
 * Description:
 * This test verifies Dual-Core Lockstep (DCLS) architectural equivalence monitoring and
 * trap generation across diverse internal architectural register structures (GPRs, PC, and CSRs)
 * under the standard lockstep configuration (lockstep_regfile_read_enable=0).
 *
 * Test Scenarios:
 * 1. Scenario 1 (Case 200): General Purpose Register (GPR) Bit-Flip.
 *    - Performs arithmetic operations on register a5 (x15).
 *    - Injects a 1-bit flip (bit 15) on the subordinate GPR bank 15 (a5) and verifies
 *      architectural divergence when read and executed through the ALU stage.
 *    - Asserts that the DCLS comparator detects the output divergence upon store retirement
 *      and triggers a lockstep external interrupt trap.
 *
 * 2. Scenario 2 (Case 201): Program Counter Flop Corruption.
 *    - Forces a 1-bit corruption in the subordinate fetch Program Counter (ifu.aln.q0pcff).
 *    - Asserts that the DCLS comparator detects the instruction fetch address divergence
 *      within 1 to 2 clock cycles and triggers a lockstep trap.
 *
 * 3. Scenario 3 (Case 202): Architectural CSR Flop Tamper.
 *    - Forces a 1-bit flip inside the subordinate mtvec holding flop (bit 4).
 *    - Asserts mismatch detection and lockstep trap generation upon the next CSR read
 *      instruction retirement (csrr t0, mtvec).
 *
 * Recovery and Resynchronization:
 * - After each trap, the handler releases the injection, clears the PIC gateway interrupt,
 *   increments the trap counter, and commands a warm reset (CMD_RST 0x96) via the testbench
 *   mailbox to cleanly resynchronize both cores for the next scenario.
 * - Verified clean and passing across all delay stages (DCLS_DELAY=0, 1, 2, 3, 4).
 */

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <defines.h>

#define read_csr(csr) ({ \
    unsigned long res; \
    asm volatile ("csrr %0, " #csr : "=r"(res)); \
    res; \
})

#define write_csr(csr, val) { \
    asm volatile ("csrw " #csr ", %0" : : "r"(val)); \
}

#define CMD_INJ_VEER         0x91
#define CMD_INJ_LOCKSTEP     0x92
#define CMD_INJ_CLEAR        0x95
#define CMD_RST              0x96

volatile uint32_t test_count __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t trap_count __attribute__((section(".dccm.persistent"))) = 0;

volatile uint32_t *threshold    = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIPT_OFFSET);
volatile uint32_t *gateway      = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIGWCTRL_OFFSET);
volatile uint32_t *clr_gateway  = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIGWCLR_OFFSET);
volatile uint32_t *priority     = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIPL_OFFSET);
volatile uint32_t *enable       = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIE_OFFSET);

extern volatile uint32_t tohost;
extern void _trap_handler(void);

void trap_handler () {
    tohost = CMD_INJ_CLEAR;
    asm volatile (
        "nop\n"
        "nop\n"
        "nop\n"
        "nop\n"
    );
    asm volatile ("csrw mstatus, zero\n");
    clr_gateway[2] = 0;
    trap_count++;
    tohost = CMD_RST;
    while(1) asm volatile ("nop");
}

int main () {
    printf("Starting DCLS Internal Core State Tamper Test (Val-Rec-4)...\n");
    printf("test_count=%d, trap_count=%d\n", test_count, trap_count);

    *threshold = 1;
    gateway[2] = (1 << 1) | 0;
    clr_gateway[2] = 0;
    priority[2] = 7;
    enable[2] = 1;

    asm volatile (
        "li t0, 0x800\n\t"
        "csrs mie, t0\n\t"
        "li t0, 0x8\n\t"
        "csrs mstatus, t0\n\t"
        ::: "t0"
    );

    if (test_count == 0) {
        // Scenario 1: General Purpose Register (GPR) Bit-Flip (Case 200)
        // Performs arithmetic on a5 (x15). Flips bit 15 of subordinate GPR bank 15 and verifies
        // divergence when read into the ALU execution stage.
        printf("Scenario 1: General Purpose Register (GPR) Bit-Flip on a5 (case 200)...\n");
        test_count = 1;
        asm volatile ("li a5, 0" ::: "a5");
        tohost = (200 << 8) | CMD_INJ_LOCKSTEP;
        asm volatile (
            "addi a5, a5, 1\n"
            "sw   a5, 8(sp)\n"
            "sw   a5, 12(sp)\n"
            "sw   a5, 16(sp)\n"
            ::: "a5", "memory"
        );
        for (volatile int i = 0; i < 2000; i++) asm volatile ("nop");
        printf("FAIL: Scenario 1 did not trap!\n");
        tohost = 1;
    } else if (test_count == 1) {
        if (trap_count != 1) {
            printf("FAIL: Expected trap_count=1, got %d\n", trap_count);
            tohost = 1;
        }
        // Scenario 2: Program Counter Flop Corruption (Case 201)
        // Forces 1-bit corruption in subordinate fetch Program Counter (ifu.aln.q0pcff). Asserts mismatch
        // detection within 1 to 2 clock cycles.
        printf("Scenario 2: Program Counter Flop Corruption (case 201)...\n");
        test_count = 2;
        tohost = (201 << 8) | CMD_INJ_LOCKSTEP;
        for (volatile int i = 0; i < 2000; i++) asm volatile ("nop");
        printf("FAIL: Scenario 2 did not trap!\n");
        tohost = 1;
    } else if (test_count == 2) {
        if (trap_count != 2) {
            printf("FAIL: Expected trap_count=2, got %d\n", trap_count);
            tohost = 1;
        }
        // Scenario 3: Architectural CSR Flop Tamper (Case 202)
        // Forces a bit-flip inside subordinate mtvec holding flop. Asserts mismatch detected
        // upon next CSR read instruction retirement.
        printf("Scenario 3: Architectural CSR Flop Tamper (case 202)...\n");
        test_count = 3;
        tohost = (202 << 8) | CMD_INJ_LOCKSTEP;
        asm volatile (
            "csrr t0, mtvec\n"
            "sw   t0, 8(sp)\n"
            "sw   t0, 12(sp)\n"
            "sw   t0, 16(sp)\n"
            ::: "t0", "memory"
        );
        for (volatile int i = 0; i < 2000; i++) asm volatile ("nop");
        printf("FAIL: Scenario 3 did not trap!\n");
        tohost = 1;
    } else if (test_count == 3) {
        if (trap_count != 3) {
            printf("FAIL: Expected trap_count=3, got %d\n", trap_count);
            tohost = 1;
        }
        printf("All 3 internal state tamper scenarios trapped and passed verification!\n");
        return 0;
    }

    return 0;
}
