/* SPDX-License-Identifier: Apache-2.0
 * Copyright 2026 Google LLC
 *
 * DCLS Safety Scope: Multi-Memory Asymmetric ECC Threshold Mismatch Test
 * Author: Samip Modi (samipmodi@google.com)
 *
 * Description:
 * This test verifies Dual-Core Lockstep (DCLS) safety isolation and architectural equivalence
 * monitoring when asymmetric RAS threshold alert events occur across all 3 internal core
 * memories (DCCM, ICCM, and ICache) on only one of the redundant execution cores.
 *
 * Test Phases:
 * 1. Phase 1 (Case 203): DCCM SBE Threshold Asymmetric Alert (MDCCMECT CSR 0x7F2)
 *    - Injects an asymmetric DCCM threshold alert exclusively onto the subordinate shadow core.
 *    - Asserts that the DCLS comparator detects core divergence and triggers a lockstep mismatch trap.
 *
 * 2. Phase 2 (Case 204): ICCM SBE Threshold Asymmetric Alert (MICCMECT CSR 0x7F1)
 *    - Injects an asymmetric ICCM threshold alert exclusively onto the subordinate shadow core.
 *    - Asserts that the DCLS comparator detects core divergence and triggers a lockstep mismatch trap.
 *
 * 3. Phase 3 (Case 205): ICache ECC/Parity Threshold Asymmetric Alert (MICECT CSR 0x7F0)
 *    - Injects an asymmetric ICache threshold alert exclusively onto the subordinate shadow core.
 *    - Asserts that the DCLS comparator detects core divergence and triggers a lockstep mismatch trap.
 *
 * State Machine & Trap Verification:
 * - test_count tracks the active test phase (0 -> 1 -> 2 -> 3) and is updated in main()
 *   prior to each fault injection.
 * - trap_count tracks trap handler execution and is incremented exclusively in trap_handler().
 * - After warm reset, main() verifies that trap_count matches the completed phase before proceeding,
 *   guaranteeing independent verification of trap occurrence.
 */

#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <defines.h>

#define CMD_INJ_LOCKSTEP        0x92
#define CMD_INJ_CLEAR           0x95
#define CMD_RST                 0x96
#define TEST_PASSED             0xff
#define TEST_FAILED             0x01

extern volatile uint32_t tohost;

volatile uint32_t test_count __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t trap_count __attribute__((section(".dccm.persistent"))) = 0;

volatile uint32_t *threshold    = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIPT_OFFSET);
volatile uint32_t *gateway      = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIGWCTRL_OFFSET);
volatile uint32_t *clr_gateway  = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIGWCLR_OFFSET);
volatile uint32_t *priority     = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIPL_OFFSET);
volatile uint32_t *enable       = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIE_OFFSET);

static inline void write_mdccmect(uint32_t val) {
    __asm__ volatile ("csrw %1, %0" : : "r" (val), "i" (0x7F2));
}

static inline void write_miccmect(uint32_t val) {
    __asm__ volatile ("csrw %1, %0" : : "r" (val), "i" (0x7F1));
}

static inline void write_micect(uint32_t val) {
    __asm__ volatile ("csrw %1, %0" : : "r" (val), "i" (0x7F0));
}

void trap_handler(void) {
    uint32_t mcause;
    __asm__ volatile ("csrr %0, mcause" : "=r" (mcause));
    printf("Lockstep divergence trap detected! mcause=0x%08X\n", mcause);
    trap_count++;
    write_mdccmect(0);
    write_miccmect(0);
    write_micect(0);
    tohost = CMD_INJ_CLEAR;
    tohost = CMD_RST;
}

int main(void) {
    write_mdccmect(0);
    write_miccmect(0);
    write_micect(0);

    if (test_count == 0) {
        printf("Starting DCLS Multi-Memory Asymmetric ECC Threshold Test...\n");
    }
    printf("test_count=%d, trap_count=%d\n", test_count, trap_count);

    *threshold = 1;
    gateway[2] = (1 << 1) | 0;
    clr_gateway[2] = 0;
    priority[2] = 7;
    enable[2] = 1;

    uint32_t mie_val;
    __asm__ volatile ("csrr %0, mie" : "=r" (mie_val));
    mie_val |= (1 << 11) | (1 << 30); // Bit 11 = MEIE (PIC DCLS int), Bit 30 = MCEIE (Core ECC alert)
    __asm__ volatile ("csrw mie, %0" : : "r" (mie_val));

    uint32_t mstatus_val;
    __asm__ volatile ("csrr %0, mstatus" : "=r" (mstatus_val));
    mstatus_val |= (1 << 3);
    __asm__ volatile ("csrw mstatus, %0" : : "r" (mstatus_val));

    if (test_count == 0) {
        // Phase 1: DCCM Asymmetric ECC Threshold Alert (Case 203)
        printf("\n[Phase 1] Injecting asymmetric DCCM threshold alert onto Shadow Core (Case 203)...\n");
        test_count = 1;
        write_mdccmect(2 << 27);
        tohost = (203 << 8) | CMD_INJ_LOCKSTEP;
        for (volatile int i = 0; i < 500; i++) asm volatile ("nop");
        printf("FAIL: Phase 1 (DCCM Case 203) did not trap!\n");
        tohost = 1;
    } else if (test_count == 1) {
        if (trap_count != 1) {
            printf("FAIL: Phase 1 Expected trap_count=1, got %d\n", trap_count);
            tohost = 1;
        }
        // Phase 2: ICCM Asymmetric ECC Threshold Alert (Case 204)
        printf("\n[Phase 2] Injecting asymmetric ICCM threshold alert onto Shadow Core (Case 204)...\n");
        test_count = 2;
        write_miccmect(2 << 27);
        tohost = (204 << 8) | CMD_INJ_LOCKSTEP;
        for (volatile int i = 0; i < 500; i++) asm volatile ("nop");
        printf("FAIL: Phase 2 (ICCM Case 204) did not trap!\n");
        tohost = 1;
    } else if (test_count == 2) {
        if (trap_count != 2) {
            printf("FAIL: Phase 2 Expected trap_count=2, got %d\n", trap_count);
            tohost = 1;
        }
        // Phase 3: ICache Asymmetric ECC Threshold Alert (Case 205)
        printf("\n[Phase 3] Injecting asymmetric ICache threshold alert onto Shadow Core (Case 205)...\n");
        test_count = 3;
        write_micect(2 << 27);
        tohost = (205 << 8) | CMD_INJ_LOCKSTEP;
        for (volatile int i = 0; i < 500; i++) asm volatile ("nop");
        printf("FAIL: Phase 3 (ICache Case 205) did not trap!\n");
        tohost = 1;
    } else if (test_count == 3) {
        if (trap_count != 3) {
            printf("FAIL: Phase 3 Expected trap_count=3, got %d\n", trap_count);
            tohost = 1;
        }
        printf("\n=================================================================\n");
        printf(" DCLS Multi-Memory Asymmetric ECC Threshold Test PASSED.\n");
        printf(" (All 3 Memories DCCM, ICCM, ICache Verified Against Core Divergence)\n");
        printf("=================================================================\n");

        return 0;
    }

    return 0;
}
