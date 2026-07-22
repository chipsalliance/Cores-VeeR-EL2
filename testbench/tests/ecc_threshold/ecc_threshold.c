/* SPDX-License-Identifier: Apache-2.0
 * Copyright 2026 Google LLC
 *
 * Core RAS Scope: Comprehensive Multi-Memory ECC/Parity Counter & Threshold Alert Test
 * Author: Samip Modi (samipmodi@google.com)
 *
 * Architecture & Test Intent:
 * VeeR EL2 provides internal Reliability, Availability, and Serviceability (RAS) Single-Bit
 * Error (SBE) counting and threshold alert interrupt generation across all 3 internal core
 * memories (DCCM, ICCM, and ICache).
 *
 * Hardware Threshold Comparator Formula (TLU el2_dec_tlu_ctl.sv):
 * Each memory has an independent CSR containing a 5-bit threshold exponent field (bits [31:27],
 * value T) and a 27-bit SBE counter field (bits [26:0], value C):
 *     assign ce_req = |({32'hffffffff << CSR[31:27]} & {5'b0, CSR[26:0]});
 * An alert condition trips whenever the error count reaches or exceeds 2^T (e.g. T=2 trips
 * at Count >= 4). When tripped, hardware asserts Machine Correctable Error Interrupt (ce_int),
 * which raises an interrupt via mie[30] (MCEIE) to mtvec.
 *
 * Test Phases:
 * 1. Phase 1: Data Closely Coupled Memory (DCCM) SBE Threshold Alert (MDCCMECT CSR 0x7F2)
 *    - Programs MDCCMECT threshold exponent to T=2 (alert trips at count >= 4) and enables mie[30].
 *    - Injects single-bit write ECC bitflips into DCCM (tohost mailbox 0xe2).
 *    - Performs repeated read/write access cycles to dummy DCCM data.
 *    - Validates that LSU hardware detects and corrects each SBE, increments MDCCMECT counter cleanly,
 *      and triggers a Machine Correctable Error Interrupt trap upon reaching the threshold.
 *
 * 2. Phase 2: Instruction Closely Coupled Memory (ICCM) SBE Threshold Alert (MICCMECT CSR 0x7F1)
 *    - Relocates target executable subroutine into ICCM memory (0xee000000) while single-bit ICCM
 *      error injection is active (tohost mailbox 0xe0).
 *    - Programs MICCMECT threshold exponent to T=2 and enables mie[30].
 *    - Executes instructions from ICCM, causing the Instruction Fetch Unit (IFU) SEC-DED decoder
 *      to correct read errors, increment MICCMECT counter, and generate the threshold alert trap.
 *
 * 3. Phase 3: Instruction Cache (ICache) Parity/ECC Threshold Alert (MICECT CSR 0x7F0)
 *    - Programs MICECT threshold exponent to T=2 and enables mie[30].
 *    - Warms up target instruction cache line in ICache.
 *    - Injects single-bit read data faults via tohost mailbox 0x89.
 *    - Verifies that ICache core-side decoder detects the fault, flushes the pipeline, refetches
 *      the instruction, increments MICECT counter, and asserts the threshold alert interrupt.
 */

#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>

#define INJECT_ICCM_SINGLE_BIT       0xe0
#define INJECT_DCCM_SINGLE_BIT       0xe2
#define DISABLE_ERROR_INJECTION      0xe4
#define CMD_INJECT_ICACHE_SINGLE_BIT 0x89

#define TEST_PASSED                  0xff
#define TEST_FAILED                  0x01

#define ICCM_SADDR                   0xee000000

extern volatile uint32_t tohost;
extern uintptr_t iccm_start, iccm_end;

volatile uint32_t dccm_test_data[10] __attribute__((section(".dccm"))) = { 0x11111111, 0x22222222, 0x33333333, 0x44444444, 0x55555555, 0x66666666, 0x77777777, 0x88888888, 0x99999999, 0xAAAAAAAA };
volatile int trap_count = 0;

static inline uint32_t read_mdccmect(void) {
    uint32_t val;
    __asm__ volatile ("csrr %0, %1" : "=r" (val) : "i" (0x7F2));
    return val;
}

static inline void write_mdccmect(uint32_t val) {
    __asm__ volatile ("csrw %1, %0" : : "r" (val), "i" (0x7F2));
}

static inline uint32_t read_miccmect(void) {
    uint32_t val;
    __asm__ volatile ("csrr %0, %1" : "=r" (val) : "i" (0x7F1));
    return val;
}

static inline void write_miccmect(uint32_t val) {
    __asm__ volatile ("csrw %1, %0" : : "r" (val), "i" (0x7F1));
}

static inline uint32_t read_micect(void) {
    uint32_t val;
    __asm__ volatile ("csrr %0, %1" : "=r" (val) : "i" (0x7F0));
    return val;
}

static inline void write_micect(uint32_t val) {
    __asm__ volatile ("csrw %1, %0" : : "r" (val), "i" (0x7F0));
}

static inline void enable_mceie(void) {
    uint32_t mie_val;
    __asm__ volatile ("csrr %0, mie" : "=r" (mie_val));
    mie_val |= (1 << 30); // Bit 30 = Machine Correctable Error Interrupt Enable (MCEIE in VeeR EL2)
    __asm__ volatile ("csrw mie, %0" : : "r" (mie_val));
    uint32_t mstatus_val;
    __asm__ volatile ("csrr %0, mstatus" : "=r" (mstatus_val));
    mstatus_val |= (1 << 3); // Bit 3 = Global Machine Interrupt Enable (mstatus.MIE)
    __asm__ volatile ("csrw mstatus, %0" : : "r" (mstatus_val));
}

static inline void disable_mceie(void) {
    uint32_t mie_val;
    __asm__ volatile ("csrr %0, mie" : "=r" (mie_val));
    mie_val &= ~(1 << 30);
    __asm__ volatile ("csrw mie, %0" : : "r" (mie_val));
}

volatile uint32_t last_mcause = 0;

void trap_handler(void) {
    tohost = DISABLE_ERROR_INJECTION;
    disable_mceie(); // Mask level-sensitive interrupt so return resumes cleanly
    trap_count++;
    __asm__ volatile ("csrr %0, mcause" : "=r" (last_mcause));
    printf("ECC threshold alert trap received! mcause=0x%08X\n", last_mcause);
}

// 5 separate single-instruction functions located in ICCM section
void iccm_fn_1(void) __attribute__((aligned(4), section(".iccm_data0"), noinline));
void iccm_fn_1(void) { __asm__ volatile ("ret"); }

void iccm_fn_2(void) __attribute__((aligned(4), section(".iccm_data0"), noinline));
void iccm_fn_2(void) { __asm__ volatile ("ret"); }

void iccm_fn_3(void) __attribute__((aligned(4), section(".iccm_data0"), noinline));
void iccm_fn_3(void) { __asm__ volatile ("ret"); }

void iccm_fn_4(void) __attribute__((aligned(4), section(".iccm_data0"), noinline));
void iccm_fn_4(void) { __asm__ volatile ("ret"); }

void iccm_fn_5(void) __attribute__((aligned(4), section(".iccm_data0"), noinline));
void iccm_fn_5(void) { __asm__ volatile ("ret"); }

// Function aligned to 16-byte boundary to isolate ICache line
__attribute__((noinline, aligned(16)))
void icache_target_func(void) {
    __asm__ volatile ("nop; nop; nop; nop;");
}

int main(void) {
    printf("=================================================================\n");
    printf(" Starting Core RAS Scope: Multi-Memory ECC Threshold Alert Test\n");
    printf("=================================================================\n");

    // Clear all memory error counters and thresholds
    write_mdccmect(0);
    write_miccmect(0);
    write_micect(0);

    // Configure mtvec to assembly interrupt frame wrapper and enable global interrupts (mstatus.MIE)
    extern void _trap_handler(void);
    __asm__ volatile ("csrw mtvec, %0" : : "r" ((uint32_t)&_trap_handler));
    uint32_t mstatus_val;
    __asm__ volatile ("csrr %0, mstatus" : "=r" (mstatus_val));
    mstatus_val |= (1 << 3);
    __asm__ volatile ("csrw mstatus, %0" : : "r" (mstatus_val));

    int pass = 1;

    // =================================================================
    // Phase 1: DCCM ECC Threshold Alert Test (mdccmect 0x7F2)
    // =================================================================
    printf("\n[Phase 1] Testing DCCM SBE Counter & Threshold Alert (0x7F2)...\n");
    trap_count = 0;
    last_mcause = 0;
    int phase1_pass = 1;

    // Corrupt 6 distinct words in DCCM (Word 0 primes the latch, Words 1-5 store SBEs)
    tohost = INJECT_DCCM_SINGLE_BIT;
    for (int k = 0; k < 6; k++) {
        dccm_test_data[k] = 0xA5A50000 | k;
    }
    tohost = DISABLE_ERROR_INJECTION;

    write_mdccmect(2 << 27); // Set threshold exponent = 2 (triggers at count >= 2^2 = 4)
    enable_mceie();
    printf("Programmed MDCCMECT threshold exponent to 2 (triggers at count >= 4). Initial MDCCMECT=0x%08X\n", read_mdccmect());

    for (int i = 1; i <= 5; i++) {
        // Read back corrupted word from DCCM to trigger LSU SEC-DED detection & hardware counter increment
        volatile uint32_t rd = dccm_test_data[i];

        uint32_t mdccm = read_mdccmect();
        uint32_t cnt = mdccm & 0x7FFFFFF;
        printf("DCCM Access %d: MDCCMECT=0x%08X (Counter=%d, Traps=%d)\n", i, mdccm, cnt, trap_count);

        // Strict Check: Ensure no premature trap fires while count < 4
        if (cnt < 4 && trap_count != 0) {
            printf("  --> ERROR: Premature trap fired at Counter=%d (expected Traps=0)!\n", cnt);
            phase1_pass = 0;
        }
        for (int slp = 0; slp < 10; slp++) asm volatile ("nop");
    }
    disable_mceie();

    uint32_t dccm_cnt = read_mdccmect() & 0x7FFFFFF;
    if (dccm_cnt < 4) {
        printf("  --> ERROR: DCCM Counter did not reach threshold (Counter=%d < 4)!\n", dccm_cnt);
        phase1_pass = 0;
    }
    if (trap_count == 0) {
        printf("  --> ERROR: No DCCM threshold alert trap was triggered (TrapCount=0)!\n");
        phase1_pass = 0;
    }
    if (last_mcause != 0x8000001e) {
        printf("  --> ERROR: Incorrect mcause=0x%08X received (expected 0x8000001E)!\n", last_mcause);
        phase1_pass = 0;
    }

    if (phase1_pass) {
        printf("PASS: DCCM threshold alert verified (Counter=%d, TrapCount=%d)\n", dccm_cnt, trap_count);
    } else {
        printf("FAIL: DCCM threshold alert verification failed (Counter=%d, TrapCount=%d)\n", dccm_cnt, trap_count);
        pass = 0;
    }
    // Clear DCCM threshold & counter so mdccme_ce_req drops to 0 for next phases
    write_mdccmect(0);

    // =================================================================
    // Phase 2: ICCM ECC Threshold Alert Test (miccmect 0x7F1)
    // =================================================================
    printf("\n[Phase 2] Testing ICCM SBE Counter & Threshold Alert (0x7F1)...\n");
    trap_count = 0;
    last_mcause = 0;
    int phase2_pass = 1;

    // Copy all iccm functions from Flash/RAM to ICCM (0xee000000) with error injection active
    uint32_t *iccm_dst = (uint32_t *)ICCM_SADDR;
    uint32_t *iccm_src = (uint32_t *)&iccm_start;

    tohost = INJECT_ICCM_SINGLE_BIT;
    while (iccm_src < (uint32_t *)&iccm_end) {
        *iccm_dst++ = *iccm_src++;
    }
    tohost = DISABLE_ERROR_INJECTION;

    write_miccmect(2 << 27); // Set threshold exponent = 2 (triggers at count >= 2^2 = 4)
    enable_mceie();
    printf("Programmed MICCMECT threshold exponent to 2 (triggers at count >= 4). Initial MICCMECT=0x%08X\n", read_miccmect());

    void (* const iccm_funcs[5])(void) = { iccm_fn_1, iccm_fn_2, iccm_fn_3, iccm_fn_4, iccm_fn_5 };

    for (int i = 1; i <= 5; i++) {
        iccm_funcs[i - 1]();
        uint32_t miccm = read_miccmect();
        uint32_t cnt = miccm & 0x7FFFFFF;
        printf("ICCM Exec %d: MICCMECT=0x%08X (Counter=%d, Traps=%d)\n", i, miccm, cnt, trap_count);

        // Strict Check: Ensure no premature trap fires while count < 4
        if (cnt < 4 && trap_count != 0) {
            printf("  --> ERROR: Premature trap fired at Counter=%d (expected Traps=0)!\n", cnt);
            phase2_pass = 0;
        }
        for (int slp = 0; slp < 10; slp++) asm volatile ("nop");
    }
    disable_mceie();

    uint32_t iccm_cnt = read_miccmect() & 0x7FFFFFF;
    if (iccm_cnt < 4) {
        printf("  --> ERROR: ICCM Counter did not reach threshold (Counter=%d < 4)!\n", iccm_cnt);
        phase2_pass = 0;
    }
    if (trap_count == 0) {
        printf("  --> ERROR: No ICCM threshold alert trap was triggered (TrapCount=0)!\n");
        phase2_pass = 0;
    }
    if (last_mcause != 0x8000001e) {
        printf("  --> ERROR: Incorrect mcause=0x%08X received (expected 0x8000001E)!\n", last_mcause);
        phase2_pass = 0;
    }

    if (phase2_pass) {
        printf("PASS: ICCM threshold alert verified (Counter=%d, TrapCount=%d)\n", iccm_cnt, trap_count);
    } else {
        printf("FAIL: ICCM threshold alert verification failed (Counter=%d, TrapCount=%d)\n", iccm_cnt, trap_count);
        pass = 0;
    }
    // Clear ICCM threshold & counter so miccme_ce_req drops to 0 for next phases
    write_miccmect(0);

    // =================================================================
    // Phase 3: ICache ECC/Parity Threshold Alert Test (micect 0x7F0)
    // =================================================================
    printf("\n[Phase 3] Testing ICache Counter & Threshold Alert (0x7F0)...\n");
    trap_count = 0;
    last_mcause = 0;
    int phase3_pass = 1;

    // Warm up target function into ICache
    icache_target_func();

    write_micect(2 << 27); // Set threshold exponent = 2 (triggers at count >= 2^2 = 4)
    enable_mceie();
    printf("Programmed MICECT threshold exponent to 2 (triggers at count >= 4). Initial MICECT=0x%08X\n", read_micect());

    for (int i = 1; i <= 5; i++) {
        icache_target_func(); // Re-warm before inject to ensure hit
        tohost = CMD_INJECT_ICACHE_SINGLE_BIT;
        icache_target_func(); // Trigger read error and refetch
        uint32_t mice = read_micect();
        uint32_t cnt = mice & 0x7FFFFFF;
        printf("ICache Access %d: MICECT=0x%08X (Counter=%d, Traps=%d)\n", i, mice, cnt, trap_count);

        // Strict Check: Ensure no premature trap fires while count < 4
        if (cnt < 4 && trap_count != 0) {
            printf("  --> ERROR: Premature trap fired at Counter=%d (expected Traps=0)!\n", cnt);
            phase3_pass = 0;
        }
        for (int slp = 0; slp < 10; slp++) asm volatile ("nop");
    }
    disable_mceie();

    uint32_t icache_cnt = read_micect() & 0x7FFFFFF;
    if (icache_cnt < 4) {
        printf("  --> ERROR: ICache Counter did not reach threshold (Counter=%d < 4)!\n", icache_cnt);
        phase3_pass = 0;
    }
    if (trap_count == 0) {
        printf("  --> ERROR: No ICache threshold alert trap was triggered (TrapCount=0)!\n");
        phase3_pass = 0;
    }
    if (last_mcause != 0x8000001e) {
        printf("  --> ERROR: Incorrect mcause=0x%08X received (expected 0x8000001E)!\n", last_mcause);
        phase3_pass = 0;
    }

    if (phase3_pass) {
        printf("PASS: ICache threshold alert verified (Counter=%d, TrapCount=%d)\n", icache_cnt, trap_count);
    } else {
        printf("FAIL: ICache threshold alert verification failed (Counter=%d, TrapCount=%d)\n", icache_cnt, trap_count);
        pass = 0;
    }
    // Clear ICache threshold & counter
    write_micect(0);

    printf("\n=================================================================\n");
    if (pass) {
        printf(" Multi-Memory RAS ECC Threshold Test SUCCEEDED (All 3 Memories Passed)\n");
        printf("=================================================================\n");
        return 0;
    } else {
        printf(" Multi-Memory RAS ECC Threshold Test FAILED!\n");
        printf("=================================================================\n");
        tohost = TEST_FAILED;
        return 1;
    }
}
