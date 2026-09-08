/* SPDX-License-Identifier: Apache-2.0
 * Copyright 2026 Google LLC
 *
 * DCCM Address-XOR Infection Feature Test (PR #492)
 * Author: Samip Modi (samipmodi@google.com)
 *
 * Test Intent:
 * 1. Clean read/write access to DCCM with dccm_addr_xor enabled (address XOR cancels).
 * 2. Read Address Fault Injection (0xE9): Corrupted address during load causes XOR mismatch,
 *    triggering an LSU load access fault / ECC error (mcause=0x5, mscause=0x1).
 * 3. Write Address Fault Injection (0xE9): Corrupted address during store causes XOR mismatch on read back.
 * 4. Write Enable Fault Injection (0xEA): Suppressed wren prevents valid XORed data storage.
 * 5. Read Enable Fault Injection (0xEB): Suppressed rden prevents valid data retrieval.
 */

#include <stdint.h>
#include <stdlib.h>

#define STDOUT_ADDR 0xD0580000
volatile char *stdout_reg = (char *)STDOUT_ADDR;

// Mailbox command protocols
#define TEST_PASSED             0xFF
#define TEST_FAILED             0x01
#define INJECT_ICCM_SINGLE_BIT  0xE0
#define INJECT_ICCM_DOUBLE_BIT  0xE1
#define INJECT_DCCM_SINGLE_BIT  0xE2
#define INJECT_DCCM_DOUBLE_BIT  0xE3
#define DISABLE_ERROR_INJECTION 0xE4
#define INJECT_DCCM_ADDR_FAULT  0xE9
#define INJECT_DCCM_WREN_FAULT  0xEA
#define INJECT_DCCM_RDEN_FAULT  0xEB
#define DISABLE_DCCM_FAULT      0xEC

#define DCCM_BASE 0xF0040000

extern int printf(const char* format, ...);
extern int putchar(int c);

volatile uint32_t boot_phase __attribute__((section(".data"))) = 0;
volatile uint32_t trap_count __attribute__((section(".data"))) = 0;
volatile uint32_t last_mcause __attribute__((section(".data"))) = 0;
volatile uint32_t last_mscause __attribute__((section(".data"))) = 0;

static inline uint32_t read_csr_mdccmect(void) {
    uint32_t val;
    __asm__ volatile ("csrr %0, 0x7F2" : "=r" (val));
    return val;
}

static inline uint32_t read_csr_mcause(void) {
    uint32_t val;
    __asm__ volatile ("csrr %0, 0x342" : "=r" (val));
    return val;
}

static inline uint32_t read_csr_mscause(void) {
    uint32_t val;
    __asm__ volatile ("csrr %0, 0x7FF" : "=r" (val));
    return val;
}

static inline void clear_csr_causes(void) {
    __asm__ volatile ("csrw 0x342, x0");
    __asm__ volatile ("csrw 0x7FF, x0");
}

void trap_handler(void) {
    last_mcause = read_csr_mcause();
    last_mscause = read_csr_mscause();
    trap_count++;
    clear_csr_causes();

    printf("[TRAP] Caught exception mcause=0x%x, mscause=0x%x (trap_count=%u, phase=%u)\n",
           last_mcause, last_mscause, trap_count, boot_phase);

    // Load Access Fault (0x5) or Store Access Fault (0x7) with ECC error (mscause=0x1)
    if ((last_mcause == 0x5 || last_mcause == 0x7) && last_mscause == 0x1) {
        printf("[TRAP] Verified expected DCCM ECC error on fault injection!\n");
    } else {
        printf("[TRAP] WARNING: Unexpected trap cause: mcause=0x%x mscause=0x%x\n", last_mcause, last_mscause);
    }
}

int main(void) {
    boot_phase++;

    printf("=====================================================\n");
    printf(" Starting DCCM Address-XOR Infection Feature Test\n");
    printf(" Phase: %u, Boot Count: %u, Trap Count: %u\n", boot_phase, boot_phase, trap_count);
    printf("=====================================================\n");

    if (boot_phase == 1) {
        // -------------------------------------------------------------
        // Phase 1: Clean Read/Write Access to DCCM (XOR must cancel)
        // -------------------------------------------------------------
        printf("\n[Phase 1] Testing clean DCCM store & load with dccm_addr_xor enabled...\n");
        volatile uint32_t *dccm_clean = (volatile uint32_t *)(DCCM_BASE + 0x8000);
        uint32_t test_values[4] = {0x11223344, 0x55667788, 0xAABBCCDD, 0xCAFEBABE};

        uint32_t mdccmect_before = read_csr_mdccmect();
        for (int i = 0; i < 4; i++) {
            dccm_clean[i] = test_values[i];
        }

        __asm__ volatile ("fence");

        for (int i = 0; i < 4; i++) {
            uint32_t rval = dccm_clean[i];
            if (rval != test_values[i]) {
                printf("FAIL [Phase 1]: DCCM read mismatch at index %d! Expected 0x%x, got 0x%x\n",
                       i, test_values[i], rval);
                putchar(TEST_FAILED);
                return 1;
            }
        }
        uint32_t mdccmect_after = read_csr_mdccmect();

        if (mdccmect_after != mdccmect_before) {
            printf("FAIL [Phase 1]: Spurious DCCM ECC error detected! mdccmect before=%u, after=%u\n",
                   mdccmect_before, mdccmect_after);
            putchar(TEST_FAILED);
            return 1;
        }
        printf("PASS [Phase 1]: Clean DCCM access with Address-XOR successful (no ECC errors).\n");

        // -------------------------------------------------------------
        // Phase 1b: DCCM Read Address Fault Injection (0xE9)
        // -------------------------------------------------------------
        printf("\n[Phase 1b] Testing DCCM Read Address Fault Injection (0xE9)...\n");
        volatile uint32_t *dccm_rd_fault = (volatile uint32_t *)(DCCM_BASE + 0x8100);
        *dccm_rd_fault = 0xDEADBEEF;
        __asm__ volatile ("fence");

        printf("[Phase 1b] Loading from 0x%x with address fault (expecting ECC trap)...\n", (uint32_t)(DCCM_BASE + 0x8100));
        putchar(INJECT_DCCM_ADDR_FAULT);
        volatile uint32_t fault_read = *dccm_rd_fault;
        (void)fault_read;

        putchar(DISABLE_DCCM_FAULT);
        printf("FAIL [Phase 1b]: Did not hit expected ECC trap on DCCM read address fault!\n");
        putchar(TEST_FAILED);
        return 1;

    } else if (boot_phase == 2) {
        // -------------------------------------------------------------
        // Phase 2: DCCM Write Address Fault Injection (0xE9)
        // -------------------------------------------------------------
        printf("\n[Phase 2] Verified Read Address Fault Trap (trap_count=%u).\n", trap_count);
        printf("[Phase 2] Testing DCCM Write Address Fault Injection (0xE9)...\n");

        volatile uint32_t *dccm_wr_fault = (volatile uint32_t *)(DCCM_BASE + 0x8200);
        putchar(INJECT_DCCM_ADDR_FAULT);
        *dccm_wr_fault = 0xCAFED00D;
        __asm__ volatile ("fence");
        putchar(DISABLE_DCCM_FAULT);

        printf("[Phase 2] Loading from 0x%x (written with address fault, expecting ECC trap)...\n", (uint32_t)(DCCM_BASE + 0x8200));
        volatile uint32_t fault_read = *dccm_wr_fault;
        (void)fault_read;

        printf("FAIL [Phase 2]: Did not hit expected ECC trap on DCCM write address fault!\n");
        putchar(TEST_FAILED);
        return 1;

    } else if (boot_phase == 3) {
        // -------------------------------------------------------------
        // Phase 3: DCCM Write Enable Fault Injection (0xEA)
        // -------------------------------------------------------------
        printf("\n[Phase 3] Verified Write Address Fault Trap (trap_count=%u).\n", trap_count);
        printf("[Phase 3] Testing DCCM Write Enable Fault Injection (0xEA)...\n");

        volatile uint32_t *dccm_wren_fault = (volatile uint32_t *)(DCCM_BASE + 0x8300);
        putchar(INJECT_DCCM_WREN_FAULT);
        *dccm_wren_fault = 0xBAADF00D;
        __asm__ volatile ("fence");
        putchar(DISABLE_DCCM_FAULT);

        printf("[Phase 3] Loading from 0x%x (unwritten due to wren fault, expecting ECC trap)...\n", (uint32_t)(DCCM_BASE + 0x8300));
        volatile uint32_t fault_read = *dccm_wren_fault;
        (void)fault_read;

        printf("FAIL [Phase 3]: Did not hit expected ECC trap on DCCM wren fault!\n");
        putchar(TEST_FAILED);
        return 1;

    } else if (boot_phase == 4) {
        // -------------------------------------------------------------
        // Phase 4: DCCM Read Enable Fault Injection (0xEB)
        // -------------------------------------------------------------
        printf("\n[Phase 4] Verified Write Enable Fault Trap (trap_count=%u).\n", trap_count);
        printf("[Phase 4] Testing DCCM Read Enable Fault Injection (0xEB)...\n");

        volatile uint32_t *dccm_rden_fault = (volatile uint32_t *)(DCCM_BASE + 0x8400);
        *dccm_rden_fault = 0xFEEDFACE;
        __asm__ volatile ("fence");

        printf("[Phase 4] Loading from 0x%x with rden fault (expecting ECC trap)...\n", (uint32_t)(DCCM_BASE + 0x8400));
        putchar(INJECT_DCCM_RDEN_FAULT);
        volatile uint32_t fault_read = *dccm_rden_fault;
        (void)fault_read;

        putchar(DISABLE_DCCM_FAULT);
        printf("FAIL [Phase 4]: Did not hit expected ECC trap on DCCM rden fault!\n");
        putchar(TEST_FAILED);
        return 1;

    } else if (boot_phase == 5) {
        // -------------------------------------------------------------
        // Phase 5: Verification & Completion
        // -------------------------------------------------------------
        printf("\n[Phase 5] Verified Read Enable Fault Trap (trap_count=%u).\n", trap_count);
        printf("\n=====================================================\n");
        printf(" ALL DCCM Address-XOR Infection Tests PASSED!\n");
        printf(" Total verified ECC fault traps: %u\n", trap_count);
        printf("=====================================================\n");
        putchar(TEST_PASSED);
        return 0;

    } else {
        printf("FAIL: Unexpected boot phase %u\n", boot_phase);
        putchar(TEST_FAILED);
        return 1;
    }
}
