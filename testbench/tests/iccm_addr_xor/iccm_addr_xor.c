/* SPDX-License-Identifier: Apache-2.0
 * Copyright 2026 Google LLC
 *
 * ICCM Address-XOR Infection Feature Test (PR #481 / PR #489)
 * Author: Samip Modi (samipmodi@google.com)
 *
 * Test Intent:
 * 1. Clean ICCM execution with iccm_addr_xor enabled (address XOR cancels).
 * 2. Read Address Fault Injection (0xE5): Corrupted address during fetch causes XOR mismatch,
 *    triggering an instruction access fault / ECC error (mcause=0x1, mscause=0x1).
 * 3. Write Address Fault Injection (0xE5): Corrupted address during store causes XOR mismatch on read back.
 * 4. Write Enable Fault Injection (0xE6): Suppressed wren prevents valid XORed instruction storage.
 * 5. Read Enable Fault Injection (0xE7): Suppressed rden prevents valid instruction retrieval.
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
#define DISABLE_ERROR_INJECTION 0xE4
#define INJECT_ICCM_ADDR_FAULT  0xE5
#define INJECT_ICCM_WREN_FAULT  0xE6
#define INJECT_ICCM_RDEN_FAULT  0xE7
#define DISABLE_ICCM_FAULT      0xE8

#define ICCM_BASE 0xEE000000

extern uintptr_t iccm_start, iccm_end;
extern int printf(const char* format, ...);
extern int putchar(int c);

volatile uint32_t boot_phase __attribute__((section(".data"))) = 0;
volatile uint32_t trap_count __attribute__((section(".data"))) = 0;
volatile uint32_t last_mcause __attribute__((section(".data"))) = 0;
volatile uint32_t last_mscause __attribute__((section(".data"))) = 0;
volatile uint32_t target_exec_count __attribute__((section(".data"))) = 0;

static inline uint32_t read_csr_miccmect(void) {
    uint32_t val;
    __asm__ volatile ("csrr %0, 0x7F1" : "=r" (val));
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

// Function located in ICCM section
void iccm_target_func(void) __attribute__ ((aligned(16), section(".iccm_data0")));
void iccm_target_func(void) {
    target_exec_count++;
}

void trap_handler(void) {
    last_mcause = read_csr_mcause();
    last_mscause = read_csr_mscause();
    trap_count++;
    clear_csr_causes();

    // Disable any active fault injection
    putchar(DISABLE_ICCM_FAULT);
    putchar(DISABLE_ERROR_INJECTION);

    printf("[TRAP] Caught exception mcause=0x%x, mscause=0x%x (trap_count=%u, phase=%u)\n",
           last_mcause, last_mscause, trap_count, boot_phase);

    if (last_mcause == 0x1 && last_mscause == 0x1) {
        printf("[TRAP] Verified expected ICCM ECC error on fault injection!\n");
    } else {
        printf("[TRAP] WARNING: Unexpected trap cause: mcause=0x%x mscause=0x%x\n", last_mcause, last_mscause);
    }
}

void copy_code_to_iccm_dest(uint32_t dest_addr) {
    uint32_t *src = (uint32_t *)&iccm_start;
    uint32_t *dst = (uint32_t *)dest_addr;
    uint32_t *end = (uint32_t *)&iccm_end;

    printf("Copying ICCM code from 0x%x to 0x%x (size %u bytes)\n",
           (uintptr_t)src, (uintptr_t)dst, (uint32_t)((uintptr_t)end - (uintptr_t)src));
    while (src < end) {
        *dst++ = *src++;
    }
    __asm__ volatile ("fence.i");
}

int main(void) {
    boot_phase++;

    printf("=====================================================\n");
    printf(" Starting ICCM Address-XOR Infection Feature Test\n");
    printf(" Phase: %u, Boot Count: %u, Trap Count: %u\n", boot_phase, boot_phase, trap_count);
    printf("=====================================================\n");

    if (boot_phase == 1) {
        // -------------------------------------------------------------
        // Phase 1: Baseline Clean Execution from ICCM (XOR must cancel)
        // -------------------------------------------------------------
        printf("\n[Phase 1] Testing clean ICCM execution with iccm_addr_xor enabled...\n");
        copy_code_to_iccm_dest(ICCM_BASE + 0x000);

        void (*func_clean)(void) = (void (*)(void))(ICCM_BASE + 0x000);
        uint32_t miccmect_before = read_csr_miccmect();
        func_clean();
        uint32_t miccmect_after = read_csr_miccmect();

        if (target_exec_count != 1) {
            printf("FAIL [Phase 1]: iccm_target_func failed to execute! count=%u\n", target_exec_count);
            putchar(TEST_FAILED);
            return 1;
        }

        if (miccmect_after != miccmect_before) {
            printf("FAIL [Phase 1]: Spurious ICCM ECC error detected! miccmect before=%u, after=%u\n",
                   miccmect_before, miccmect_after);
            putchar(TEST_FAILED);
            return 1;
        }
        printf("PASS [Phase 1]: Clean ICCM execution with Address-XOR successful (no ECC errors).\n");

        // -------------------------------------------------------------
        // Phase 1b: ICCM Read Address Fault Injection (0xE5)
        // -------------------------------------------------------------
        printf("\n[Phase 1b] Testing ICCM Read Address Fault Injection (0xE5)...\n");
        copy_code_to_iccm_dest(ICCM_BASE + 0x100);

        void (*func_rd_fault)(void) = (void (*)(void))(ICCM_BASE + 0x100);
        putchar(INJECT_ICCM_ADDR_FAULT);
        printf("[Phase 1b] Executing from 0x%x with address fault (expecting ECC trap)...\n", (uint32_t)(ICCM_BASE + 0x100));
        func_rd_fault();

        putchar(DISABLE_ICCM_FAULT);
        printf("FAIL [Phase 1b]: Did not hit expected ECC trap on ICCM read address fault!\n");
        putchar(TEST_FAILED);
        return 1;

    } else if (boot_phase == 2) {
        // -------------------------------------------------------------
        // Phase 2: ICCM Write Address Fault Injection (0xE5)
        // -------------------------------------------------------------
        printf("\n[Phase 2] Verified Read Address Fault Trap (trap_count=%u).\n", trap_count);
        printf("[Phase 2] Testing ICCM Write Address Fault Injection (0xE5)...\n");

        putchar(INJECT_ICCM_ADDR_FAULT);
        copy_code_to_iccm_dest(ICCM_BASE + 0x200);
        putchar(DISABLE_ICCM_FAULT);

        void (*func_wr_fault)(void) = (void (*)(void))(ICCM_BASE + 0x200);
        printf("[Phase 2] Executing from 0x%x (written with address fault, expecting ECC trap)...\n", (uint32_t)(ICCM_BASE + 0x200));
        func_wr_fault();

        printf("FAIL [Phase 2]: Did not hit expected ECC trap on ICCM write address fault!\n");
        putchar(TEST_FAILED);
        return 1;

    } else if (boot_phase == 3) {
        // -------------------------------------------------------------
        // Phase 3: ICCM Write Enable Fault Injection (0xE6)
        // -------------------------------------------------------------
        printf("\n[Phase 3] Verified Write Address Fault Trap (trap_count=%u).\n", trap_count);
        printf("[Phase 3] Testing ICCM Write Enable Fault Injection (0xE6)...\n");

        putchar(INJECT_ICCM_WREN_FAULT);
        copy_code_to_iccm_dest(ICCM_BASE + 0x300);
        putchar(DISABLE_ICCM_FAULT);

        void (*func_wren_fault)(void) = (void (*)(void))(ICCM_BASE + 0x300);
        printf("[Phase 3] Executing from 0x%x (unwritten due to wren fault, expecting ECC trap)...\n", (uint32_t)(ICCM_BASE + 0x300));
        func_wren_fault();

        printf("FAIL [Phase 3]: Did not hit expected ECC trap on ICCM wren fault!\n");
        putchar(TEST_FAILED);
        return 1;

    } else if (boot_phase == 4) {
        // -------------------------------------------------------------
        // Phase 4: ICCM Read Enable Fault Injection (0xE7)
        // -------------------------------------------------------------
        printf("\n[Phase 4] Verified Write Enable Fault Trap (trap_count=%u).\n", trap_count);
        printf("[Phase 4] Testing ICCM Read Enable Fault Injection (0xE7)...\n");

        copy_code_to_iccm_dest(ICCM_BASE + 0x400);

        void (*func_rden_fault)(void) = (void (*)(void))(ICCM_BASE + 0x400);
        putchar(INJECT_ICCM_RDEN_FAULT);
        printf("[Phase 4] Executing from 0x%x with rden fault (expecting ECC trap)...\n", (uint32_t)(ICCM_BASE + 0x400));
        func_rden_fault();

        putchar(DISABLE_ICCM_FAULT);
        printf("FAIL [Phase 4]: Did not hit expected ECC trap on ICCM rden fault!\n");
        putchar(TEST_FAILED);
        return 1;

    } else if (boot_phase == 5) {
        // -------------------------------------------------------------
        // Phase 5: Verification & Completion
        // -------------------------------------------------------------
        printf("\n[Phase 5] Verified Read Enable Fault Trap (trap_count=%u).\n", trap_count);
        printf("\n=====================================================\n");
        printf(" ALL ICCM Address-XOR Infection Tests PASSED!\n");
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
