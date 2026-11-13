/* SPDX-License-Identifier: Apache-2.0
 * Copyright 2026 Google LLC
 *
 * DCCM Address-XOR Infection Feature Test
 * Author: Samip Modi (samipmodi@google.com)
 *
 * Description:
 * Validates the DCCM Address-XOR infection security feature across clean aligned,
 * unaligned dual-bank, and sub-word accesses, single-bit ECC correction with
 * hardware scrub writeback, and SRAM address/control fault injections.
 *
 * Test Phases:
 * 1. Phase 1a: Clean word-aligned 32-bit read/write access to DCCM (_lo XOR lane).
 *    Phase 1b: Clean unaligned dual-bank 32-bit (_lo + _hi XOR lanes) and sub-word
 *              (halfword/byte read-modify-write) DCCM accesses.
 *    Phase 1c: Single-bit ECC error injection (0xE2) and hardware scrub writeback
 *              verification across even/odd words (_lo scrub path) and unaligned
 *              dual-bank loads (_hi scrub path).
 *    Phase 1d: Read Address Fault Injection (0xE9) -> load ECC trap (mcause=0x5, mscause=0x1).
 * 2. Phase 2:  Write Address Fault Injection (0xE9) -> load ECC trap on read-back.
 * 3. Phase 3:  Write Enable Fault Injection (0xEA) -> load ECC trap on read-back.
 * 4. Phase 4:  Access (ME/clken) Fault Injection (0xEB) -> load ECC trap.
 * 5. Phase 5:  Verification and completion (4 expected traps).
 */

#include <stdint.h>
#include <stdlib.h>
#include "defines.h"

// Hardware Configuration Requirement:
// Requires RV_DCCM_ADDR_XOR=1 in the hardware build (-set dccm_addr_xor=1).
// When enabled in veer.config, RV_DCCM_ADDR_XOR is emitted to defines.h.
#if !defined(RV_DCCM_ADDR_XOR) || (RV_DCCM_ADDR_XOR != 1)
#error "Configuration Mismatch: RV_DCCM_ADDR_XOR is not set to 1! Hardware DCCM address-XOR infection must be enabled (-set dccm_addr_xor=1)."
#endif

#define STDOUT_ADDR 0xD0580000
volatile char *stdout_reg = (char *)STDOUT_ADDR;

// Mailbox command protocols
#define TEST_PASSED              0xFF
#define TEST_FAILED              0x01
#define INJECT_ICCM_SINGLE_BIT   0xE0
#define INJECT_ICCM_DOUBLE_BIT   0xE1
#define INJECT_DCCM_SINGLE_BIT   0xE2
#define INJECT_DCCM_DOUBLE_BIT   0xE3
#define DISABLE_ERROR_INJECTION  0xE4
#define INJECT_DCCM_ADDR_FAULT   0xE9
#define INJECT_DCCM_WREN_FAULT   0xEA
#define INJECT_DCCM_ACCESS_FAULT 0xEB
#define DISABLE_DCCM_FAULT       0xEC
#define DISABLE_ICCM_FAULT       0xE8

#define DCCM_BASE 0xF0040000

extern int printf(const char *format, ...);
extern int putchar(int c);

volatile uint32_t boot_phase __attribute__((section(".data"))) = 0;
volatile uint32_t trap_count __attribute__((section(".data"))) = 0;
volatile uint32_t expect_trap __attribute__((section(".data"))) = 0;
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

static inline void unaligned_sw(uintptr_t addr, uint32_t val) {
    __asm__ volatile ("sw %1, 0(%0)" :: "r" (addr), "r" (val) : "memory");
}

static inline uint32_t unaligned_lw(uintptr_t addr) {
    uint32_t val;
    __asm__ volatile ("lw %0, 0(%1)" : "=r" (val) : "r" (addr) : "memory");
    return val;
}

void trap_handler(void) {
    last_mcause = read_csr_mcause();
    last_mscause = read_csr_mscause();
    trap_count++;
    clear_csr_causes();

    // Redundant explicit disable (also performed proactively by crt0.s)
    putchar(DISABLE_DCCM_FAULT);
    putchar(DISABLE_ICCM_FAULT);
    putchar(DISABLE_ERROR_INJECTION);
    __asm__ volatile ("fence");

    printf("[TRAP] Caught exception mcause=0x%x, mscause=0x%x (trap_count=%u, phase=%u)\n",
           last_mcause, last_mscause, trap_count, boot_phase);

    if (!expect_trap) {
        printf("[TRAP] FAIL: Unexpected trap while expect_trap=0! (mcause=0x%x, mscause=0x%x)\n",
               last_mcause, last_mscause);
        putchar(TEST_FAILED);
    }
    expect_trap = 0;

    // Load Access Fault (0x5) or Store Access Fault (0x7) with ECC error (mscause=0x1)
    if ((last_mcause == 0x5 || last_mcause == 0x7) && last_mscause == 0x1) {
        printf("[TRAP] Verified expected DCCM ECC error on fault injection!\n");
    } else {
        printf("[TRAP] FAIL: Unexpected trap cause: mcause=0x%x mscause=0x%x\n", last_mcause, last_mscause);
        putchar(TEST_FAILED);
    }
}

int main(void) {
    boot_phase++;
    expect_trap = 0;

    printf("=====================================================\n");
    printf(" Starting DCCM Address-XOR Infection Feature Test\n");
    printf(" Phase: %u, Boot Count: %u, Trap Count: %u\n", boot_phase, boot_phase, trap_count);
    printf("=====================================================\n");

    if (boot_phase == 1) {
        // -------------------------------------------------------------
        // Phase 1a: Clean Aligned Read/Write Access to DCCM (_lo lane)
        // -------------------------------------------------------------
        printf("\n[Phase 1a] Testing clean aligned DCCM store & load with dccm_addr_xor enabled...\n");
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
                printf("FAIL [Phase 1a]: DCCM read mismatch at index %d! Expected 0x%x, got 0x%x\n",
                       i, test_values[i], rval);
                putchar(TEST_FAILED);
                return 1;
            }
        }
        uint32_t mdccmect_after = read_csr_mdccmect();

        if (mdccmect_after != mdccmect_before) {
            printf("FAIL [Phase 1a]: Spurious DCCM ECC error detected! mdccmect before=%u, after=%u\n",
                   mdccmect_before, mdccmect_after);
            putchar(TEST_FAILED);
            return 1;
        }
        printf("PASS [Phase 1a]: Clean aligned DCCM access successful.\n");

        // -------------------------------------------------------------
        // Phase 1b: Clean Unaligned Dual-Bank (_lo + _hi lanes) & Sub-Word Access
        // -------------------------------------------------------------
        printf("\n[Phase 1b] Testing unaligned dual-bank (sw/lw) & sub-word (sh/sb/lh/lb) DCCM accesses...\n");
        uintptr_t unaligned_base = DCCM_BASE + 0x8020;
        volatile uint32_t *w_ptr = (volatile uint32_t *)unaligned_base;
        volatile uint16_t *h_ptr = (volatile uint16_t *)unaligned_base;
        volatile uint8_t *b_ptr = (volatile uint8_t *)unaligned_base;

        w_ptr[0] = 0x01020304;
        w_ptr[1] = 0x05060708;
        w_ptr[2] = 0x090A0B0C;
        __asm__ volatile ("fence");

        // Unaligned 32-bit store across Bank 0 (_lo) and Bank 1 (_hi) at offset +2
        unaligned_sw(unaligned_base + 2, 0xA1B2C3D4);
        // Unaligned 32-bit store across Bank 1 (_lo) and Bank 2 (_hi) at offset +6
        unaligned_sw(unaligned_base + 6, 0xE5F61234);
        __asm__ volatile ("fence");

        uint32_t uval0 = unaligned_lw(unaligned_base + 2);
        uint32_t uval1 = unaligned_lw(unaligned_base + 6);
        if (uval0 != 0xA1B2C3D4 || uval1 != 0xE5F61234) {
            printf("FAIL [Phase 1b]: Unaligned lw mismatch! uval0=0x%x (exp 0xa1b2c3d4), uval1=0x%x (exp 0xe5f61234)\n",
                   uval0, uval1);
            putchar(TEST_FAILED);
            return 1;
        }

        // Verify the underlying aligned words reflect the unaligned stores
        if (w_ptr[0] != 0xC3D40304 || w_ptr[1] != 0x1234A1B2 || w_ptr[2] != 0x090AE5F6) {
            printf("FAIL [Phase 1b]: Aligned word check after unaligned sw failed! w0=0x%x, w1=0x%x, w2=0x%x\n",
                   w_ptr[0], w_ptr[1], w_ptr[2]);
            putchar(TEST_FAILED);
            return 1;
        }

        // Sub-word halfword and byte stores (exercising internal DCCM read-deXOR-modify-reXOR-write)
        h_ptr[0] = 0xBEEF;
        b_ptr[11] = 0x99;
        __asm__ volatile ("fence");

        if (h_ptr[0] != 0xBEEF || b_ptr[11] != 0x99 || w_ptr[0] != 0xC3D4BEEF || w_ptr[2] != 0x990AE5F6) {
            printf("FAIL [Phase 1b]: Sub-word sh/sb check failed! w0=0x%x, w2=0x%x\n",
                   w_ptr[0], w_ptr[2]);
            putchar(TEST_FAILED);
            return 1;
        }

        mdccmect_after = read_csr_mdccmect();
        if (mdccmect_after != mdccmect_before) {
            printf("FAIL [Phase 1b]: Spurious DCCM ECC error during unaligned/sub-word accesses! mdccmect=%u\n",
                   mdccmect_after);
            putchar(TEST_FAILED);
            return 1;
        }
        printf("PASS [Phase 1b]: Unaligned dual-bank & sub-word DCCM accesses successful.\n");

        // -------------------------------------------------------------
        // Phase 1c: Single-Bit ECC Correction & Hardware Scrub Writeback (0xE2)
        // -------------------------------------------------------------
        printf("\n[Phase 1c] Testing DCCM single-bit ECC correction & scrub writeback (0xE2)...\n");
        volatile uint32_t *dccm_sec = (volatile uint32_t *)(DCCM_BASE + 0x8040);
        uint32_t sec_patterns[2] = {0x13572468, 0x24681357};

        // Test aligned single-bit ECC correction and scrub writeback on even (word 0) and odd (word 1) banks
        for (int i = 0; i < 2; i++) {
            uint32_t ect_pre = read_csr_mdccmect();

            putchar(INJECT_DCCM_SINGLE_BIT);
            __asm__ volatile ("fence");
            dccm_sec[i] = sec_patterns[i];
            __asm__ volatile ("fence");
            putchar(DISABLE_ERROR_INJECTION);
            __asm__ volatile ("fence");

            // 1st read: must correct the 1-bit error, increment mdccmect, and scrub DCCM SRAM
            uint32_t r1 = dccm_sec[i];
            __asm__ volatile ("fence");
            uint32_t ect_mid = read_csr_mdccmect();

            if (r1 != sec_patterns[i] || ect_mid == ect_pre) {
                printf("FAIL [Phase 1c]: Word %d 1st read failed! r1=0x%x (exp 0x%x), ect %u -> %u\n",
                       i, r1, sec_patterns[i], ect_pre, ect_mid);
                putchar(TEST_FAILED);
                return 1;
            }

            // 2nd read: served from scrubbed DCCM SRAM; must match data with NO new ECC error
            uint32_t r2 = dccm_sec[i];
            __asm__ volatile ("fence");
            uint32_t ect_post = read_csr_mdccmect();

            if (r2 != sec_patterns[i] || ect_post != ect_mid) {
                printf("FAIL [Phase 1c]: Word %d post-scrub 2nd read failed! r2=0x%x (exp 0x%x), ect %u -> %u\n",
                       i, r2, sec_patterns[i], ect_mid, ect_post);
                putchar(TEST_FAILED);
                return 1;
            }
        }

        // Test unaligned dual-bank load encountering a 1-bit ECC error on the _hi bank
        // (exercises ld_single_ecc_error_hi_r_ff and dccm_wr_infect_hi during scrub writeback)
        dccm_sec[2] = 0xAAAA1111; // Clean lower word (offset +8)
        __asm__ volatile ("fence");

        uint32_t ect_hi_pre = read_csr_mdccmect();
        putchar(INJECT_DCCM_SINGLE_BIT);
        __asm__ volatile ("fence");
        dccm_sec[3] = 0x2222BBBB; // Corrupted upper word (offset +12)
        __asm__ volatile ("fence");
        putchar(DISABLE_ERROR_INJECTION);
        __asm__ volatile ("fence");

        // Unaligned load at offset +10 straddles dccm_sec[2] (_lo) and dccm_sec[3] (_hi)
        uint32_t u_r1 = unaligned_lw((uintptr_t)&dccm_sec[2] + 2);
        __asm__ volatile ("fence");
        uint32_t ect_hi_mid = read_csr_mdccmect();

        if (u_r1 != 0xBBBBAAAA || ect_hi_mid == ect_hi_pre) {
            printf("FAIL [Phase 1c]: Unaligned _hi bank 1st read failed! u_r1=0x%x (exp 0xbbbbaaaa), ect %u -> %u\n",
                   u_r1, ect_hi_pre, ect_hi_mid);
            putchar(TEST_FAILED);
            return 1;
        }

        // Re-read both unaligned and aligned upper word to confirm _hi bank scrub writeback succeeded
        uint32_t u_r2 = unaligned_lw((uintptr_t)&dccm_sec[2] + 2);
        uint32_t hi_r2 = dccm_sec[3];
        __asm__ volatile ("fence");
        uint32_t ect_hi_post = read_csr_mdccmect();

        if (u_r2 != 0xBBBBAAAA || hi_r2 != 0x2222BBBB || ect_hi_post != ect_hi_mid) {
            printf("FAIL [Phase 1c]: Unaligned _hi bank post-scrub read failed! u_r2=0x%x, hi_r2=0x%x, ect %u -> %u\n",
                   u_r2, hi_r2, ect_hi_mid, ect_hi_post);
            putchar(TEST_FAILED);
            return 1;
        }
        printf("PASS [Phase 1c]: DCCM single-bit ECC correction & scrub writeback (_lo and _hi lanes) successful.\n");

        // -------------------------------------------------------------
        // Phase 1d: DCCM Read Address Fault Injection (0xE9)
        // -------------------------------------------------------------
        printf("\n[Phase 1d] Testing DCCM Read Address Fault Injection (0xE9)...\n");
        volatile uint32_t *dccm_rd_fault = (volatile uint32_t *)(DCCM_BASE + 0x8100);
        *dccm_rd_fault = 0xDEADBEEF;
        __asm__ volatile ("fence");

        printf("[Phase 1d] Loading from 0x%x with address fault (expecting ECC trap)...\n", (uint32_t)(DCCM_BASE + 0x8100));
        expect_trap = 1;
        putchar(INJECT_DCCM_ADDR_FAULT);
        __asm__ volatile ("fence");
        volatile uint32_t fault_read = *dccm_rd_fault;
        (void)fault_read;

        putchar(DISABLE_DCCM_FAULT);
        __asm__ volatile ("fence");
        printf("FAIL [Phase 1d]: Did not hit expected ECC trap on DCCM read address fault!\n");
        putchar(TEST_FAILED);
        return 1;

    } else if (boot_phase == 2) {
        // -------------------------------------------------------------
        // Phase 2: DCCM Write Address Fault Injection (0xE9)
        // -------------------------------------------------------------
        printf("\n[Phase 2] Verified Read Address Fault Trap (trap_count=%u).\n", trap_count);
        if (trap_count != 1) {
            printf("FAIL [Phase 2]: Expected trap_count=1, got %u\n", trap_count);
            putchar(TEST_FAILED);
            return 1;
        }
        printf("[Phase 2] Testing DCCM Write Address Fault Injection (0xE9)...\n");

        volatile uint32_t *dccm_wr_fault = (volatile uint32_t *)(DCCM_BASE + 0x8200);
        putchar(INJECT_DCCM_ADDR_FAULT);
        __asm__ volatile ("fence");
        *dccm_wr_fault = 0xCAFED00D;
        __asm__ volatile ("fence");
        putchar(DISABLE_DCCM_FAULT);
        __asm__ volatile ("fence");

        printf("[Phase 2] Loading from 0x%x (written with address fault, expecting ECC trap)...\n", (uint32_t)(DCCM_BASE + 0x8200));
        expect_trap = 1;
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
        if (trap_count != 2) {
            printf("FAIL [Phase 3]: Expected trap_count=2, got %u\n", trap_count);
            putchar(TEST_FAILED);
            return 1;
        }
        printf("[Phase 3] Testing DCCM Write Enable Fault Injection (0xEA)...\n");

        volatile uint32_t *dccm_wren_fault = (volatile uint32_t *)(DCCM_BASE + 0x8300);
        putchar(INJECT_DCCM_WREN_FAULT);
        __asm__ volatile ("fence");
        *dccm_wren_fault = 0xBAADF00D;
        __asm__ volatile ("fence");
        putchar(DISABLE_DCCM_FAULT);
        __asm__ volatile ("fence");

        printf("[Phase 3] Loading from 0x%x (unwritten due to wren fault, expecting ECC trap)...\n", (uint32_t)(DCCM_BASE + 0x8300));
        expect_trap = 1;
        volatile uint32_t fault_read = *dccm_wren_fault;
        (void)fault_read;

        printf("FAIL [Phase 3]: Did not hit expected ECC trap on DCCM wren fault!\n");
        putchar(TEST_FAILED);
        return 1;

    } else if (boot_phase == 4) {
        // -------------------------------------------------------------
        // Phase 4: DCCM Access (ME/clken) Fault Injection (0xEB)
        // -------------------------------------------------------------
        printf("\n[Phase 4] Verified Write Enable Fault Trap (trap_count=%u).\n", trap_count);
        if (trap_count != 3) {
            printf("FAIL [Phase 4]: Expected trap_count=3, got %u\n", trap_count);
            putchar(TEST_FAILED);
            return 1;
        }
        printf("[Phase 4] Testing DCCM Access (ME/clken) Fault Injection (0xEB)...\n");

        volatile uint32_t *dccm_access_fault = (volatile uint32_t *)(DCCM_BASE + 0x8400);
        *dccm_access_fault = 0xFEEDFACE;
        __asm__ volatile ("fence");

        printf("[Phase 4] Loading from 0x%x with access fault (expecting ECC trap)...\n", (uint32_t)(DCCM_BASE + 0x8400));
        expect_trap = 1;
        putchar(INJECT_DCCM_ACCESS_FAULT);
        __asm__ volatile ("fence");
        volatile uint32_t fault_read = *dccm_access_fault;
        (void)fault_read;

        putchar(DISABLE_DCCM_FAULT);
        __asm__ volatile ("fence");
        printf("FAIL [Phase 4]: Did not hit expected ECC trap on DCCM access fault!\n");
        putchar(TEST_FAILED);
        return 1;

    } else if (boot_phase == 5) {
        // -------------------------------------------------------------
        // Phase 5: Verification & Completion
        // -------------------------------------------------------------
        printf("\n[Phase 5] Verified Access (ME/clken) Fault Trap (trap_count=%u).\n", trap_count);
        if (trap_count != 4) {
            printf("FAIL [Phase 5]: Expected trap_count=4, got %u\n", trap_count);
            putchar(TEST_FAILED);
            return 1;
        }
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
