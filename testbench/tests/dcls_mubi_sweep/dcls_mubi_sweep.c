/* SPDX-License-Identifier: Apache-2.0
 * Copyright 2026 Google LLC
 *
 * Dual-Core Lockstep (DCLS) Multi-Bit Integrity (MUBI) Sweep Test
 * Author: Samip Modi (samipmodi@google.com)
 *
 * Description:
 * This test verifies the functionality, fault tolerance, and tamper resistance of the
 * Dual-Core Lockstep (DCLS) error monitoring and injection mechanisms using Multi-Bit
 * Integrity (MUBI) control signals.
 *
 * MUBI Width Test Strategy:
 * - Small MUBI Widths (width <= 8, e.g., 2, 4, 8 bits):
 *   Exhaustively sweeps all 2^width possible binary values (4, 16, 256 iterations) across
 *   external error injection (CMD_INJ_EXT) and control signal validation (CMD_INJ_CTRL).
 *
 * - Large MUBI Widths (width >= 16, e.g., 16, 32 bits):
 *   To avoid 32-bit shift truncation and simulation execution timeouts (which would require
 *   over 131,000 core resets for 16-bit and 8.5 billion resets for 32-bit), testing is
 *   scaled down to 4 representative MUBI test values:
 *     1. RV_MUBI_FALSE (Valid False encoding)
 *     2. RV_MUBI_TRUE (Valid True encoding)
 *     3. RV_MUBI_FALSE ^ 1 (Corrupted / Invalid MUBI encoding #1)
 *     4. RV_MUBI_TRUE ^ 1 (Corrupted / Invalid MUBI encoding #2)
 *
 * Test Phases:
 * Phase 1: Error Suppression - External Error Injection (Monitoring Disabled)
 *          Sets disable_corruption_detection_i = RV_MUBI_TRUE. Sweeps all possible
 *          external error injection values (CMD_INJ_EXT) and verifies all errors
 *          are masked (0 traps occur).
 *
 * Phase 2: Error Suppression - Core Lockstep Mismatch (Monitoring Disabled)
 *          With disable_corruption_detection_i = RV_MUBI_TRUE, injects a core
 *          lockstep mismatch (CMD_INJ_LOCKSTEP) and verifies the mismatch is masked
 *          (0 traps occur).
 *
 * Phase 3: Normal Monitoring - External Error Injection (Monitoring Enabled)
 *          Re-enables reporting (disable_corruption_detection_i = RV_MUBI_FALSE). Sweeps
 *          all injection values (CMD_INJ_EXT) and verifies exactly 1 value (RV_MUBI_FALSE)
 *          does not trap, while all other values trigger a corruption trap.
 *
 * Phase 4: Disable Control Signal Fault / Encoding Validation
 *          Sweeps all possible multibit patterns on CMD_INJ_CTRL. Verifies that valid
 *          RV_MUBI_TRUE disables reporting, valid RV_MUBI_FALSE enables reporting, and all
 *          invalid/corrupted multibit encodings trigger a tamper/control fault trap.
 *
 * Phase 5: Fail-Secure Tamper Resistance (Corrupted Disable + Fault Injection)
 *          Writes an invalid/corrupted multibit value (dis_inv) to CMD_INJ_CTRL and injects
 *          an external fault (CMD_INJ_EXT = RV_MUBI_TRUE). Verifies that unless CMD_INJ_CTRL
 *          is strictly equal to valid RV_MUBI_TRUE, any tampered disable signal fails secure
 *          and traps immediately upon fault injection.
 *
 * Final Phase: End-of-Test Lockstep Corruption Verification
 *          Masks interrupts and triggers CMD_INJ_LOCKSTEP with normal reporting enabled.
 *          Verifies that corruption_detected_o is asserted (El2MuBiTrue) when simulation
 *          reaches tohost = 0xFE (TEST_PASSED).
 */

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <defines.h>

// ============================================================================

#define read_csr(csr) ({ \
    unsigned long res; \
    asm volatile ("csrr %0, " #csr : "=r"(res)); \
    res; \
})

#define write_csr(csr, val) { \
    asm volatile ("csrw " #csr ", %0" : : "r"(val)); \
}

// ============================================================================

#define CMD_INJ_VEER         0x91
#define CMD_INJ_LOCKSTEP     0x92
#define CMD_INJ_EXT          0x93
#define CMD_INJ_CTRL         0x94
#define CMD_INJ_CLEAR        0x95
#define CMD_RST              0x96

volatile uint32_t test_count __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t trap_count __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t test_completed __attribute__((section(".dccm.persistent"))) = 0;

extern volatile uint32_t tohost;
volatile uint32_t *threshold    = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIPT_OFFSET);
volatile uint32_t *gateway      = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIGWCTRL_OFFSET);
volatile uint32_t *clr_gateway  = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIGWCLR_OFFSET);
volatile uint32_t *priority     = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIPL_OFFSET);
volatile uint32_t *enable       = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIE_OFFSET);

// ============================================================================

void trap_handler () {
    uint32_t mstatus = read_csr(mstatus);
    uint32_t mcause  = read_csr(mcause);
    uint32_t mepc    = read_csr(mepc);

    if (test_completed) {
        tohost = 0xFE;
        while (1);
    }

    tohost = CMD_INJ_CLEAR;
    tohost = RV_MUBI_FALSE << 8 | CMD_INJ_EXT;
    tohost = RV_MUBI_FALSE << 8 | CMD_INJ_CTRL;

    printf("trap! mstatus=0x%08X, mcause=0x%08X, mepc=0x%08X\n", mstatus, mcause, mepc);
    trap_count++;

    tohost = CMD_RST;
}

#if (RV_MUBI_WIDTH >= 16)
#define NUM_MUBI_VALS 4
static const uint32_t mubi_vals[NUM_MUBI_VALS] = {
    RV_MUBI_FALSE,
    RV_MUBI_TRUE,
    RV_MUBI_FALSE ^ 1,
    RV_MUBI_TRUE ^ 1
};
#define GET_MUBI_VAL(i) (mubi_vals[(i)])
#else
#define NUM_MUBI_VALS (1 << RV_MUBI_WIDTH)
#define GET_MUBI_VAL(i) ((uint32_t)(i))
#endif

static uint32_t get_mubi_test_val(uint32_t idx, uint32_t *total_vals) {
    *total_vals = NUM_MUBI_VALS;
    return GET_MUBI_VAL(idx);
}

int main () {
    printf("Hello VeeR\n");
    printf("Test_count: %d, trap_count: %d\n", test_count, trap_count);

    unsigned long mie;
    unsigned long mstatus;

    unsigned long i;
    unsigned long tests_done;
    uint32_t num_vals = 0;
    get_mubi_test_val(0, &num_vals);

    asm volatile (
        "li t0, 0x800\n\t"
        "csrc mie, t0\n\t"
        ::: "t0"
    );

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

    // ========================================================================
    // Phase 1: Error Suppression - External Error Injection (Monitoring Disabled)
    // Purpose: Set disable_corruption_detection_i = RV_MUBI_TRUE and sweep all
    //          external injection values (CMD_INJ_EXT).
    // Expected: All errors are masked; 0 traps should occur.
    // ========================================================================
    printf("Disable reporting!\n");
    tohost = RV_MUBI_TRUE << 8 | CMD_INJ_CTRL;

    if (test_count < num_vals) {
        for (i = test_count; i < num_vals; ++i) {
            test_count++;
            tohost = get_mubi_test_val(i, &num_vals) << 8 | CMD_INJ_EXT;
            for (uint32_t slp = 0; slp < 20; slp++) {
                __asm__ volatile ("nop");
            }
        }

        if (trap_count > 0) {
            tohost = 1;
        }

        tohost = RV_MUBI_FALSE << 8 | CMD_INJ_EXT;
    }
    tests_done = num_vals;

    // ========================================================================
    // Phase 2: Error Suppression - Core Lockstep Mismatch (Monitoring Disabled)
    // Purpose: With disable_corruption_detection_i = RV_MUBI_TRUE, inject a
    //          lockstep error (CMD_INJ_LOCKSTEP).
    // Expected: Core mismatch is masked; 0 traps should occur.
    // ========================================================================
    if (test_count == tests_done) {
        test_count++;
        tohost = 5 << 8 | CMD_INJ_LOCKSTEP;
        for (volatile int slp = 0; slp < 20; slp++) {
            __asm__ volatile ("nop");
        }

        if (trap_count > 0) {
            tohost = 1;
        } else {
            // Reset cores to guarantee clean synchronization for subsequent phases
            tohost = CMD_INJ_CLEAR;
            tohost = CMD_RST;
        }
    }
    tests_done += 1;

    // ========================================================================
    // Phase 3: Normal Monitoring - External Error Injection (Monitoring Enabled)
    // Purpose: Re-enable reporting (disable_corruption_detection_i = RV_MUBI_FALSE)
    //          and sweep all external injection values (CMD_INJ_EXT).
    // Expected: Exactly 1 value (RV_MUBI_FALSE) does not trap; all non-false
    //          values trigger a corruption trap (num_vals - 1 traps total).
    // ========================================================================
    printf("Re-enable reporting!\n");
    tohost = RV_MUBI_FALSE << 8 | CMD_INJ_CTRL;

    if (test_count - tests_done < num_vals) {
        for (i = test_count - tests_done; i < num_vals; ++i) {
            test_count++;
            tohost = get_mubi_test_val(i, &num_vals) << 8 | CMD_INJ_EXT;
            for (uint32_t slp = 0; slp < 20; slp++) {
                __asm__ volatile ("nop");
            }
        }
    }
    if (test_count - tests_done == num_vals && trap_count != num_vals - 1) {
        tohost = 1;
    } else if (test_count - tests_done == num_vals) {
        printf("Clearing test_count\n");
        trap_count = 0;
    }
    tests_done += num_vals;

    // ========================================================================
    // Phase 4: Disable Control Signal Fault / Encoding Validation
    // Purpose: Sweep all multibit patterns on CMD_INJ_CTRL.
    // Expected: Valid RV_MUBI_TRUE disables reporting, valid RV_MUBI_FALSE
    //          enables reporting, and all invalid MUBI encodings trigger a
    //          tamper/control fault trap (num_vals - 2 traps total).
    // ========================================================================
    if (test_count - tests_done < num_vals) {
        for (i = test_count - tests_done; i < num_vals; ++i) {
            test_count++;
            tohost = get_mubi_test_val(i, &num_vals) << 8 | CMD_INJ_CTRL;
            for (uint32_t slp = 0; slp < 20; slp++) {
                __asm__ volatile ("nop");
            }
        }
    }
    if (test_count - tests_done == num_vals && trap_count != num_vals - 2) {
        tohost = 1;
    } else if (test_count - tests_done == num_vals) {
        printf("Clearing test_count\n");
        trap_count = 0;
    }
    tests_done += num_vals;

    // ========================================================================
    // Phase 5: Fail-Secure Tamper Resistance (Corrupted Disable + Error Injection)
    // Purpose: Write an invalid/tampered MUBI value (dis_inv = RV_MUBI_TRUE ^ 1)
    //          to CMD_INJ_CTRL, then inject external fault (CMD_INJ_EXT = RV_MUBI_TRUE).
    // Expected: Hardware fails secure and immediately traps because disable
    //          control signal is not strictly valid RV_MUBI_TRUE.
    // ========================================================================
    if (test_count == tests_done) {
        printf("Testing SW Inject + DIS Tamper...\n");
        test_count++;
        uint32_t dis_inv = RV_MUBI_TRUE ^ 1;
        tohost = dis_inv << 8 | CMD_INJ_CTRL;
        tohost = RV_MUBI_TRUE << 8 | CMD_INJ_EXT;
        for (volatile int slp = 0; slp < 500; slp++) asm volatile("nop");
    }
    if (test_count == tests_done + 1 && trap_count != 1) {
        printf("FAIL: SW Inject + DIS Tamper did not trap!\n");
        tohost = 1;
    } else if (test_count == tests_done + 1) {
        printf("PASS: SW Inject + DIS Tamper trapped as expected!\n");
        trap_count = 0;
        tohost = CMD_INJ_CLEAR;
    }
    tests_done += 1;

    // ========================================================================
    // Final Phase: End-of-Test Lockstep Corruption Verification
    // Purpose: Mask interrupts and trigger CMD_INJ_LOCKSTEP with normal reporting.
    // Expected: Testbench top-level monitors corruption_detected_o == El2MuBiTrue
    //          and asserts TEST_PASSED upon tohost = 0xFE.
    // ========================================================================
    asm volatile (
        "li t0, 0x800\n\t"
        "csrc mie, t0\n\t"
        "li t0, 0x8\n\t"
        "csrc mstatus, t0\n\t"
        ::: "t0"
    );

    test_completed = 1;

    tohost = 1 << 8 | CMD_INJ_LOCKSTEP;
    for (volatile int slp = 0; slp < 100; slp++) {
        __asm__ volatile ("nop");
    }
    return 0;
}
