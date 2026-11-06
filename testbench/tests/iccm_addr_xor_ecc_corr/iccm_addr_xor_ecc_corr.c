/* SPDX-License-Identifier: Apache-2.0
 *
 * ICCM Address-XOR + single-bit ECC correction test.
 *
 * Checks that single-bit ECC errors on instruction fetches from the ICCM are
 * corrected transparently while the ICCM address-XOR infection
 * (RV_ICCM_ADDR_XOR) is enabled. A corrected word is written back to the ICCM
 * and to a redundant row in el2_ifu_iccm_mem.sv; later fetches of that word
 * are served from the redundant row, so both copies must hold the word folded
 * with its own address. Errors are placed on both an odd and an even word,
 * because the XOR mask differs between the two words of a 64-bit ICCM row.
 *
 * Test intent:
 *   Phase 1: clean execution of the ICCM kernel, no ECC events.
 *   Phase 2: single-bit error on an ODD word (0xEE000004). The first run must
 *            correct the error (miccmect increments) and return the right
 *            value. The re-run is served from the redundant row and must
 *            return the right value with no further ECC event.
 *   Phase 3: the same for an EVEN word (0xEE000008).
 *
 * Any trap fails the test.
 */

#include <stdint.h>
#include "defines.h"

#if !defined(RV_ICCM_ADDR_XOR) || (RV_ICCM_ADDR_XOR != 1)
#error "Requires RV_ICCM_ADDR_XOR=1 (-set iccm_addr_xor=1)."
#endif

#define TEST_PASSED             0xFF
#define TEST_FAILED             0x01
#define INJECT_ICCM_SINGLE_BIT  0xE0
#define DISABLE_ERROR_INJECTION 0xE4

#define ICCM_BASE 0xEE000000

extern uintptr_t iccm_start, iccm_end;
extern int printf(const char* format, ...);
extern int putchar(int c);
extern uint32_t iccm_kernel(uint32_t x);

volatile uint32_t boot_count __attribute__((section(".data"))) = 0;

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

void trap_handler(void) {
    uint32_t mcause = read_csr_mcause();
    uint32_t mscause = read_csr_mscause();

    printf("[TRAP] mcause=0x%x mscause=0x%x\n", mcause, mscause);
    if (mcause == 0x1 && mscause == 0x1) {
        printf("FAIL: ICCM instruction access fault (uncorrectable ECC error)\n");
    } else {
        printf("FAIL: unexpected trap\n");
    }
    putchar(TEST_FAILED);
}

static void copy_kernel_to_iccm(void) {
    uint32_t *src = (uint32_t *)&iccm_start;
    volatile uint32_t *dst = (uint32_t *)ICCM_BASE;
    while (src < (uint32_t *)&iccm_end) {
        *dst++ = *src++;
    }
    __asm__ volatile ("fence iorw, iorw");
    __asm__ volatile ("fence.i");
}

// Rewrite one ICCM word with its original value while single-bit injection
// is enabled, so only that word carries a correctable error.
static void corrupt_word(uint32_t idx) {
    uint32_t *src = (uint32_t *)&iccm_start;
    volatile uint32_t *dst = (uint32_t *)ICCM_BASE;
    uint32_t val = src[idx];

    putchar(INJECT_ICCM_SINGLE_BIT);
    __asm__ volatile ("fence iorw, iorw");
    dst[idx] = val;
    __asm__ volatile ("fence iorw, iorw");
    putchar(DISABLE_ERROR_INJECTION);
    __asm__ volatile ("fence.i");
}

static int run_kernel(uint32_t phase, int expect_correction) {
    uint32_t before = read_csr_miccmect();
    uint32_t res = iccm_kernel(0x100);
    uint32_t after = read_csr_miccmect();

    if (res != 0x10F) {
        printf("FAIL [run %u]: kernel returned 0x%x, expected 0x10f\n", phase, res);
        return 1;
    }
    if (expect_correction && after == before) {
        printf("FAIL [run %u]: expected a corrected ICCM single-bit error (miccmect=0x%x)\n", phase, after);
        return 1;
    }
    if (!expect_correction && after != before) {
        printf("FAIL [run %u]: unexpected ICCM ECC error (miccmect 0x%x -> 0x%x)\n", phase, before, after);
        return 1;
    }
    printf("PASS [run %u]: result=0x%x miccmect 0x%x -> 0x%x\n", phase, res, before, after);
    return 0;
}

int main(void) {
    boot_count++;
    if (boot_count != 1) {
        printf("FAIL: re-entered main after a trap\n");
        putchar(TEST_FAILED);
        return 1;
    }

    printf("ICCM address-XOR single-bit ECC correction test\n");

    copy_kernel_to_iccm();
    if (run_kernel(1, 0)) goto fail;

    printf("[Phase 2] single-bit error on odd word 0x%x\n", ICCM_BASE + 4);
    corrupt_word(1);
    if (run_kernel(2, 1)) goto fail;
    // Second pass is served from the redundant CAM row.
    if (run_kernel(3, 0)) goto fail;

    printf("[Phase 3] single-bit error on even word 0x%x\n", ICCM_BASE + 8);
    corrupt_word(2);
    if (run_kernel(4, 1)) goto fail;
    if (run_kernel(5, 0)) goto fail;

    printf("ALL PASSED\n");
    putchar(TEST_PASSED);
    return 0;

fail:
    putchar(TEST_FAILED);
    return 1;
}
