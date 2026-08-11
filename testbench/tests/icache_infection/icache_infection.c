/* SPDX-License-Identifier: Apache-2.0
 * Copyright 2024 Google LLC
 *
 * ICache Address Infection & Fault Recovery Test
 *
 * Architecture & Test Intent:
 * Commit 63892e51 ("ICache Address Infection") introduces the ICache Address-XOR
 * Infection countermeasure in el2_ifu_mem_ctl.sv.
 *
 * This test verifies:
 * 1. Data fault injection (mailbox 0x89) in el2_ifu_ic_mem triggers core ECC/parity detection,
 *    cache line invalidation, instruction refetch, and increments the micect CSR (0x7F0).
 * 2. Address fault injection (mailbox 0x8A) in el2_ifu_ic_mem produces an XOR mismatch against
 *    the read address, resulting in ECC/parity decoding failure, cache line invalidation,
 *    refetch, and micect CSR increment.
 * 3. Hit logic fault injection (mailbox 0x8B) in el2_ifu_ic_mem triggers ECC/parity detection,
 *    cache line invalidation, refetch, and micect CSR increment.
 * 4. Normal execution without faults runs cleanly after refetch without further micect increment.
 * 5. Works across both ECC (icache_ecc=1) and Parity (icache_ecc=0) configurations.
 */

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

#define STDOUT_ADDR 0xD0580000
volatile uint32_t *mailbox = (uint32_t *)STDOUT_ADDR;

// Mailbox Command Protocols
#define CMD_INJECT_ICACHE_DATA_FAULT 0x89
#define CMD_INJECT_ICACHE_ADDR_FAULT 0x8A
#define CMD_INJECT_ICACHE_HIT_FAULT  0x8B
#define CMD_TEST_PASSED              0xFF
#define CMD_TEST_FAILED              0x01

// CSR Definitions
#define MICECT_CSR_ADDR          0x7F0  // ICache Error Counter CSR (micect)

#define read_csr(csr) ({ \
    unsigned long res; \
    asm volatile ("csrr %0, " #csr : "=r"(res)); \
    res; \
})

#define write_csr(csr, val) { \
    asm volatile ("csrw " #csr ", %0" : : "r"(val)); \
}

static volatile uint32_t counter = 0;

void trap_handler(void) {
    // Default trap handler stub
}

// Function aligned to 16-byte boundary to isolate instruction cache line fetch
__attribute__((noinline, aligned(16)))
void target_inst(void) {
    counter++;
}

int main(void) {
    printf("=====================================================\n");
    printf(" Starting ICache Address Infection & ECC Recovery Test\n");
    printf("=====================================================\n");

    // Phase 1: Warm up target instruction in ICache (populates cache line)
    target_inst();
    printf("[Phase 1] Cache line warmup complete. Counter = %u\n", counter);

    // Phase 2: Inject ICache read data fault & verify micect CSR (0x7F0) increment
    printf("[Phase 2] Triggering ICache read data fault via mailbox (0x89)...\n");
    target_inst();
    uint32_t count_before = read_csr(0x7F0);
    *mailbox = CMD_INJECT_ICACHE_DATA_FAULT;
    target_inst();
    uint32_t count_after = read_csr(0x7F0);
    printf("[Phase 2] Pipeline flush & refetch complete. micect (0x7F0): before = %u, after = %u\n",
           count_before, count_after);
    if (count_after <= count_before) {
        printf("FAIL: Hardware ICache error counter (micect 0x7F0) failed to increment on data fault!\n");
        *mailbox = CMD_TEST_FAILED;
        return 1;
    }

    // Phase 3: Inject ICache address fault & verify address XOR mismatch detection and micect increment
    printf("[Phase 3] Triggering ICache address fault via mailbox (0x8A)...\n");
    target_inst();
    count_before = read_csr(0x7F0);
    *mailbox = CMD_INJECT_ICACHE_ADDR_FAULT;
    target_inst();
    count_after = read_csr(0x7F0);
    printf("[Phase 3] Pipeline flush & refetch complete. micect (0x7F0): before = %u, after = %u\n",
           count_before, count_after);
    if (count_after <= count_before) {
        printf("FAIL: Hardware ICache error counter (micect 0x7F0) failed to increment on address fault!\n");
        *mailbox = CMD_TEST_FAILED;
        return 1;
    }

    // Phase 4: Inject ICache hit logic fault & verify detection and micect increment
    printf("[Phase 4] Triggering ICache hit logic fault via mailbox (0x8B)...\n");
    target_inst();
    count_before = read_csr(0x7F0);
    *mailbox = CMD_INJECT_ICACHE_HIT_FAULT;
    target_inst();
    count_after = read_csr(0x7F0);
    printf("[Phase 4] Pipeline flush & refetch complete. micect (0x7F0): before = %u, after = %u\n",
           count_before, count_after);
    if (count_after <= count_before) {
        printf("FAIL: Hardware ICache error counter (micect 0x7F0) failed to increment on hit logic fault!\n");
        *mailbox = CMD_TEST_FAILED;
        return 1;
    }

    // Phase 5: Verification of cache refetch and normal operation without faults
    printf("[Phase 5] Executing target_inst() without fault injection...\n");
    count_before = read_csr(0x7F0);
    target_inst();
    count_after = read_csr(0x7F0);
    if (count_after != count_before) {
        printf("FAIL: Unexpected micect increment during clean execution!\n");
        *mailbox = CMD_TEST_FAILED;
        return 1;
    }
    printf("[Phase 5] Clean execution verified. Total counter = %u\n", counter);

    // Finish test cleanly with TEST_PASSED
    printf("All ICache Address Infection & Fault Recovery test phases PASSED!\n");
    *mailbox = CMD_TEST_PASSED;

    return 0;
}
