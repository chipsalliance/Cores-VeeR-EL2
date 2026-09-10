/* SPDX-License-Identifier: Apache-2.0
 * Copyright 2026 Google LLC
 *
 * DCLS Safety Scope: ICache Address Infection & Fault Recovery Test
 * Author: Samip Modi (samipmodi@google.com)
 *
 * Description:
 * Commit 63892e51 ("ICache Address Infection") introduces the ICache Address-XOR
 * Infection countermeasure in el2_ifu_mem_ctl.sv.
 *
 * Hardware Counter & Timing Mechanism (micect CSR 0x7F0):
 * - The `micect` CSR (0x7F0) tracks hardware-detected ICache ECC/parity errors.
 * - In `el2_dec_tlu_ctl.sv`, `micect` lower 27 bits increment synchronously whenever
 *   the decode/TLU pipeline stage detects an ICache parity/ECC error (`ic_perr_r` pulse):
 *     assign micect_inc[26:0] = micect[26:0] + {26'b0, ic_perr_r};
 * - Test Timing Sequence:
 *   1. Writing to the MMIO `mailbox` (0x89, 0x8A, 0x8B) primes `tb_top` to force error
 *      corruption on the subsequent ICache fetch.
 *   2. Calling `target_inst()` immediately forces an ICache line read.
 *   3. Core hardware detects the corruption (data fault, XOR mismatch, or hit fault),
 *      pulses `ic_perr_r`, increments `micect`, invalidates the line, and initiates a
 *      pipeline flush and refetch from the SoC bus (AXI4/AHB).
 *   4. `tb_top` detects `ic_perr_r` (sampled as `ic_perr_r_d1`) and releases the forces,
 *      enabling the SoC bus refetch to complete cleanly.
 *   5. By the time `target_inst()` finishes and software reads `micect` via `read_csr()`,
 *      the pipeline restart and retirement are complete, guaranteeing an incremented counter.
 *
 * Test Phases:
 * 1. Phase 1: ICache line warmup.
 * 2. Phase 2: Data fault injection (mailbox 0x89) in el2_ifu_ic_mem triggers core ECC/parity detection,
 *    cache line invalidation, instruction refetch, and increments the micect CSR (0x7F0).
 * 3. Phase 3: Address infection fault injection (mailbox 0x8A).
 *    - Feature enabled (RV_ICACHE_ADDR_XOR): Address XOR mismatch against the read address causes
 *      ECC/parity decoding failure, cache line invalidation, bus refetch, and increments micect.
 *    - Feature disabled (negative test): Verifies that micect does NOT increment when ICACHE_ADDR_XOR=0,
 *      confirming that mailbox 0x8A only exercises error detection when the feature is enabled.
 * 4. Phase 4: Hit logic fault injection (mailbox 0x8B) in el2_ifu_ic_mem triggers ECC/parity detection,
 *    cache line invalidation, refetch, and micect CSR increment.
 * 5. Phase 5: Normal execution without faults runs cleanly after refetch without further micect increment.
 *
 * Configuration:
 * Works across both SECDED ECC (icache_ecc=1) and Byte Parity (icache_ecc=0) configurations.
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

    // Phase 2: Inject ICache read data fault & verify micect CSR (0x7F0) increment.
    // Mailbox 0x89 primes tb_top to force `ic_rd_data = 142'h1`. Calling target_inst()
    // triggers ECC/parity check failure on read data, pulsing `ic_perr_r` in the TLU,
    // which increments `micect` (0x7F0) and initiates a pipeline flush and refetch.
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

    // Phase 3: Inject ICache address fault & verify address XOR mismatch detection.
    // Mailbox 0x8A primes tb_top to force `ic_rd_addr_infect = 64'h1234_5678` (guarded by RV_ICACHE_ADDR_XOR).
    // - If RV_ICACHE_ADDR_XOR is enabled: Fetching target_inst() creates an address XOR mismatch
    //   against the line tag, failing ECC/parity checks, pulsing `ic_perr_r`, incrementing `micect`, and refetching.
    // - If RV_ICACHE_ADDR_XOR is disabled (negative test phase): tb_top skips the force,
    //   verifying that `micect` does NOT increment, confirming the feature is actually exercised.
#ifdef RV_ICACHE_ADDR_XOR
    printf("[Phase 3] Triggering ICache address fault via mailbox (0x8A) [feature enabled]...\n");
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
#else
    printf("[Phase 3] Negative test: Triggering mailbox (0x8A) with feature disabled (ICACHE_ADDR_XOR=0)...\n");
    target_inst();
    count_before = read_csr(0x7F0);
    *mailbox = CMD_INJECT_ICACHE_ADDR_FAULT;
    target_inst();
    count_after = read_csr(0x7F0);
    printf("[Phase 3] Clean execution complete. micect (0x7F0): before = %u, after = %u\n",
           count_before, count_after);
    if (count_after != count_before) {
        printf("FAIL: micect (0x7F0) incremented when ICACHE_ADDR_XOR is disabled! (before = %u, after = %u)\n",
               count_before, count_after);
        *mailbox = CMD_TEST_FAILED;
        return 1;
    }
    printf("[Phase 3] PASS: Verified micect did NOT increment when ICACHE_ADDR_XOR=0\n");
#endif

    // Phase 4: Inject ICache hit logic fault & verify detection and micect increment.
    // Mailbox 0x8B primes tb_top to force multi-bit read data corruption (142'h5555...),
    // simulating incorrect way selection / corrupted hit data. This pulses `ic_perr_r`,
    // increments `micect` (0x7F0), and initiates cache line invalidation and refetch.
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
