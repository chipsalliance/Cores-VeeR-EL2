/* SPDX-License-Identifier: Apache-2.0
 * Copyright 2026 Google LLC
 *
 * ICache Address Infection & Fault Recovery Test
 * Author: Samip Modi (samipmodi@google.com)
 *
 * Description:
 * Commit 63892e51 ("ICache Address Infection") introduces the ICache Address-XOR
 * Infection countermeasure in el2_ifu_mem_ctl.sv, and commit 7dd5354d ("Move iCache
 * ECC and parity check into DCLS") moves the 64-bit ECC/Parity checkers and byte
 * rotators into the DCLS-protected core domain.
 *
 * Hardware Counter & Timing Mechanism (micect CSR 0x7F0):
 * - The `micect` CSR (0x7F0) tracks hardware-detected ICache ECC/parity errors.
 * - In `el2_dec_tlu_ctl.sv`, `micect` lower 27 bits increment synchronously whenever
 *   the decode/TLU pipeline stage detects an ICache parity/ECC error (`ic_perr_r` pulse):
 *     assign micect_inc[26:0] = micect[26:0] + {26'b0, ic_perr_r};
 * - Test Timing Sequence:
 *   1. Writing to the MMIO `mailbox` (0x89..0x8E) primes `tb_top` to inject a fault
 *      on the subsequent ICache fetch or cache line fill.
 *   2. Calling the target function immediately triggers the targeted ICache access.
 *   3. Core hardware detects the corruption (data fault, read/write XOR mismatch,
 *      wrong-way hit, or cross-bank fault), pulses `ic_perr_r`, increments `micect`
 *      by 1, invalidates the cache set, and initiates a pipeline flush and refetch
 *      from the SoC bus (AXI4/AHB).
 *   4. `tb_top` detects `ic_perr_r` (sampled as `ic_perr_r_d1`) and releases the forces,
 *      enabling the SoC bus refetch to complete cleanly.
 *   5. By the time the target function finishes and software reads `micect`, the
 *      pipeline restart and retirement are complete, guaranteeing an exact +1 increment.
 *
 * Test Phases:
 * 1. Phase 1: ICache line warmup for primary and set-aliased target functions.
 * 2. Phase 2: Bank-0 single-bit read data fault (mailbox 0x89) verifies exact +1 `micect`
 *    increment, cache line invalidation, and bus refetch.
 * 3. Phase 3: Read-side address infection fault (mailbox 0x8A, LSB of infection slice).
 *    - Feature enabled (RV_ICACHE_ADDR_XOR=1): 1-bit flip on `ifu_fetch_addr_int_f`
 *      triggers an address-XOR mismatch, failing ECC/parity, invalidating the line,
 *      refetching from the bus, and incrementing `micect` by 1.
 *    - Feature disabled (RV_ICACHE_ADDR_XOR=0, negative test): The same 1-bit flip
 *      slips undetected because `ic_rd_addr_infect` is tied to 0 (`micect` unchanged).
 * 4. Phase 4: Multi-bit read data corruption (mailbox 0x8B) & True Wrong-Way Selection
 *    / Set-Alias fault (mailbox 0x8C).
 *    - Phase 4a (0x8B): Multi-bit read data corruption (`142'h5557...`) verifies ECC/parity
 *      detection across 16-bit halfwords.
 *    - Phase 4b (0x8C): True wrong-way selection swaps `ic_rd_hit_q` ways in `EL2_IC_DATA`
 *      on Set 64 where both Way 0 (`target_way0` at 0x80009000) and Way 1 (`target_way1`
 *      at 0x8000d000) hold valid, ECC-clean lines with different tags.
 *      When RV_ICACHE_ADDR_XOR=1, the tag mismatch in `ic_rd_addr_infect` is caught
 *      (`micect` +1, `target_way0` refetches and executes). When RV_ICACHE_ADDR_XOR=0,
 *      `target_way1` slips past ECC/parity undetected (`micect` +0, `way1_counter` increments).
 * 5. Phase 5: Write-side address infection fault (mailbox 0x8D) & odd-beat cold cache miss
 *    (`ifu_bus_rid_ff[0] == 0` branch of `ic_wr_16bytes_data`).
 *    - Cold miss starts at an odd 8-byte beat offset (`addr % 16 == 8`) while `0x8D` flips
 *      `imb_ff[31]` into `ic_wr_addr_infect` during the cache line fill.
 *    - Call 1 (cold miss) executes cleanly via miss-buffer bypass (`micect` +0).
 *    - Call 2 (warm cache hit from SRAM) detects the infected write XOR when
 *      RV_ICACHE_ADDR_XOR=1 (`micect` +1) and slips undetected when RV_ICACHE_ADDR_XOR=0.
 * 6. Phase 6: Cross-bank straddling fetch (`ic_rd_addr_lo == 2'b01, 2'b11`,
 *    `ic_rd_bank_check_en == 2'b11`), Bank-1 single-bit data fault (mailbox 0x8E),
 *    cross-bank Address-XOR fault (0x8A), and 64-byte cacheline-wrap (`offset 0x3E`).
 * 7. Phase 7: `EL2_IC_DATA` 2-entry read-bypass buffer (`rd_data_hold_ff`) eviction &
 *    `caliptra-ss` MCU0 dynamic `MRAC` (0x7C0) uncacheable/cacheable + `fence.i` flow.
 * 8. Phase 8: Randomized 26-iteration sweep across all infection address bits `[6:31]`
 *    and randomized target functions using a deterministic lockstep-safe Xorshift PRNG.
 * 9. Phase 9: Post-recovery clean execution check.
 *
 * Configuration:
 * Works across both SECDED ECC (icache_ecc=1) and Byte Parity (icache_ecc=0) configurations,
 * Waypack (icache_waypack=0/1), AXI4/AHB-Lite buses, and DCLS lockstep delays.
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include "defines.h"  // Generated.

#define STDOUT_ADDR 0xD0580000
volatile uint32_t *mailbox = (uint32_t *)STDOUT_ADDR;

// Mailbox Command Protocols
#define CMD_INJECT_ICACHE_DATA_FAULT    0x89U
#define CMD_INJECT_ICACHE_ADDR_FAULT    0x8AU
#define CMD_INJECT_ICACHE_MULTIBIT_DATA 0x8BU
#define CMD_INJECT_ICACHE_WAY_FAULT     0x8CU
#define CMD_INJECT_ICACHE_WR_ADDR_FAULT 0x8DU
#define CMD_INJECT_ICACHE_BANK1_FAULT   0x8EU
#define CMD_TEST_PASSED                 0xFFU
#define CMD_TEST_FAILED                 0x01U

// CSR Definitions
#define MRAC_CSR_ADDR   0x7C0  // Region Access Control CSR (mrac)
#define MICECT_CSR_ADDR 0x7F0  // ICache Error Counter CSR (micect)

// Address-XOR Infection slice bounds: ifu_fetch_addr_int_f[31:6]
#define ICACHE_INFECT_BIT_LO 6U
#define ICACHE_INFECT_BIT_HI 31U
#define ICACHE_INFECT_NUM_BITS \
    (ICACHE_INFECT_BIT_HI - ICACHE_INFECT_BIT_LO + 1U)

// Region 8 (0x80000000..0x8FFFFFFF) cacheable bit in MRAC (bit 16)
#define MRAC_REGION8_CACHEABLE_MASK (1UL << 16)

#define STR(x)  #x
#define XSTR(x) STR(x)

#define read_csr(csr) ({ \
    unsigned long res_; \
    __asm__ volatile ("csrr %0, " XSTR(csr) : "=r"(res_)); \
    res_; \
})

#define write_csr(csr, val) do { \
    __asm__ volatile ("csrw " XSTR(csr) ", %0" : : "r"(val)); \
} while (false)

volatile uint32_t counter = 0;
volatile uint32_t way0_counter = 0;
volatile uint32_t way1_counter = 0;
volatile uint32_t way2_counter = 0;
volatile uint32_t cold_wr_counter = 0;
volatile uint32_t straddle_counter = 0;

/**
 * Default trap handler stub.
 */
void trap_handler(void) {
}

/**
 * Primary target function aligned to a 64-byte cache line boundary.
 */
__attribute__((noinline, aligned(64)))
void target_inst(void) {
    counter++;
}

/**
 * Set-aliased Way 0 target function at 0x80009000 (Set 64).
 */
__attribute__((noinline, section(".way0_text"), aligned(64)))
void target_way0(void) {
    __asm__ volatile (
        ".rept 8\n"
        "nop\n"
        ".endr\n"
    );
    way0_counter++;
}

/**
 * Set-aliased Way 1 target function at 0x8000d000 (Set 64, +16KB from `target_way0`).
 */
__attribute__((noinline, section(".way1_text"), aligned(64)))
void target_way1(void) {
    __asm__ volatile (
        ".rept 8\n"
        "nop\n"
        ".endr\n"
    );
    way1_counter++;
}

/**
 * Set-aliased Way 2 target function at 0x80011000 (Set 64, +32KB from `target_way0`).
 * Used to evict the 2-entry `rd_data_hold_ff` read-bypass buffer in `EL2_IC_DATA`.
 */
__attribute__((noinline, section(".way2_text"), aligned(64)))
void target_way2(void) {
    way2_counter++;
}

/**
 * Helper that writes `cmd` to `mailbox` and immediately invokes `fn` from within
 * a single warm 64-byte cache line so no intermediate fetch misses occur.
 */
__attribute__((noinline, aligned(64)))
void call_with_mailbox(void (*fn)(void), uint32_t cmd) {
    if (cmd != 0U) {
        *mailbox = cmd;
        __asm__ volatile ("fence" : : : "memory");
    }
    fn();
}

/**
 * Cold cache-miss target function whose entry point is placed at byte offset 0x08
 * (odd 8-byte beat `imb_ff[5:3] == 3'b001`) of a dedicated 64-byte cache line.
 * Exercises the `ifu_bus_rid_ff[0] == 0` write-XOR branch in `el2_ifu_mem_ctl.sv`.
 */
extern void target_cold_wr_fault(void);
__asm__(
    ".section .text.cold_wr, \"ax\", @progbits\n"
    ".balign 64\n"
    ".word 0x00000013\n"  // Offset 0x00: 32-bit nop padding
    ".word 0x00000013\n"  // Offset 0x04: 32-bit nop padding
    ".global target_cold_wr_fault\n"
    ".type target_cold_wr_fault, @function\n"
    "target_cold_wr_fault:\n"
    "la t0, cold_wr_counter\n"  // Offset 0x08: odd 8B beat (`addr[3] == 1`)
    "lw t1, 0(t0)\n"
    "addi t1, t1, 1\n"
    "sw t1, 0(t0)\n"
    ".rept 8\n"
    ".word 0x00000013\n"
    ".endr\n"
    "ret\n"
    ".size target_cold_wr_fault, .-target_cold_wr_fault\n"
    ".previous\n"
);

/**
 * Cross-bank and 64-byte cacheline-straddling target function.
 * - Starts at a 64-byte boundary (`Offset 0x00`) with two `c.nop` instructions and
 *   a compressed jump `c.j` at `Offset 0x04` that redirects the IFU to `Offset 0x06`
 *   (`ic_rd_addr_lo == 2'b11`).
 * - Executes 32-bit `nop` instructions across all odd halfword offsets `0x06..0x3E`,
 *   exercising:
 *   1. `ic_rd_addr_lo == 2'b11` Bank 0 -> Bank 1 straddle (`Offset 0x06`,
 *      `ic_rd_bank_check_en == 2'b11`).
 *   2. `ic_rd_addr_lo == 2'b01` (`Offset 0x0A`).
 *   3. `ic_rd_addr_lo == 2'b11` Bank 1 -> Bank 0 next-row wrap (`Offset 0x0E`,
 *      `ic_rw_addr_wrap == 1`, `ic_rd_bank_check_en == 2'b11`).
 *   4. `Offset 0x3E` 64-byte cacheline wrap (`ic_cacheline_wrap_ff == 1`,
 *      `line_wrap == 1`, `ic_rd_bank_check_en == 2'b01`).
 */
extern void target_straddle_bank(void);
__asm__(
    ".section .text.straddle, \"ax\", @progbits\n"
    ".balign 64\n"
    ".global target_straddle_bank\n"
    ".type target_straddle_bank, @function\n"
    "target_straddle_bank:\n"
    ".half 0x0001\n"      // Offset 0x00: c.nop
    ".half 0x0001\n"      // Offset 0x02: c.nop
    ".half 0xa009\n"      // Offset 0x04: c.j +2 -> jumps to Offset 0x06 (addr[2:1]=2'b11)
    ".word 0x00000013\n"  // Offset 0x06: straddles Bank 0 & Bank 1 (ic_rd_addr_lo=2'b11)
    ".word 0x00000013\n"  // Offset 0x0A: ic_rd_addr_lo=2'b01
    ".word 0x00000013\n"  // Offset 0x0E: straddles Bank 1 & next-row Bank 0 (ic_rw_addr_wrap=1)
    ".word 0x00000013\n"  // Offset 0x12: ic_rd_addr_lo=2'b01
    ".word 0x00000013\n"  // Offset 0x16: ic_rd_addr_lo=2'b11
    ".word 0x00000013\n"  // Offset 0x1A: ic_rd_addr_lo=2'b01
    ".word 0x00000013\n"  // Offset 0x1E: ic_rd_addr_lo=2'b11 (ic_rw_addr_wrap=1)
    ".word 0x00000013\n"  // Offset 0x22: ic_rd_addr_lo=2'b01
    ".word 0x00000013\n"  // Offset 0x26: ic_rd_addr_lo=2'b11
    ".word 0x00000013\n"  // Offset 0x2A: ic_rd_addr_lo=2'b01
    ".word 0x00000013\n"  // Offset 0x2E: ic_rd_addr_lo=2'b11 (ic_rw_addr_wrap=1)
    ".word 0x00000013\n"  // Offset 0x32: ic_rd_addr_lo=2'b01
    ".word 0x00000013\n"  // Offset 0x36: ic_rd_addr_lo=2'b11
    ".word 0x00000013\n"  // Offset 0x3A: ic_rd_addr_lo=2'b01
    ".word 0x00000013\n"  // Offset 0x3E: straddles 64B cacheline boundary (ic_cacheline_wrap_ff=1)
    ".half 0x0001\n"      // Offset 0x42: c.nop (realigns to 4B boundary at Offset 0x44)
    "la t0, straddle_counter\n"
    "lw t1, 0(t0)\n"
    "addi t1, t1, 1\n"
    "sw t1, 0(t0)\n"
    "ret\n"
    ".size target_straddle_bank, .-target_straddle_bank\n"
    ".previous\n"
);

/**
 * Deterministic 32-bit Xorshift PRNG (lockstep-safe across primary and shadow cores).
 */
static uint32_t xorshift32(uint32_t *state) {
    uint32_t x = *state;
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    *state = x;
    return x;
}

int main(void) {
    printf("=====================================================\n");
    printf(" Starting ICache Address Infection & ECC Recovery Test\n");
    printf("=====================================================\n");

    // -------------------------------------------------------------------------
    // Phase 1: Warm up target instructions and helper in ICache
    // -------------------------------------------------------------------------
    call_with_mailbox(target_inst, 0U);
    target_way0();
    target_way1();
    printf("[Phase 1] Cache line warmup complete. Counter = %u\n",
           (unsigned int)counter);

    // -------------------------------------------------------------------------
    // Phase 2: Single-bit read data fault across both physical banks (mailbox 0x89)
    // -------------------------------------------------------------------------
    printf("[Phase 2] Triggering ICache read data fault via mailbox (0x89)...\n");
    target_inst();
    uint32_t count_before = (uint32_t)read_csr(MICECT_CSR_ADDR);
    call_with_mailbox(target_inst, CMD_INJECT_ICACHE_DATA_FAULT);
    uint32_t count_after = (uint32_t)read_csr(MICECT_CSR_ADDR);
    printf("[Phase 2] Pipeline flush & refetch complete. micect (0x7F0): before = %u, after = %u\n",
           (unsigned int)count_before, (unsigned int)count_after);
    if (count_after != count_before + 1U) {
        printf("FAIL: Phase 2 expected micect == %u, got %u!\n",
               (unsigned int)(count_before + 1U), (unsigned int)count_after);
        *mailbox = CMD_TEST_FAILED;
        return 1;
    }

    // -------------------------------------------------------------------------
    // Phase 3: Read-side address infection fault (mailbox 0x8A)
    // -------------------------------------------------------------------------
#ifdef RV_ICACHE_ADDR_XOR
    printf("[Phase 3] Triggering ICache address fault via mailbox (0x8A) [feature enabled]...\n");
    target_inst();
    count_before = (uint32_t)read_csr(MICECT_CSR_ADDR);
    call_with_mailbox(target_inst, CMD_INJECT_ICACHE_ADDR_FAULT);
    count_after = (uint32_t)read_csr(MICECT_CSR_ADDR);
    printf("[Phase 3] Pipeline flush & refetch complete. micect (0x7F0): before = %u, after = %u\n",
           (unsigned int)count_before, (unsigned int)count_after);
    if (count_after != count_before + 1U) {
        printf("FAIL: Phase 3 expected micect == %u, got %u!\n",
               (unsigned int)(count_before + 1U), (unsigned int)count_after);
        *mailbox = CMD_TEST_FAILED;
        return 1;
    }
#else
    printf("[Phase 3] Negative test: Triggering mailbox (0x8A) with feature disabled (ICACHE_ADDR_XOR=0)...\n");
    target_inst();
    count_before = (uint32_t)read_csr(MICECT_CSR_ADDR);
    call_with_mailbox(target_inst, CMD_INJECT_ICACHE_ADDR_FAULT);
    count_after = (uint32_t)read_csr(MICECT_CSR_ADDR);
    printf("[Phase 3] Clean execution complete. micect (0x7F0): before = %u, after = %u\n",
           (unsigned int)count_before, (unsigned int)count_after);
    if (count_after != count_before) {
        printf("FAIL: Phase 3 micect incremented when ICACHE_ADDR_XOR=0! (before = %u, after = %u)\n",
               (unsigned int)count_before, (unsigned int)count_after);
        *mailbox = CMD_TEST_FAILED;
        return 1;
    }
    printf("[Phase 3] PASS: Verified fault slipped undetected when ICACHE_ADDR_XOR=0\n");
#endif

    // -------------------------------------------------------------------------
    // Phase 4: Multi-bit read data fault across both banks (0x8B) &
    //          True Wrong-Way Selection (0x8C)
    // -------------------------------------------------------------------------
    printf("[Phase 4a] Triggering multi-bit read data corruption via mailbox (0x8B)...\n");
    target_inst();
    count_before = (uint32_t)read_csr(MICECT_CSR_ADDR);
    call_with_mailbox(target_inst, CMD_INJECT_ICACHE_MULTIBIT_DATA);
    count_after = (uint32_t)read_csr(MICECT_CSR_ADDR);
    printf("[Phase 4a] Pipeline flush & refetch complete. micect (0x7F0): before = %u, after = %u\n",
           (unsigned int)count_before, (unsigned int)count_after);
    if (count_after != count_before + 1U) {
        printf("FAIL: Phase 4a expected micect == %u, got %u!\n",
               (unsigned int)(count_before + 1U), (unsigned int)count_after);
        *mailbox = CMD_TEST_FAILED;
        return 1;
    }

    // Phase 4b: Populate both ways of Set 64 (`target_way0` and `target_way1`) with
    // valid, ECC-clean lines that have different tags (0x80009000 vs 0x8000d000).
    printf("[Phase 4b] Triggering true wrong-way selection (`ic_rd_hit_q` swap, 0x8C)...\n");
    target_way0();
    target_way1();
    uint32_t w0_before = way0_counter;
    uint32_t w1_before = way1_counter;
    count_before = (uint32_t)read_csr(MICECT_CSR_ADDR);
    call_with_mailbox(target_way0, CMD_INJECT_ICACHE_WAY_FAULT);
    count_after = (uint32_t)read_csr(MICECT_CSR_ADDR);
#ifdef RV_ICACHE_ADDR_XOR
    printf("[Phase 4b] Wrong-way hit caught! micect: %u -> %u, way0_cnt: %u -> %u, way1_cnt: %u -> %u\n",
           (unsigned int)count_before, (unsigned int)count_after,
           (unsigned int)w0_before, (unsigned int)way0_counter,
           (unsigned int)w1_before, (unsigned int)way1_counter);
    if ((count_after != count_before + 1U) ||
        (way0_counter != w0_before + 1U) ||
        (way1_counter != w1_before)) {
        printf("FAIL: Phase 4b wrong-way selection fault was not properly caught and recovered!\n");
        *mailbox = CMD_TEST_FAILED;
        return 1;
    }
#else
    printf("[Phase 4b] Negative test (ICACHE_ADDR_XOR=0): micect: %u -> %u, way0_cnt: %u -> %u, way1_cnt: %u -> %u\n",
           (unsigned int)count_before, (unsigned int)count_after,
           (unsigned int)w0_before, (unsigned int)way0_counter,
           (unsigned int)w1_before, (unsigned int)way1_counter);
    if ((count_after != count_before) || (way1_counter != w1_before + 1U)) {
        printf("FAIL: Phase 4b negative test unexpected behavior when ICACHE_ADDR_XOR=0!\n");
        *mailbox = CMD_TEST_FAILED;
        return 1;
    }
#endif

    // -------------------------------------------------------------------------
    // Phase 5: Write-side address infection fault (0x8D) & odd-beat cold miss
    // (`ifu_bus_rid_ff[0] == 0` branch of `ic_wr_16bytes_data`)
    // -------------------------------------------------------------------------
    printf("[Phase 5] Triggering write-side address infection fault (0x8D) on odd-beat cold miss...\n");
    call_with_mailbox(target_inst, 0U);
    count_before = (uint32_t)read_csr(MICECT_CSR_ADDR);
    // Call 1: Cold miss on `target_cold_wr_fault` (entry at offset 0x08 -> odd beat 1).
    // Executes from the miss-buffer bypass (`sel_byp_data = 1`), while the line written
    // to ICache SRAM on `last_beat` is infected with a corrupted `ic_wr_addr_infect`.
    call_with_mailbox(target_cold_wr_fault, CMD_INJECT_ICACHE_WR_ADDR_FAULT);
    target_way0();
    uint32_t count_after_miss = (uint32_t)read_csr(MICECT_CSR_ADDR);
    if (count_after_miss != count_before) {
        printf("FAIL: Phase 5 expected 0 errors during miss-buffer bypass, got %u -> %u!\n",
               (unsigned int)count_before, (unsigned int)count_after_miss);
        *mailbox = CMD_TEST_FAILED;
        return 1;
    }
    // Call 2: Warm cache hit reading the infected line from ICache SRAM.
    target_cold_wr_fault();
    count_after = (uint32_t)read_csr(MICECT_CSR_ADDR);
#ifdef RV_ICACHE_ADDR_XOR
    printf("[Phase 5] Write-side infection detected on subsequent SRAM hit! micect: %u -> %u\n",
           (unsigned int)count_before, (unsigned int)count_after);
    if (count_after != count_before + 1U) {
        printf("FAIL: Phase 5 expected micect == %u on infected SRAM hit, got %u!\n",
               (unsigned int)(count_before + 1U), (unsigned int)count_after);
        *mailbox = CMD_TEST_FAILED;
        return 1;
    }
#else
    printf("[Phase 5] Negative test (ICACHE_ADDR_XOR=0): micect: %u -> %u\n",
           (unsigned int)count_before, (unsigned int)count_after);
    if (count_after != count_before) {
        printf("FAIL: Phase 5 micect incremented when ICACHE_ADDR_XOR=0!\n");
        *mailbox = CMD_TEST_FAILED;
        return 1;
    }
#endif

    // -------------------------------------------------------------------------
    // Phase 6: Cross-bank straddling fetch (`ic_rd_addr_lo == 2'b01, 2'b11`,
    // `ic_rd_bank_check_en == 2'b11`), Bank-1 fault (0x8E), & 64B cacheline wrap
    // -------------------------------------------------------------------------
    printf("[Phase 6a] Warming up cross-bank & 64B-wrap straddling sequence and testing Bank-1 fault (0x8E)...\n");
    target_straddle_bank();
    call_with_mailbox(target_inst, 0U);
    count_before = (uint32_t)read_csr(MICECT_CSR_ADDR);
    call_with_mailbox(target_straddle_bank, CMD_INJECT_ICACHE_BANK1_FAULT);
    count_after = (uint32_t)read_csr(MICECT_CSR_ADDR);
    printf("[Phase 6a] Bank-1 fault recovery complete. micect: %u -> %u, straddle_cnt = %u\n",
           (unsigned int)count_before, (unsigned int)count_after,
           (unsigned int)straddle_counter);
    if (count_after != count_before + 1U) {
        printf("FAIL: Phase 6a Bank-1 checker failed to increment micect by 1!\n");
        *mailbox = CMD_TEST_FAILED;
        return 1;
    }

    // Phase 6b: Direct entry at odd halfword offset +6 (`ic_rd_addr_lo == 2'b11`)
    // with Address-XOR fault (0x8A).
    void (*straddle_odd_entry)(void) =
        (void (*)(void))((uintptr_t)target_straddle_bank + 6U);
    target_straddle_bank();
    call_with_mailbox(target_inst, 0U);
    count_before = (uint32_t)read_csr(MICECT_CSR_ADDR);
    call_with_mailbox(straddle_odd_entry, CMD_INJECT_ICACHE_ADDR_FAULT);
    count_after = (uint32_t)read_csr(MICECT_CSR_ADDR);
#ifdef RV_ICACHE_ADDR_XOR
    printf("[Phase 6b] Cross-bank straddling Address-XOR fault caught! micect: %u -> %u\n",
           (unsigned int)count_before, (unsigned int)count_after);
    if (count_after != count_before + 1U) {
        printf("FAIL: Phase 6b expected micect == %u, got %u!\n",
               (unsigned int)(count_before + 1U), (unsigned int)count_after);
        *mailbox = CMD_TEST_FAILED;
        return 1;
    }
#else
    if (count_after != count_before) {
        printf("FAIL: Phase 6b micect incremented when ICACHE_ADDR_XOR=0!\n");
        *mailbox = CMD_TEST_FAILED;
        return 1;
    }
#endif

    // -------------------------------------------------------------------------
    // Phase 7: `EL2_IC_DATA` 2-entry read-bypass buffer (`rd_data_hold_ff`) eviction
    // & `caliptra-ss` MCU0 dynamic `MRAC` uncacheable/cacheable + `fence.i` flow
    // -------------------------------------------------------------------------
    printf("[Phase 7a] Evicting 2-entry `rd_data_hold_ff` bypass buffer before SRAM fault injection...\n");
    target_inst();
    // Fetch 3 distinct cache lines so `target_inst` is evicted from the 2-entry
    // `rd_data_hold_ff` bypass buffer in `EL2_IC_DATA` while remaining valid in SRAM.
    target_way0();
    target_way1();
    target_way2();
    call_with_mailbox(target_way0, 0U);
    count_before = (uint32_t)read_csr(MICECT_CSR_ADDR);
    call_with_mailbox(target_inst, CMD_INJECT_ICACHE_ADDR_FAULT);
    count_after = (uint32_t)read_csr(MICECT_CSR_ADDR);
#ifdef RV_ICACHE_ADDR_XOR
    if (count_after != count_before + 1U) {
        printf("FAIL: Phase 7a SRAM-direct read fault failed to increment micect!\n");
        *mailbox = CMD_TEST_FAILED;
        return 1;
    }
#else
    if (count_after != count_before) {
        printf("FAIL: Phase 7a micect incremented when ICACHE_ADDR_XOR=0!\n");
        *mailbox = CMD_TEST_FAILED;
        return 1;
    }
#endif

    printf("[Phase 7b] Testing `caliptra-ss` MCU0 dynamic MRAC uncacheable/cacheable + fence.i flow...\n");
    unsigned long orig_mrac = read_csr(MRAC_CSR_ADDR);
    // Mark Region 8 (0x80000000) uncacheable in MRAC (`ifc_fetch_uncacheable_bf = 1`)
    write_csr(MRAC_CSR_ADDR, orig_mrac & ~MRAC_REGION8_CACHEABLE_MASK);
    __asm__ volatile ("fence.i");
    count_before = (uint32_t)read_csr(MICECT_CSR_ADDR);
    target_inst();
    count_after = (uint32_t)read_csr(MICECT_CSR_ADDR);
    if (count_after != count_before) {
        printf("FAIL: Phase 7b unexpected micect increment during uncacheable MRAC fetch!\n");
        *mailbox = CMD_TEST_FAILED;
        return 1;
    }
    // Restore Region 8 cacheable in MRAC and invalidate tags via `fence.i`
    write_csr(MRAC_CSR_ADDR, orig_mrac | MRAC_REGION8_CACHEABLE_MASK);
    __asm__ volatile ("fence.i");
    target_inst();
    call_with_mailbox(target_way0, 0U);
    count_before = (uint32_t)read_csr(MICECT_CSR_ADDR);
    call_with_mailbox(target_inst, CMD_INJECT_ICACHE_ADDR_FAULT);
    count_after = (uint32_t)read_csr(MICECT_CSR_ADDR);
#ifdef RV_ICACHE_ADDR_XOR
    if (count_after != count_before + 1U) {
        printf("FAIL: Phase 7b post-MRAC/fence.i Address-XOR check failed!\n");
        *mailbox = CMD_TEST_FAILED;
        return 1;
    }
#else
    if (count_after != count_before) {
        printf("FAIL: Phase 7b post-MRAC/fence.i negative check failed!\n");
        *mailbox = CMD_TEST_FAILED;
        return 1;
    }
#endif
    write_csr(MRAC_CSR_ADDR, orig_mrac);
    printf("[Phase 7] Bypass-buffer eviction & MRAC/fence.i transition verified.\n");

    // -------------------------------------------------------------------------
    // Phase 8: Randomized 26-Iteration Sweep Across All Infection Address Bits [6:31]
    // -------------------------------------------------------------------------
    printf("[Phase 8] Running randomized 26-bit address-infection sweep (bits %u..%u)...\n",
           ICACHE_INFECT_BIT_LO, ICACHE_INFECT_BIT_HI);
    uint8_t bit_perm[ICACHE_INFECT_NUM_BITS];
    for (uint32_t i = 0U; i < ICACHE_INFECT_NUM_BITS; ++i) {
        bit_perm[i] = (uint8_t)(ICACHE_INFECT_BIT_LO + i);
    }
    uint32_t prng_state = 0xC0FFEE42U;
    for (uint32_t i = ICACHE_INFECT_NUM_BITS - 1U; i > 0U; --i) {
        uint32_t j = xorshift32(&prng_state) % (i + 1U);
        uint8_t tmp = bit_perm[i];
        bit_perm[i] = bit_perm[j];
        bit_perm[j] = tmp;
    }

    void (*target_table[4])(void) = {
        target_inst,
        target_way0,
        target_way1,
        target_straddle_bank,
    };

    uint32_t sweep_before = (uint32_t)read_csr(MICECT_CSR_ADDR);
    for (uint32_t i = 0U; i < ICACHE_INFECT_NUM_BITS; ++i) {
        uint32_t bit_idx = (uint32_t)bit_perm[i];
        uint32_t fn_idx = xorshift32(&prng_state) & 3U;
        void (*fn)(void) = target_table[fn_idx];

        // Warm up selected target function and `call_with_mailbox`
        fn();
        call_with_mailbox(target_way2, 0U);

        uint32_t iter_before = (uint32_t)read_csr(MICECT_CSR_ADDR);
        uint32_t cmd = CMD_INJECT_ICACHE_ADDR_FAULT | (bit_idx << 8);
        call_with_mailbox(fn, cmd);
        uint32_t iter_after = (uint32_t)read_csr(MICECT_CSR_ADDR);

#ifdef RV_ICACHE_ADDR_XOR
        if (iter_after != iter_before + 1U) {
            printf("FAIL: [Phase 8] Iter %u (addr bit %u, fn %u): expected micect %u, got %u!\n",
                   (unsigned int)i, (unsigned int)bit_idx, (unsigned int)fn_idx,
                   (unsigned int)(iter_before + 1U), (unsigned int)iter_after);
            *mailbox = CMD_TEST_FAILED;
            return 1;
        }
#else
        if (iter_after != iter_before) {
            printf("FAIL: [Phase 8] Iter %u (addr bit %u): micect incremented when ICACHE_ADDR_XOR=0!\n",
                   (unsigned int)i, (unsigned int)bit_idx);
            *mailbox = CMD_TEST_FAILED;
            return 1;
        }
#endif
    }
    uint32_t sweep_after = (uint32_t)read_csr(MICECT_CSR_ADDR);
    printf("[Phase 8] Randomized 26-bit sweep complete. micect: %u -> %u\n",
           (unsigned int)sweep_before, (unsigned int)sweep_after);

    // -------------------------------------------------------------------------
    // Phase 9: Verification of cache refetch and normal operation without faults
    // -------------------------------------------------------------------------
    printf("[Phase 9] Executing target functions without fault injection...\n");
    count_before = (uint32_t)read_csr(MICECT_CSR_ADDR);
    target_inst();
    target_way0();
    target_way1();
    target_cold_wr_fault();
    target_straddle_bank();
    count_after = (uint32_t)read_csr(MICECT_CSR_ADDR);
    if (count_after != count_before) {
        printf("FAIL: Unexpected micect increment during clean execution!\n");
        *mailbox = CMD_TEST_FAILED;
        return 1;
    }
    printf("[Phase 9] Clean execution verified. Counters: main=%u, w0=%u, w1=%u, w2=%u, cold_wr=%u, straddle=%u\n",
           (unsigned int)counter, (unsigned int)way0_counter,
           (unsigned int)way1_counter, (unsigned int)way2_counter,
           (unsigned int)cold_wr_counter, (unsigned int)straddle_counter);

    // Finish test cleanly with TEST_PASSED
    printf("All ICache Address Infection & Fault Recovery test phases PASSED!\n");
    *mailbox = CMD_TEST_PASSED;

    return 0;
}
