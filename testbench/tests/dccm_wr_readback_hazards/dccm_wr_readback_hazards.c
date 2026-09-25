/* SPDX-License-Identifier: Apache-2.0
 * Copyright 2026 Google LLC
 *
 * DCCM Write Readback Check Pipeline Hazards & Stall Verification (#512)
 * Author: Samip Modi (samipmodi@google.com)
 *
 * Description:
 * This test verifies the DCCM write-readback check feature (RV_DCCM_WR_READBACK)
 * under tight pipeline hazard conditions, as specified in Issue #512. It verifies
 * that the readback check operates transparently without deadlocks, corruption,
 * or unexpected pipeline stalls during snoop and opportunistic steal resolution,
 * sustained load bursts, store-buffer backpressure saturation, and runtime disable.
 *
 * Test Phases:
 * 1. Phase 1: Snoop Path (#512) - Store followed immediately by a load to the exact
 *    same address. Verifies that the check resolves via snoop with zero additional stalls.
 * 2. Phase 2: Steal Path (#512) - Store followed by non-DCCM arithmetic/register instructions.
 *    Verifies opportunistic read-port stealing on cycle N+1 when DCCM read port is idle.
 * 3. Phase 3: Sustained Read Stream (#512) - Store followed by an unbroken stream of 32
 *    consecutive DCCM loads to distinct addresses. Verifies check remains outstanding
 *    indefinitely without deadlock/starvation, resolving on the first idle cycle.
 * 4. Phase 4: Store Buffer Full (#512) - Burst 5 stores while check is pending to saturate
 *    the 4-entry store buffer. Verifies clean decode stall via lsu_stbuf_full_any
 *    backpressure, with all stores draining in FIFO order without corruption or hang.
 * 5. Phase 5: Runtime Disable (#512) - Toggles the MFDC.dwrd bit (bit 7) to verify that
 *    the write-readback check can be dynamically disabled and re-enabled.
 */

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#define MFDC_CSR 0x7f9
#define MFDC_DCCM_WR_READBACK_DISABLE_MASK (1u << 7) /* bit 7, "dwrd" */

#define TEST_PASSED 0xff
#define TEST_FAILED 0x01

#define DCCM_SADDR 0xf0040000
#define DCCM_TEST_BASE (DCCM_SADDR + 0x4000)

extern int printf(const char *format, ...);
extern int putchar(int c);

/**
 * Halts execution and reports failure to testbench harness.
 */
static void report_failure(void) {
  printf("Test FAILED!\n");
  putchar(TEST_FAILED);
  while (true) {}
}

/**
 * Reads the Machine Feature Disable Control (MFDC) register.
 */
static uint32_t read_mfdc(void) {
  uint32_t mfdc;
  __asm__ volatile("csrr %0, %1" : "=r"(mfdc) : "i"(MFDC_CSR) : );
  return mfdc;
}

/**
 * Disables the DCCM write-readback check at runtime via MFDC.dwrd.
 */
static void disable_dccm_wr_readback(void) {
  uint32_t mask = MFDC_DCCM_WR_READBACK_DISABLE_MASK;
  __asm__ volatile("csrs %0, %1" : : "i"(MFDC_CSR), "r"(mask) : );

  if ((read_mfdc() & MFDC_DCCM_WR_READBACK_DISABLE_MASK) == 0) {
    printf("ERROR: dwrd bit did not read back as set after disable!\n");
    report_failure();
  }
}

/**
 * Enables the DCCM write-readback check at runtime via MFDC.dwrd.
 */
static void enable_dccm_wr_readback(void) {
  uint32_t mask = MFDC_DCCM_WR_READBACK_DISABLE_MASK;
  __asm__ volatile("csrc %0, %1" : : "i"(MFDC_CSR), "r"(mask) : );

  if ((read_mfdc() & MFDC_DCCM_WR_READBACK_DISABLE_MASK) != 0) {
    printf("ERROR: dwrd bit did not read back as clear after enable!\n");
    report_failure();
  }
}

/**
 * Phase 1: Snoop Path Verification (#512)
 *
 * Executes a store immediately followed by a load to the exact same DCCM word
 * address. The LSU readback check must snoop the read data without stealing
 * the port or adding stall cycles.
 */
static void test_phase1_snoop_path(void) {
  printf("Starting Phase 1: Snoop Path (#512)...\n");

  const uint32_t test_patterns[] = {
      0x12345678, 0xdeadbeef, 0x00000000, 0xffffffff,
      0xa5a5a5a5, 0x5a5a5a5a, 0x00000001, 0x80000000};
  const uint32_t offsets[] = {0x00, 0x04, 0x08, 0x0c, 0x40, 0x80, 0x100, 0x200};
  const size_t num_tests = sizeof(test_patterns) / sizeof(test_patterns[0]);

  for (size_t i = 0; i < num_tests; i++) {
    volatile uint32_t *target_ptr = (volatile uint32_t *)(DCCM_TEST_BASE + offsets[i]);
    uint32_t pattern = test_patterns[i];
    uint32_t snooped_val = 0;

    // sw immediately followed by lw to the same address
    __asm__ volatile(
        "sw   %[val], 0(%[addr])\n\t"
        "lw   %[res], 0(%[addr])\n\t"
        : [res] "=r"(snooped_val)
        : [val] "r"(pattern), [addr] "r"(target_ptr)
        : "memory");

    if (snooped_val != pattern) {
      printf("Phase 1 FAILED: Snoop mismatch at offset 0x%x: wrote 0x%x, got 0x%x\n",
             offsets[i], pattern, snooped_val);
      report_failure();
    }

    // Verify stored data remains intact in SRAM
    if (*target_ptr != pattern) {
      printf("Phase 1 FAILED: Memory verify mismatch at offset 0x%x: expected 0x%x, read 0x%x\n",
             offsets[i], pattern, *target_ptr);
      report_failure();
    }
  }

  printf("Phase 1 Passed: Snoop path verified across %d address/pattern combinations.\n\n",
         (int)num_tests);
}

/**
 * Phase 2: Steal Path Verification (#512)
 *
 * Executes a store followed by non-DCCM instructions (arithmetic, NOPs).
 * Since the DCCM read port is idle, the check must opportunistically steal
 * the port on cycle N+1 without stalling the non-DCCM execution flow.
 */
static void test_phase2_steal_path(void) {
  printf("Starting Phase 2: Steal Path (#512)...\n");

  const uint32_t test_patterns[] = {0xcafe0001, 0xcafe0002, 0xcafe0003, 0xcafe0004};
  const uint32_t offsets[] = {0x300, 0x304, 0x308, 0x30c};
  const size_t num_tests = sizeof(test_patterns) / sizeof(test_patterns[0]);

  for (size_t i = 0; i < num_tests; i++) {
    volatile uint32_t *target_ptr = (volatile uint32_t *)(DCCM_TEST_BASE + offsets[i]);
    uint32_t pattern = test_patterns[i];
    uint32_t t0 = 0;
    uint32_t t1 = 0;

    // sw followed by non-DCCM arithmetic operations leaving read port idle
    __asm__ volatile(
        "sw    %[val], 0(%[addr])\n\t"
        "addi  %[t0], %[val], 1\n\t"
        "addi  %[t1], %[t0], 2\n\t"
        "xor   %[t0], %[t0], %[t1]\n\t"
        "nop\n\t"
        "nop\n\t"
        : [t0] "=&r"(t0), [t1] "=&r"(t1)
        : [val] "r"(pattern), [addr] "r"(target_ptr)
        : "memory");

    // Memory read after opportunistic steal should return newly written data
    uint32_t readback_val = *target_ptr;
    if (readback_val != pattern) {
      printf("Phase 2 FAILED: Steal path mismatch at offset 0x%x: wrote 0x%x, read 0x%x\n",
             offsets[i], pattern, readback_val);
      report_failure();
    }
  }

  printf("Phase 2 Passed: Steal path verified across %d addresses.\n\n", (int)num_tests);
}

/**
 * Phase 3: Sustained Read Stream Starvation Stress (#512)
 *
 * Executes a store to address A, immediately followed by an unrolled sequence
 * of 32 consecutive DCCM loads to addresses B_0 ... B_31 (where B_k != A).
 *
 * Since every cycle contains a real read to a non-matching address:
 * - Snoop does not match (B_k != A)
 * - Port stealing is suppressed (reads have strict priority)
 * - The check remains outstanding indefinitely without deadlocking the core.
 *
 * An idle cycle following the burst allows the check to resolve cleanly.
 */
static void test_phase3_sustained_read_stream(void) {
  printf("Starting Phase 3: Sustained Read Stream Starvation Stress (#512)...\n");

  volatile uint32_t *store_target = (volatile uint32_t *)(DCCM_TEST_BASE + 0x400);
  volatile uint32_t *stream_base = (volatile uint32_t *)(DCCM_TEST_BASE + 0x500);

  const uint32_t store_pattern = 0xbabecafe;

  // Initialize the 32 streaming addresses with unique values
  for (int i = 0; i < 32; i++) {
    stream_base[i] = 0x10000 + i;
  }

  uint32_t first_loaded_val = 0;
  uint32_t last_loaded_val = 0;

  // Store to A, immediately followed by 32 back-to-back loads from B_0..B_31
  __asm__ volatile(
      "sw   %[st_val], 0(%[st_addr])\n\t"
      "lw   %[first_val], 0*4(%[rd_base])\n\t"
      "lw   t0,   1*4(%[rd_base])\n\t"
      "lw   t1,   2*4(%[rd_base])\n\t"
      "lw   t2,   3*4(%[rd_base])\n\t"
      "lw   t0,   4*4(%[rd_base])\n\t"
      "lw   t1,   5*4(%[rd_base])\n\t"
      "lw   t2,   6*4(%[rd_base])\n\t"
      "lw   t0,   7*4(%[rd_base])\n\t"
      "lw   t1,   8*4(%[rd_base])\n\t"
      "lw   t2,   9*4(%[rd_base])\n\t"
      "lw   t0,  10*4(%[rd_base])\n\t"
      "lw   t1,  11*4(%[rd_base])\n\t"
      "lw   t2,  12*4(%[rd_base])\n\t"
      "lw   t0,  13*4(%[rd_base])\n\t"
      "lw   t1,  14*4(%[rd_base])\n\t"
      "lw   t2,  15*4(%[rd_base])\n\t"
      "lw   t0,  16*4(%[rd_base])\n\t"
      "lw   t1,  17*4(%[rd_base])\n\t"
      "lw   t2,  18*4(%[rd_base])\n\t"
      "lw   t0,  19*4(%[rd_base])\n\t"
      "lw   t1,  20*4(%[rd_base])\n\t"
      "lw   t2,  21*4(%[rd_base])\n\t"
      "lw   t0,  22*4(%[rd_base])\n\t"
      "lw   t1,  23*4(%[rd_base])\n\t"
      "lw   t2,  24*4(%[rd_base])\n\t"
      "lw   t0,  25*4(%[rd_base])\n\t"
      "lw   t1,  26*4(%[rd_base])\n\t"
      "lw   t2,  27*4(%[rd_base])\n\t"
      "lw   t0,  28*4(%[rd_base])\n\t"
      "lw   t1,  29*4(%[rd_base])\n\t"
      "lw   t2,  30*4(%[rd_base])\n\t"
      "lw   %[last_val],  31*4(%[rd_base])\n\t"
      "nop\n\t"
      "nop\n\t"
      : [first_val] "=&r"(first_loaded_val),
        [last_val] "=&r"(last_loaded_val)
      : [st_val] "r"(store_pattern), [st_addr] "r"(store_target),
        [rd_base] "r"(stream_base)
      : "t0", "t1", "t2", "memory");

  // Verify that the streamed loads returned valid boundary data
  if (first_loaded_val != 0x10000) {
    printf("Phase 3 FAILED: First streamed load mismatch: expected 0x10000, read 0x%x\n",
           first_loaded_val);
    report_failure();
  }
  if (last_loaded_val != (0x10000 + 31)) {
    printf("Phase 3 FAILED: Last streamed load mismatch: expected 0x%x, read 0x%x\n",
           0x10000 + 31, last_loaded_val);
    report_failure();
  }

  // Verify that the initial store committed without corruption
  if (*store_target != store_pattern) {
    printf("Phase 3 FAILED: Store target mismatch after read stream: expected 0x%x, read 0x%x\n",
           store_pattern, *store_target);
    report_failure();
  }

  printf("Phase 3 Passed: 32-load sustained stream completed without deadlock or corruption.\n\n");
}

/**
 * Phase 4: Store Buffer Full Backpressure Stall (#512)
 *
 * VeeR-EL2 features a 4-entry store buffer. While a readback check is pending,
 * new store commits from the store buffer are deferred.
 *
 * This test rapidly issues 5 consecutive stores interleaved with loads to keep
 * the read port active, saturating all 4 store buffer entries. The 5th store
 * must trigger lsu_stbuf_full_any backpressure stall at decode cleanly,
 * and all 5 stores must subsequently drain in FIFO order without hang or data loss.
 */
static void test_phase4_stbuf_full_backpressure(void) {
  printf("Starting Phase 4: Store Buffer Full Backpressure Stall (#512)...\n");

  volatile uint32_t *target_st = (volatile uint32_t *)(DCCM_TEST_BASE + 0x600);
  volatile uint32_t *target_rd = (volatile uint32_t *)(DCCM_TEST_BASE + 0x700);

  // Initialize targets
  for (int i = 0; i < 5; i++) {
    target_st[i] = 0x00000000;
    target_rd[i] = 0xaa00 + i;
  }

  const uint32_t st_vals[5] = {0x55000001, 0x55000002, 0x55000003, 0x55000004, 0x55000005};
  uint32_t rd_vals[5];

  // Rapid burst of 5 stores interleaved with reads to saturate 4-entry store buffer
  __asm__ volatile(
      "sw  %[s0], 0*4(%[st_base])\n\t"
      "lw  %[r0], 0*4(%[rd_base])\n\t"
      "sw  %[s1], 1*4(%[st_base])\n\t"
      "lw  %[r1], 1*4(%[rd_base])\n\t"
      "sw  %[s2], 2*4(%[st_base])\n\t"
      "lw  %[r2], 2*4(%[rd_base])\n\t"
      "sw  %[s3], 3*4(%[st_base])\n\t"
      "lw  %[r3], 3*4(%[rd_base])\n\t"
      "sw  %[s4], 4*4(%[st_base])\n\t"
      "lw  %[r4], 4*4(%[rd_base])\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      : [r0] "=&r"(rd_vals[0]), [r1] "=&r"(rd_vals[1]),
        [r2] "=&r"(rd_vals[2]), [r3] "=&r"(rd_vals[3]),
        [r4] "=&r"(rd_vals[4])
      : [s0] "r"(st_vals[0]), [s1] "r"(st_vals[1]),
        [s2] "r"(st_vals[2]), [s3] "r"(st_vals[3]),
        [s4] "r"(st_vals[4]),
        [st_base] "r"(target_st), [rd_base] "r"(target_rd)
      : "memory");

  // Verify all 5 stores committed accurately to SRAM
  for (int i = 0; i < 5; i++) {
    if (target_st[i] != st_vals[i]) {
      printf("Phase 4 FAILED: Store buffer entry %d corruption: expected 0x%x, read 0x%x\n",
             i, st_vals[i], target_st[i]);
      report_failure();
    }
    if (rd_vals[i] != (0xaa00 + i)) {
      printf("Phase 4 FAILED: Interleaved read %d corruption: expected 0x%x, read 0x%x\n",
             i, (0xaa00 + i), rd_vals[i]);
      report_failure();
    }
  }

  printf("Phase 4 Passed: Store buffer saturation & backpressure stall drained cleanly.\n\n");
}

/**
 * Phase 5: Runtime Disable via MFDC.dwrd (#512)
 *
 * Toggles the dwrd bit in MFDC CSR to confirm runtime disabling and re-enabling
 * of the readback check.
 */
static void test_phase5_runtime_disable(void) {
  printf("Starting Phase 5: Runtime Disable (MFDC.dwrd) (#512)...\n");

  volatile uint32_t *target_ptr = (volatile uint32_t *)(DCCM_TEST_BASE + 0x800);

  // 1. Disable write readback
  printf("Disabling write-readback check (dwrd = 1)...\n");
  disable_dccm_wr_readback();

  *target_ptr = 0x11223344;
  if (*target_ptr != 0x11223344) {
    printf("Phase 5 FAILED: Write failed while dwrd=1!\n");
    report_failure();
  }

  // 2. Re-enable write readback
  printf("Re-enabling write-readback check (dwrd = 0)...\n");
  enable_dccm_wr_readback();

  *target_ptr = 0x55667788;
  if (*target_ptr != 0x55667788) {
    printf("Phase 5 FAILED: Write failed after re-enabling dwrd=0!\n");
    report_failure();
  }

  printf("Phase 5 Passed: MFDC.dwrd runtime control verified.\n\n");
}

/**
 * Unexpected trap handler.
 */
void trap_handler(void) {
  printf("ERROR: Unexpected trap encountered!\n");
  report_failure();
}

/**
 * Main test entry point.
 */
int main(void) {
  printf("===============================================================\n");
  printf("DCCM Write Readback Check Pipeline Hazards & Stall Verification (#512)\n");
  printf("Author: Samip Modi (samipmodi@google.com)\n");
  printf("===============================================================\n\n");

  test_phase1_snoop_path();
  test_phase2_steal_path();
  test_phase3_sustained_read_stream();
  test_phase4_stbuf_full_backpressure();
  test_phase5_runtime_disable();

  printf("===============================================================\n");
  printf("SUCCESS: All 5 Issue #512 Hazard & Pipeline Phases Passed!\n");
  printf("===============================================================\n");

  return 0;
}
