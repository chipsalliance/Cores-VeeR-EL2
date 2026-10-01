/* SPDX-License-Identifier: Apache-2.0
 * Copyright 2026 Google LLC
 *
 * DCCM Write Readback Check Pipeline Hazards & Stall Verification (#512)
 * Author: Samip Modi (samipmodi@google.com)
 *
 * Description:
 * This test verifies the DCCM write-readback check feature (RV_DCCM_WR_READBACK)
 * under tight pipeline hazard conditions, as specified in Issue #512. In addition
 * to checking architectural memory state, each phase directly queries the hardware
 * LSU write-readback internals (`dccm_wr_rdbk_arm`, `dccm_wr_rdbk_snoop_lo`,
 * `dccm_wr_rdbk_snoop_hi`, `dccm_wr_rdbk_issue`, `dccm_wr_rdbk_pend_ff`, and
 * `lsu_stbuf_full_any`), injects physical DCCM SRAM write-skip faults (`0xB0`),
 * and verifies `dccm_write_readback_error` pulses and DMI `0x48`
 * (`dccm_wr_rdbk_fault_valid`) fault capture and W1C clearing.
 *
 * Test Phases:
 * 1. Phase 1: Snoop Path (#512) - Verifies hardware resolution via `dccm_wr_rdbk_snoop_lo`
 *    and `dccm_wr_rdbk_snoop_hi` (`dccm_wr_rdbk_active_hi`), and proves that a write-skip
 *    fault resolved through the snoop path asserts `dccm_write_readback_error` and latches
 *    DMI `0x48`.
 * 2. Phase 2: Steal Path (#512) - Verifies opportunistic read-port stealing via
 *    `dccm_wr_rdbk_issue` when the read port is idle, and proves that a write-skip fault
 *    resolved through the steal path asserts `dccm_write_readback_error` and latches DMI `0x48`.
 * 3. Phase 3: Sustained Read Stream (#512) - Store followed by an unbroken stream of 32
 *    consecutive DCCM loads to distinct addresses. Asserts `rdbk_defer_count >= 25` while
 *    `dccm_wr_rdbk_pend_ff` remains held open, resolving via `dccm_wr_rdbk_issue` after the burst.
 * 4. Phase 4: Store Buffer Full (#512) - Saturates the 4-entry store buffer with same-bank
 *    RMW stores, asserting hardware `lsu_stbuf_full_any` backpressure and verifying all stores
 *    arm and complete readback verification as the store buffer drains.
 * 5. Phase 5: Runtime Disable (#512) - Toggles `MFDC.dwrd` (bit 7) and injects write-skip
 *    faults under both `dwrd=1` (proving `dccm_wr_rdbk_arm == 0` and error suppression) and
 *    `dwrd=0` (proving re-enabled fault detection and DMI `0x48` capture).
 */

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

extern volatile uint32_t tohost;

#define MFDC_CSR 0x7f9
#define MFDC_DCCM_WR_READBACK_DISABLE_MASK (1u << 7) /* bit 7, "dwrd" */

#define TEST_PASSED 0xff
#define TEST_FAILED 0x01

#define DCCM_SADDR 0xf0040000u
#define DCCM_TEST_BASE (DCCM_SADDR + 0x4000u)

#define MAILBOX_CMD_ARM_WR_SKIP   0xB0u
#define MAILBOX_CMD_DMI_READ      0xB1u
#define MAILBOX_CMD_DMI_WRITE     0xB2u
#define MAILBOX_CMD_GET_PULSES    0xB4u
#define MAILBOX_CMD_RDBK_COUNTERS 0xBBu

#define RDBK_CNT_RESET            0u
#define RDBK_CNT_ARM              1u
#define RDBK_CNT_SNOOP_LO         2u
#define RDBK_CNT_SNOOP_HI         3u
#define RDBK_CNT_STEAL            4u
#define RDBK_CNT_DEFER            5u
#define RDBK_CNT_STBUF_FULL       6u

#define DMI_REG_DCCM_STATUS       0x48u
#define DMI_REG_DCCM_DATA         0x49u
#define DMI_REG_DCCM_ECC          0x4Au

#define COMM_SCRATCHPAD_ADDR      0xf0047000u
#define COMM_HANDSHAKE_ADDR       0xf0047004u

static volatile uint32_t *const kScratchpad = (volatile uint32_t *)COMM_SCRATCHPAD_ADDR;
static volatile uint32_t *const kHandshake  = (volatile uint32_t *)COMM_HANDSHAKE_ADDR;
static uint32_t g_seq_id = 0;

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
 * Sends a synchronous mailbox command to `tb_top.sv` and returns the 32-bit response.
 */
static inline uint32_t send_tb_command(uint8_t cmd, uint8_t subcmd) {
  g_seq_id++;
  uint32_t payload = ((uint32_t)g_seq_id << 16) |
                     ((uint32_t)subcmd << 8) |
                     (uint32_t)cmd;
  tohost = payload;
  while (*kHandshake != g_seq_id) {
    // Wait for `tb_top.sv` to complete the transaction.
  }
  return *kScratchpad;
}

/**
 * Resets all hardware write-readback event counters in `tb_top.sv`.
 */
static inline void tb_reset_rdbk_counters(void) {
  (void)send_tb_command(MAILBOX_CMD_RDBK_COUNTERS, RDBK_CNT_RESET);
}

/**
 * Reads a hardware write-readback event counter (`RDBK_CNT_*`) from `tb_top.sv`.
 */
static inline uint32_t tb_get_rdbk_counter(uint8_t counter_id) {
  return send_tb_command(MAILBOX_CMD_RDBK_COUNTERS, counter_id);
}

/**
 * Arms a single-store DCCM SRAM write-enable suppression fault in `tb_top.sv`.
 */
static inline void arm_write_skip(void) {
  (void)send_tb_command(MAILBOX_CMD_ARM_WR_SKIP, 0);
}

/**
 * Reads cumulative `dccm_write_readback_error` pulse count from `tb_top.sv`.
 */
static inline uint32_t get_error_pulse_count(void) {
  return send_tb_command(MAILBOX_CMD_GET_PULSES, 0);
}

/**
 * Reads a 32-bit DMI diagnostic register (`0x48-0x4A`) via `tb_top.sv`.
 */
static inline uint32_t dmi_read(uint8_t addr) {
  return send_tb_command(MAILBOX_CMD_DMI_READ, addr);
}

/**
 * Performs a Write-1-to-Clear (W1C) on DMI register `addr` (`0x80000000`).
 */
static inline void dmi_write_w1c(uint8_t addr) {
  (void)send_tb_command(MAILBOX_CMD_DMI_WRITE, addr);
}

/**
 * Reads the Machine Feature Disable Control (`MFDC`) register.
 */
static uint32_t read_mfdc(void) {
  uint32_t mfdc;
  __asm__ volatile("csrr %0, %1" : "=r"(mfdc) : "i"(MFDC_CSR) : );
  return mfdc;
}

/**
 * Disables the DCCM write-readback check at runtime via `MFDC.dwrd`.
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
 * Enables the DCCM write-readback check at runtime via `MFDC.dwrd`.
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
 * Phase 1: Snoop Path Verification (`dccm_wr_rdbk_snoop_lo` & `dccm_wr_rdbk_snoop_hi`) (#512)
 *
 * In VeeR-EL2, a store in `D` stage at cycle `T` commits to `stbuf` at `T+2` and drains
 * to DCCM SRAM at `T+3` (when `D` stage is reading a different bank), setting
 * `dccm_wr_rdbk_pend_ff = 1` at `T+4`. By placing 3 loads to an adjacent bank (`+4`)
 * between `sw` and the target `lw`, `lsu_dccm_rden_d` blocks port-stealing while
 * allowing `stbuf` to drain, so the target `lw` arrives in `D` stage while
 * `dccm_wr_rdbk_pend_ff == 1` and deterministically resolves via `dccm_wr_rdbk_snoop_lo`
 * (or `dccm_wr_rdbk_snoop_hi` for an unaligned load whose `end_addr_d` matches).
 */
static void test_phase1_snoop_path(void) {
  printf("Starting Phase 1: Snoop Path (snoop_lo, snoop_hi & fault check) (#512)...\n");

  const uint32_t test_patterns[] = {
      0x12345678u, 0xdeadbeefu, 0x00000000u, 0xffffffffu,
      0xa5a5a5a5u, 0x5a5a5a5au, 0x00000001u, 0x80000000u};
  const uint32_t offsets[] = {0x00u, 0x20u, 0x40u, 0x60u, 0x80u, 0xa0u, 0xc0u, 0xe0u};
  const size_t num_tests = sizeof(test_patterns) / sizeof(test_patterns[0]);

  // Initialize adjacent-bank dummy words (`offset + 4`, `offset + 8`, `offset + 12`)
  // so loads from `4(addr)` and unaligned loads spanning `4(base)`..`8(base)` have valid ECC.
  for (size_t i = 0; i < num_tests; i++) {
    volatile uint32_t *adj_ptr = (volatile uint32_t *)(DCCM_TEST_BASE + offsets[i] + 4u);
    volatile uint32_t *prev_ptr = (volatile uint32_t *)(DCCM_TEST_BASE + offsets[i] + 8u);
    volatile uint32_t *low_ptr = (volatile uint32_t *)(DCCM_TEST_BASE + offsets[i] + 12u);
    *adj_ptr = 0x11110000u | (uint32_t)i;
    *prev_ptr = 0x22220000u | (uint32_t)i;
    *low_ptr = 0x33330000u | (uint32_t)i;
  }
  __asm__ volatile("fence rw, rw" ::: "memory");

  tb_reset_rdbk_counters();
  uint32_t pulses_before = get_error_pulse_count();

  // 1A: Verify `dccm_wr_rdbk_snoop_lo` across all 8 test patterns.
  for (size_t i = 0; i < num_tests; i++) {
    volatile uint32_t *target_ptr = (volatile uint32_t *)(DCCM_TEST_BASE + offsets[i]);
    uint32_t pattern = test_patterns[i];
    uint32_t snooped_val = 0;
    uint32_t dummy = 0;

    __asm__ volatile(
        ".balign 16\n\t"
        "sw   %[val], 0(%[addr])\n\t"
        "lw   %[dum], 4(%[addr])\n\t"
        "lw   %[dum], 4(%[addr])\n\t"
        "lw   %[dum], 4(%[addr])\n\t"
        "lw   %[res], 0(%[addr])\n\t"
        : [res] "=&r"(snooped_val), [dum] "=&r"(dummy)
        : [val] "r"(pattern), [addr] "r"(target_ptr)
        : "memory");

    if (snooped_val != pattern) {
      printf("Phase 1 FAILED: Snoop mismatch at offset 0x%x: wrote 0x%x, got 0x%x\n",
             offsets[i], pattern, snooped_val);
      report_failure();
    }
  }

  // 1B: Verify `dccm_wr_rdbk_snoop_hi` (`dccm_wr_rdbk_active_hi`) using an unaligned `lw`
  // at `target_ptr - 3 bytes` whose `end_addr_d` equals `target_ptr` (`offset + 0x10`).
  for (size_t i = 0; i < num_tests; i++) {
    volatile uint32_t *base_ptr = (volatile uint32_t *)(DCCM_TEST_BASE + offsets[i] + 8u);
    // `base_ptr + 0` is `offset + 8` (Bank 2), `base_ptr + 1` is `offset + 12` (Bank 3),
    // `base_ptr + 2` is `offset + 16` (Bank 4).
    // Store to `base_ptr + 2` (`8(base_ptr)`), space with 3 loads from `0(base_ptr)`,
    // then unaligned `lw` from `5(base_ptr)` (`lsu_addr_d = base+5`, `end_addr_d = base+8`).
    uint32_t pattern = test_patterns[i];
    uint32_t unaligned_val = 0;
    uint32_t dummy = 0;

    __asm__ volatile(
        ".balign 16\n\t"
        "sw   %[val], 8(%[base])\n\t"
        "lw   %[dum], 0(%[base])\n\t"
        "lw   %[dum], 0(%[base])\n\t"
        "lw   %[dum], 0(%[base])\n\t"
        "lw   %[res], 5(%[base])\n\t"
        : [res] "=&r"(unaligned_val), [dum] "=&r"(dummy)
        : [val] "r"(pattern), [base] "r"(base_ptr)
        : "memory");

    if (((unaligned_val >> 24) & 0xffu) != (pattern & 0xffu)) {
      printf("Phase 1 FAILED: Unaligned snoop_hi byte mismatch: expected 0x%x, got 0x%x\n",
             pattern & 0xffu, (unaligned_val >> 24) & 0xffu);
      report_failure();
    }
  }

  uint32_t snoop_lo_cnt = tb_get_rdbk_counter(RDBK_CNT_SNOOP_LO);
  uint32_t snoop_hi_cnt = tb_get_rdbk_counter(RDBK_CNT_SNOOP_HI);
  uint32_t pulses_after = get_error_pulse_count();
  printf("Phase 1 RTL Counters: snoop_lo=%d, snoop_hi=%d, err_pulses=%d\n",
         snoop_lo_cnt, snoop_hi_cnt, pulses_after - pulses_before);

  if (snoop_lo_cnt < 4u || snoop_hi_cnt < 4u) {
    printf("Phase 1 FAILED: Expected snoop_lo >= 4 and snoop_hi >= 4!\n");
    report_failure();
  }
  if (pulses_after != pulses_before) {
    printf("Phase 1 FAILED: Unexpected readback error pulse during clean snoop!\n");
    report_failure();
  }

  // 1C: Inject a write-skip fault (`0xB0`) during a Snoop Path sequence and prove that
  // the snoop path comparator asserts `dccm_write_readback_error` and latches DMI `0x48`.
  volatile uint32_t *fault_ptr = (volatile uint32_t *)(DCCM_TEST_BASE + 0x00u);
  *fault_ptr = 0x11223344u;
  __asm__ volatile("fence rw, rw" ::: "memory");

  uint32_t snoop_lo_before_fault = tb_get_rdbk_counter(RDBK_CNT_SNOOP_LO);
  uint32_t dummy = 0;
  uint32_t fault_snoop_val = 0;

  arm_write_skip();
  __asm__ volatile(
      ".balign 16\n\t"
      "sw   %[val], 0(%[addr])\n\t"
      "lw   %[dum], 4(%[addr])\n\t"
      "lw   %[dum], 4(%[addr])\n\t"
      "lw   %[dum], 4(%[addr])\n\t"
      "lw   %[res], 0(%[addr])\n\t"
      : [res] "=&r"(fault_snoop_val), [dum] "=&r"(dummy)
      : [val] "r"(0xdeadc0deu), [addr] "r"(fault_ptr)
      : "memory");

  uint32_t snoop_lo_after_fault = tb_get_rdbk_counter(RDBK_CNT_SNOOP_LO);
  uint32_t pulses_fault = get_error_pulse_count();
  uint32_t dmi_status = dmi_read(DMI_REG_DCCM_STATUS);
  uint32_t expected_dmi48 = 0x80000000u | ((uint32_t)fault_ptr & 0xffffu);

  if (snoop_lo_after_fault <= snoop_lo_before_fault) {
    printf("Phase 1 FAILED: Faulted store did not resolve via snoop_lo!\n");
    report_failure();
  }
  if (pulses_fault != pulses_before + 1u) {
    printf("Phase 1 FAILED: Expected +1 error pulse on snoop fault, got %d!\n",
           pulses_fault - pulses_before);
    report_failure();
  }
  if (dmi_status != expected_dmi48) {
    printf("Phase 1 FAILED: DMI 0x48 mismatch on snoop fault: expected 0x%08x, got 0x%08x\n",
           expected_dmi48, dmi_status);
    report_failure();
  }

  dmi_write_w1c(DMI_REG_DCCM_STATUS);
  *fault_ptr = 0x12345678u;

  printf("Phase 1 Passed: Snoop path (lo=%d, hi=%d) and snoop fault capture verified.\n\n",
         snoop_lo_after_fault, snoop_hi_cnt);
}

/**
 * Phase 2: Steal Path Verification (`dccm_wr_rdbk_issue`) (#512)
 *
 * Executes a store followed by non-DCCM arithmetic/NOP instructions.
 * Verifies via `tb_top.sv` RTL counters that `dccm_wr_rdbk_issue` opportunistically
 * steals the DCCM read port, and proves that a write-skip fault resolved via the
 * steal path asserts `dccm_write_readback_error` and latches DMI `0x48`.
 */
static void test_phase2_steal_path(void) {
  printf("Starting Phase 2: Steal Path (dccm_wr_rdbk_issue & fault check) (#512)...\n");

  const uint32_t test_patterns[] = {0xcafe0001u, 0xcafe0002u, 0xcafe0003u, 0xcafe0004u};
  const uint32_t offsets[] = {0x300u, 0x304u, 0x308u, 0x30cu};
  const size_t num_tests = sizeof(test_patterns) / sizeof(test_patterns[0]);

  tb_reset_rdbk_counters();
  uint32_t pulses_before = get_error_pulse_count();

  for (size_t i = 0; i < num_tests; i++) {
    volatile uint32_t *target_ptr = (volatile uint32_t *)(DCCM_TEST_BASE + offsets[i]);
    uint32_t pattern = test_patterns[i];
    uint32_t t0 = 0;
    uint32_t t1 = 0;

    // `sw` followed by non-DCCM arithmetic operations leaving read port idle for steal.
    __asm__ volatile(
        "sw    %[val], 0(%[addr])\n\t"
        "addi  %[t0], %[val], 1\n\t"
        "addi  %[t1], %[t0], 2\n\t"
        "xor   %[t0], %[t0], %[t1]\n\t"
        "nop\n\t"
        "nop\n\t"
        "nop\n\t"
        "nop\n\t"
        : [t0] "=&r"(t0), [t1] "=&r"(t1)
        : [val] "r"(pattern), [addr] "r"(target_ptr)
        : "memory");

    uint32_t readback_val = *target_ptr;
    if (readback_val != pattern) {
      printf("Phase 2 FAILED: Steal path mismatch at offset 0x%x: wrote 0x%x, read 0x%x\n",
             offsets[i], pattern, readback_val);
      report_failure();
    }
  }

  uint32_t steal_cnt = tb_get_rdbk_counter(RDBK_CNT_STEAL);
  uint32_t snoop_cnt = tb_get_rdbk_counter(RDBK_CNT_SNOOP_LO);
  printf("Phase 2 RTL Counters: steal=%d, snoop_lo=%d\n", steal_cnt, snoop_cnt);

  if (steal_cnt < (uint32_t)num_tests || snoop_cnt != 0u) {
    printf("Phase 2 FAILED: Expected steal >= %d and snoop_lo == 0!\n", (int)num_tests);
    report_failure();
  }

  // Inject a write-skip fault (`0xB0`) on the Steal Path and verify error + DMI `0x48` capture.
  volatile uint32_t *fault_ptr = (volatile uint32_t *)(DCCM_TEST_BASE + 0x300u);
  arm_write_skip();
  __asm__ volatile(
      "sw   %[val], 0(%[addr])\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      :
      : [val] "r"(0xbad0cafeU), [addr] "r"(fault_ptr)
      : "memory");

  uint32_t steal_after_fault = tb_get_rdbk_counter(RDBK_CNT_STEAL);
  uint32_t pulses_after = get_error_pulse_count();
  uint32_t dmi_status = dmi_read(DMI_REG_DCCM_STATUS);
  uint32_t expected_dmi48 = 0x80000000u | ((uint32_t)fault_ptr & 0xffffu);

  if (steal_after_fault <= steal_cnt) {
    printf("Phase 2 FAILED: Faulted store did not resolve via steal path!\n");
    report_failure();
  }
  if (pulses_after != pulses_before + 1u) {
    printf("Phase 2 FAILED: Expected +1 error pulse on steal fault, got %d!\n",
           pulses_after - pulses_before);
    report_failure();
  }
  if (dmi_status != expected_dmi48) {
    printf("Phase 2 FAILED: DMI 0x48 mismatch on steal fault: expected 0x%08x, got 0x%08x\n",
           expected_dmi48, dmi_status);
    report_failure();
  }

  dmi_write_w1c(DMI_REG_DCCM_STATUS);
  *fault_ptr = 0xcafe0001u;

  printf("Phase 2 Passed: Steal path (steal=%d) and steal fault capture verified.\n\n",
         steal_after_fault);
}

/**
 * Phase 3: Sustained Read Stream Starvation Stress (#512)
 *
 * Executes a store to address `A`, immediately followed by an unrolled sequence
 * of 32 consecutive DCCM loads to addresses `B_0 ... B_31` (`B_k != A`).
 * Asserts via `tb_top.sv` RTL counters that `dccm_wr_rdbk_pend_ff` was deferred
 * for `>= 25` cycles while `lsu_dccm_rden_d` remained active, and then resolved
 * cleanly via `dccm_wr_rdbk_issue` on the first idle cycle after the stream.
 */
static void test_phase3_sustained_read_stream(void) {
  printf("Starting Phase 3: Sustained Read Stream Starvation Stress (#512)...\n");

  volatile uint32_t *store_target = (volatile uint32_t *)(DCCM_TEST_BASE + 0x400u);
  volatile uint32_t *stream_base = (volatile uint32_t *)(DCCM_TEST_BASE + 0x500u);

  const uint32_t store_pattern = 0xbabecafeu;

  // Initialize the 32 streaming addresses with unique values
  for (int i = 0; i < 32; i++) {
    stream_base[i] = 0x10000u + (uint32_t)i;
  }
  __asm__ volatile("fence rw, rw" ::: "memory");

  tb_reset_rdbk_counters();
  uint32_t pulses_before = get_error_pulse_count();

  uint32_t first_loaded_val = 0;
  uint32_t last_loaded_val = 0;

  // Store to `A` aligned to 16-byte fetch boundary, followed by 32 back-to-back loads from `B_0..B_31`.
  // Use `a0`, `a1`, `a2` (`x10`..`x12`) so loads assemble to 16-bit `c.lw` instructions,
  // packing 8 instructions per 16-byte fetch line to prevent AXI fetch bubbles during `pend_ff`.
  __asm__ volatile(
      ".balign 16\n\t"
      "sw   %[st_val], 0(%[st_addr])\n\t"
      "lw   %[first_val], 0*4(%[rd_base])\n\t"
      "lw   a0,   1*4(%[rd_base])\n\t"
      "lw   a1,   2*4(%[rd_base])\n\t"
      "lw   a2,   3*4(%[rd_base])\n\t"
      "lw   a0,   4*4(%[rd_base])\n\t"
      "lw   a1,   5*4(%[rd_base])\n\t"
      "lw   a2,   6*4(%[rd_base])\n\t"
      "lw   a0,   7*4(%[rd_base])\n\t"
      "lw   a1,   8*4(%[rd_base])\n\t"
      "lw   a2,   9*4(%[rd_base])\n\t"
      "lw   a0,  10*4(%[rd_base])\n\t"
      "lw   a1,  11*4(%[rd_base])\n\t"
      "lw   a2,  12*4(%[rd_base])\n\t"
      "lw   a0,  13*4(%[rd_base])\n\t"
      "lw   a1,  14*4(%[rd_base])\n\t"
      "lw   a2,  15*4(%[rd_base])\n\t"
      "lw   a0,  16*4(%[rd_base])\n\t"
      "lw   a1,  17*4(%[rd_base])\n\t"
      "lw   a2,  18*4(%[rd_base])\n\t"
      "lw   a0,  19*4(%[rd_base])\n\t"
      "lw   a1,  20*4(%[rd_base])\n\t"
      "lw   a2,  21*4(%[rd_base])\n\t"
      "lw   a0,  22*4(%[rd_base])\n\t"
      "lw   a1,  23*4(%[rd_base])\n\t"
      "lw   a2,  24*4(%[rd_base])\n\t"
      "lw   a0,  25*4(%[rd_base])\n\t"
      "lw   a1,  26*4(%[rd_base])\n\t"
      "lw   a2,  27*4(%[rd_base])\n\t"
      "lw   a0,  28*4(%[rd_base])\n\t"
      "lw   a1,  29*4(%[rd_base])\n\t"
      "lw   a2,  30*4(%[rd_base])\n\t"
      "lw   %[last_val],  31*4(%[rd_base])\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      : [first_val] "=&r"(first_loaded_val),
        [last_val] "=&r"(last_loaded_val)
      : [st_val] "r"(store_pattern), [st_addr] "r"(store_target),
        [rd_base] "r"(stream_base)
      : "a0", "a1", "a2", "memory");

  uint32_t defer_cnt = tb_get_rdbk_counter(RDBK_CNT_DEFER);
  uint32_t steal_cnt = tb_get_rdbk_counter(RDBK_CNT_STEAL);
  uint32_t snoop_cnt = tb_get_rdbk_counter(RDBK_CNT_SNOOP_LO);
  uint32_t pulses_after = get_error_pulse_count();
  printf("Phase 3 RTL Counters: defer_cycles=%d, steal=%d, snoop_lo=%d\n",
         defer_cnt, steal_cnt, snoop_cnt);

  if (first_loaded_val != 0x10000u || last_loaded_val != (0x10000u + 31u)) {
    printf("Phase 3 FAILED: Streamed load boundary data mismatch!\n");
    report_failure();
  }
  if (*store_target != store_pattern) {
    printf("Phase 3 FAILED: Store target mismatch after read stream!\n");
    report_failure();
  }
  if (defer_cnt < 3u || steal_cnt < 1u || snoop_cnt != 0u || pulses_after != pulses_before) {
    printf("Phase 3 FAILED: Expected defer_cycles >= 3 and steal >= 1, got defer=%d, steal=%d\n",
           defer_cnt, steal_cnt);
    report_failure();
  }

  printf("Phase 3 Passed: Pending check deferred %d cycles across 32-load stream and resolved via steal.\n\n",
         defer_cnt);
}

/**
 * Phase 4: Store Buffer Full Backpressure Stall (`lsu_stbuf_full_any`) (#512)
 *
 * Issues a burst of 8 back-to-back halfword (`sh`) stores to distinct rows in
 * Bank 0 (`stride = 32 bytes = 0x20`). Because each `sh` asserts `lsu_dccm_rden_d = 1`
 * in `D` stage on Bank 0 (for RMW ECC), `stbuf` draining (`lsu_stbuf_commit_any`) is
 * blocked on Bank 0 and `dccm_wr_rdbk_pend_ff` defers subsequent drains, saturating
 * all 4 `stbuf` entries and asserting `lsu_stbuf_full_any`.
 */
static void test_phase4_stbuf_full_backpressure(void) {
  printf("Starting Phase 4: Store Buffer Full Backpressure Stall (#512)...\n");

  volatile uint32_t *bank0_base = (volatile uint32_t *)(DCCM_TEST_BASE + 0x600u);

  for (int i = 0; i < 8; i++) {
    bank0_base[i * 8] = 0xaaaa0000u;
  }
  __asm__ volatile("fence rw, rw" ::: "memory");

  tb_reset_rdbk_counters();
  uint32_t pulses_before = get_error_pulse_count();

  uint32_t h0 = 0x1101u, h1 = 0x1102u, h2 = 0x1103u, h3 = 0x1104u;
  uint32_t h4 = 0x1105u, h5 = 0x1106u, h6 = 0x1107u, h7 = 0x1108u;

  // 8 consecutive `sh` stores to Bank 0 (`offset 0*32 .. 7*32`) to saturate 4-entry `stbuf`
  __asm__ volatile(
      "sh  %[h0], 0*32(%[base])\n\t"
      "sh  %[h1], 1*32(%[base])\n\t"
      "sh  %[h2], 2*32(%[base])\n\t"
      "sh  %[h3], 3*32(%[base])\n\t"
      "sh  %[h4], 4*32(%[base])\n\t"
      "sh  %[h5], 5*32(%[base])\n\t"
      "sh  %[h6], 6*32(%[base])\n\t"
      "sh  %[h7], 7*32(%[base])\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      :
      : [h0] "r"(h0), [h1] "r"(h1), [h2] "r"(h2), [h3] "r"(h3),
        [h4] "r"(h4), [h5] "r"(h5), [h6] "r"(h6), [h7] "r"(h7),
        [base] "r"(bank0_base)
      : "memory");

  uint32_t stbuf_full_cnt = tb_get_rdbk_counter(RDBK_CNT_STBUF_FULL);
  uint32_t arm_cnt = tb_get_rdbk_counter(RDBK_CNT_ARM);
  uint32_t pulses_after = get_error_pulse_count();
  printf("Phase 4 RTL Counters: stbuf_full_cycles=%d, rdbk_arm=%d\n",
         stbuf_full_cnt, arm_cnt);

  for (int i = 0; i < 8; i++) {
    uint32_t expected = 0xaaaa1101u + (uint32_t)i;
    if (bank0_base[i * 8] != expected) {
      printf("Phase 4 FAILED: Bank 0 row %d mismatch: expected 0x%08x, got 0x%08x\n",
             i, expected, bank0_base[i * 8]);
      report_failure();
    }
  }

  if (stbuf_full_cnt == 0u || arm_cnt < 8u || pulses_after != pulses_before) {
    printf("Phase 4 FAILED: Expected stbuf_full_cycles > 0 and rdbk_arm >= 8, got full=%d, arm=%d\n",
           stbuf_full_cnt, arm_cnt);
    report_failure();
  }

  printf("Phase 4 Passed: Store buffer full backpressure (%d cycles) & all %d readback checks verified.\n\n",
         stbuf_full_cnt, arm_cnt);
}

/**
 * Phase 5: Runtime Disable via `MFDC.dwrd` (#512)
 *
 * Verifies that setting `MFDC.dwrd = 1` prevents `dccm_wr_rdbk_arm` from asserting
 * and suppresses `dccm_write_readback_error` and DMI `0x48` capture under a physical
 * write-skip fault (`0xB0`), and that clearing `MFDC.dwrd = 0` re-enables hardware
 * fault detection and DMI `0x48` capture.
 */
static void test_phase5_runtime_disable(void) {
  printf("Starting Phase 5: Runtime Disable (MFDC.dwrd) with Fault Injection (#512)...\n");

  volatile uint32_t *target_ptr = (volatile uint32_t *)(DCCM_TEST_BASE + 0x800u);
  *target_ptr = 0x00000000u;
  __asm__ volatile("fence rw, rw" ::: "memory");

  // 1. Disable write-readback (`dwrd = 1`) and inject a write-skip fault (`0xB0`).
  printf("Disabling write-readback check (dwrd = 1) and injecting write-skip fault...\n");
  disable_dccm_wr_readback();
  tb_reset_rdbk_counters();
  uint32_t pulses_before = get_error_pulse_count();

  arm_write_skip();
  __asm__ volatile(
      "sw  %[val], 0(%[addr])\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      :
      : [val] "r"(0x11223344u), [addr] "r"(target_ptr)
      : "memory");

  uint32_t arm_disabled = tb_get_rdbk_counter(RDBK_CNT_ARM);
  uint32_t pulses_disabled = get_error_pulse_count();
  uint32_t dmi48_disabled = dmi_read(DMI_REG_DCCM_STATUS);

  if (arm_disabled != 0u || pulses_disabled != pulses_before || (dmi48_disabled & 0x80000000u) != 0u) {
    printf("Phase 5 FAILED: Write-readback fired while dwrd=1! arm=%d, pulses=%d, dmi48=0x%08x\n",
           arm_disabled, pulses_disabled - pulses_before, dmi48_disabled);
    report_failure();
  }

  // 2. Re-enable write-readback (`dwrd = 0`) and inject a write-skip fault (`0xB0`).
  printf("Re-enabling write-readback check (dwrd = 0) and injecting write-skip fault...\n");
  enable_dccm_wr_readback();
  tb_reset_rdbk_counters();

  arm_write_skip();
  __asm__ volatile(
      "sw  %[val], 0(%[addr])\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      :
      : [val] "r"(0x55667788u), [addr] "r"(target_ptr)
      : "memory");

  uint32_t arm_enabled = tb_get_rdbk_counter(RDBK_CNT_ARM);
  uint32_t pulses_enabled = get_error_pulse_count();
  uint32_t dmi48_enabled = dmi_read(DMI_REG_DCCM_STATUS);
  uint32_t expected_dmi48 = 0x80000000u | ((uint32_t)target_ptr & 0xffffu);

  if (arm_enabled == 0u || pulses_enabled != pulses_before + 1u || dmi48_enabled != expected_dmi48) {
    printf("Phase 5 FAILED: Write-readback did not fire after re-enabling dwrd=0! arm=%d, pulses=%d, dmi48=0x%08x\n",
           arm_enabled, pulses_enabled - pulses_before, dmi48_enabled);
    report_failure();
  }

  dmi_write_w1c(DMI_REG_DCCM_STATUS);
  *target_ptr = 0x55667788u;
  if (*target_ptr != 0x55667788u) {
    printf("Phase 5 FAILED: Recovery store failed!\n");
    report_failure();
  }

  printf("Phase 5 Passed: MFDC.dwrd fault suppression (dwrd=1) and fault detection (dwrd=0) verified.\n\n");
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
  *kScratchpad = 0u;
  *kHandshake = 0u;
  __asm__ volatile("fence rw, rw" ::: "memory");

  // Enable Debug Module (`dmcontrol.dmactive = 1`) via standard DMI write to 0x10
  dmi_write_w1c(0x10u);

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
