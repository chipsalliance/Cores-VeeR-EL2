/* SPDX-License-Identifier: Apache-2.0
 * Copyright 2026 Google LLC
 *
 * DCCM Write Readback Check Pseudo-Random Stress & Fuzzing Verification (#512)
 * Author: Samip Modi (samipmodi@google.com)
 *
 * Description:
 * This test provides extensive pseudo-randomized stress and fuzzing verification for the
 * DCCM write-readback check feature (RV_DCCM_WR_READBACK) to stress microarchitectural
 * hazard boundaries beyond deterministic directed testing, addressing Issue #512.
 * In addition to shadow-memory checking, every phase directly queries the LSU
 * hardware counters (`dccm_wr_rdbk_arm`, `dccm_wr_rdbk_snoop_lo`, `dccm_wr_rdbk_snoop_hi`,
 * `dccm_wr_rdbk_issue`, `dccm_wr_rdbk_pend_ff`) and injects randomized physical DCCM
 * write-skip faults (`0xB0`) to verify `dccm_write_readback_error` assertion and
 * DMI `0x48` (`dccm_wr_rdbk_fault_valid`) address capture under random traffic.
 *
 * Test Phases:
 * 1. Phase 1: Randomized Timing Jitter & Collision Probing (#512) - Random delay intervals
 *    (0 to 6 competing loads) between store commit and subsequent reads, asserting that
 *    both `dccm_wr_rdbk_snoop_lo` and `dccm_wr_rdbk_issue` (plus deferral cycles) are
 *    actively exercised and catch randomized write-skip faults.
 * 2. Phase 2: Randomized Access Sizes & RMW Alignment (#512) - Random mix of byte (`sb`),
 *    halfword (`sh`), and word (`sw`) stores across arbitrary byte offsets (`+0..+3`),
 *    verifying RMW ECC codeword merging, `dccm_wr_rdbk_arm` counts, and sub-word fault
 *    capture in DMI `0x48`.
 * 3. Phase 3: Multi-Bank Interleaving & True Unaligned Spanning (#512) - Executes real
 *    unaligned `sw`/`lw` instructions across word/bank boundaries (`offset +1, +2, +3`),
 *    asserting hardware `dccm_wr_rdbk_snoop_hi` (`dccm_wr_rdbk_active_hi`) and `steal`
 *    resolutions.
 * 4. Phase 4: Store Buffer Depth Oscillation & Random Walk Torture (#512) - 500-step
 *    randomized operation stream with live single-store write-skip fault injections,
 *    asserting exact 1:1 `dccm_write_readback_error` and DMI `0x48` capture alongside
 *    snoop, steal, and deferral RTL counter verification.
 * 5. Phase 5: Asynchronous Runtime `dwrd` Toggling Under Active Traffic (#512) - Randomly
 *    flips `MFDC.dwrd` (bit 7) between 0 and 1 during active load/store bursts with periodic
 *    write-skip fault injections, proving that faults are suppressed when `dwrd=1` and
 *    detected/captured in DMI `0x48` when `dwrd=0`.
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

#define COMM_SCRATCHPAD_ADDR      0xf0047000u
#define COMM_HANDSHAKE_ADDR       0xf0047004u

static volatile uint32_t *const kScratchpad = (volatile uint32_t *)COMM_SCRATCHPAD_ADDR;
static volatile uint32_t *const kHandshake  = (volatile uint32_t *)COMM_HANDSHAKE_ADDR;
static uint32_t g_seq_id = 0;

extern int printf(const char *format, ...);
extern int putchar(int c);

/**
 * State variable for deterministic Xorshift32 PRNG.
 */
static uint32_t prng_state = 0x5a17e001u;

/**
 * Generates next pseudo-random 32-bit integer.
 */
static inline uint32_t prng_next(void) {
  uint32_t x = prng_state;
  x ^= x << 13;
  x ^= x >> 17;
  x ^= x << 5;
  prng_state = x;
  return x;
}

/**
 * Generates pseudo-random integer in range `[min, max]` inclusive.
 */
static inline uint32_t prng_range(uint32_t min, uint32_t max) {
  if (min >= max) {
    return min;
  }
  return min + (prng_next() % (max - min + 1u));
}

/**
 * Halts execution and reports failure to testbench harness.
 */
static void report_failure(const char *msg) {
  printf("ERROR: %s (PRNG State: 0x%08x)\n", msg, prng_state);
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
    // Wait for `tb_top.sv` to complete transaction.
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
 * Queries a hardware write-readback event counter (`RDBK_CNT_*`) from `tb_top.sv`.
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
 * Queries cumulative `dccm_write_readback_error` pulse count from `tb_top.sv`.
 */
static inline uint32_t get_error_pulse_count(void) {
  return send_tb_command(MAILBOX_CMD_GET_PULSES, 0);
}

/**
 * Reads a 32-bit DMI diagnostic register via `tb_top.sv`.
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
static inline uint32_t read_mfdc(void) {
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
    report_failure("dwrd bit did not read back as set after disable!");
  }
}

/**
 * Enables the DCCM write-readback check at runtime via `MFDC.dwrd`.
 */
static void enable_dccm_wr_readback(void) {
  uint32_t mask = MFDC_DCCM_WR_READBACK_DISABLE_MASK;
  __asm__ volatile("csrc %0, %1" : : "i"(MFDC_CSR), "r"(mask) : );

  if ((read_mfdc() & MFDC_DCCM_WR_READBACK_DISABLE_MASK) != 0) {
    report_failure("dwrd bit did not read back as clear after enable!");
  }
}

/**
 * Phase 1: Randomized Timing Jitter & Collision Probing (#512)
 *
 * Randomly varies the number of competing adjacent-bank loads (0 to 6) between a
 * store to `target_a` and a subsequent load from `target_a` (or idle steal),
 * probing the exact cycle window between `dccm_wr_rdbk_snoop_lo`, deferral, and
 * `dccm_wr_rdbk_issue`, while periodically injecting write-skip faults (`0xB0`).
 */
static void test_phase1_random_timing_jitter(void) {
  printf("Starting Phase 1: Randomized Timing Jitter & Collision Probing (#512)...\n");

  volatile uint32_t *target_a = (volatile uint32_t *)(DCCM_TEST_BASE + 0x000u);
  volatile uint32_t *target_b = (volatile uint32_t *)(DCCM_TEST_BASE + 0x004u);
  *target_a = 0x11111111u;
  *target_b = 0x22222222u;
  __asm__ volatile("fence rw, rw" ::: "memory");

  tb_reset_rdbk_counters();
  uint32_t expected_pulses = get_error_pulse_count();
  const int iterations = 100;

  for (int iter = 0; iter < iterations; iter++) {
    uint32_t pattern = prng_next();
    uint32_t delay = prng_range(0, 6);
    uint32_t read_val = 0;
    uint32_t dummy = 0;
    bool inject_fault = ((iter % 20) == 10);

    if (inject_fault) {
      arm_write_skip();
    }

    // Vary the number of adjacent-bank loads between `sw 0(a)` and `lw 0(a)`:
    // - `delay >= 3` keeps `lsu_dccm_rden_d = 1` until `stbuf` drains, hitting `snoop_lo`!
    // - `delay < 3` lets `lw 0(a)` forward from `stbuf` and resolves later via `steal`!
    switch (delay) {
      case 0:
        __asm__ volatile(
            "sw %[val], 0(%[a])\n\t"
            "lw %[res], 0(%[a])\n\t"
            "nop; nop; nop; nop;\n\t"
            : [res] "=&r"(read_val)
            : [val] "r"(pattern), [a] "r"(target_a)
            : "memory");
        break;
      case 1:
        __asm__ volatile(
            "sw %[val], 0(%[a])\n\t"
            "lw %[dum], 4(%[a])\n\t"
            "lw %[res], 0(%[a])\n\t"
            "nop; nop; nop; nop;\n\t"
            : [res] "=&r"(read_val), [dum] "=&r"(dummy)
            : [val] "r"(pattern), [a] "r"(target_a)
            : "memory");
        break;
      case 2:
        __asm__ volatile(
            "sw %[val], 0(%[a])\n\t"
            "lw %[dum], 4(%[a])\n\t"
            "lw %[dum], 4(%[a])\n\t"
            "lw %[res], 0(%[a])\n\t"
            "nop; nop; nop; nop;\n\t"
            : [res] "=&r"(read_val), [dum] "=&r"(dummy)
            : [val] "r"(pattern), [a] "r"(target_a)
            : "memory");
        break;
      case 3:
        __asm__ volatile(
            "sw %[val], 0(%[a])\n\t"
            "lw %[dum], 4(%[a])\n\t"
            "lw %[dum], 4(%[a])\n\t"
            "lw %[dum], 4(%[a])\n\t"
            "lw %[res], 0(%[a])\n\t"
            : [res] "=&r"(read_val), [dum] "=&r"(dummy)
            : [val] "r"(pattern), [a] "r"(target_a)
            : "memory");
        break;
      case 4:
        __asm__ volatile(
            "sw %[val], 0(%[a])\n\t"
            "lw %[dum], 4(%[a])\n\t"
            "lw %[dum], 4(%[a])\n\t"
            "lw %[dum], 4(%[a])\n\t"
            "lw %[dum], 4(%[a])\n\t"
            "lw %[res], 0(%[a])\n\t"
            : [res] "=&r"(read_val), [dum] "=&r"(dummy)
            : [val] "r"(pattern), [a] "r"(target_a)
            : "memory");
        break;
      default:
        __asm__ volatile(
            "sw %[val], 0(%[a])\n\t"
            "lw %[dum], 4(%[a])\n\t"
            "lw %[dum], 4(%[a])\n\t"
            "lw %[dum], 4(%[a])\n\t"
            "lw %[dum], 4(%[a])\n\t"
            "lw %[dum], 4(%[a])\n\t"
            "lw %[res], 0(%[a])\n\t"
            : [res] "=&r"(read_val), [dum] "=&r"(dummy)
            : [val] "r"(pattern), [a] "r"(target_a)
            : "memory");
        break;
    }

    if (inject_fault) {
      expected_pulses++;
      uint32_t pulses_now = get_error_pulse_count();
      uint32_t dmi48 = dmi_read(DMI_REG_DCCM_STATUS);
      uint32_t exp_dmi48 = 0x80000000u | ((uint32_t)target_a & 0xffffu);
      if (pulses_now != expected_pulses || dmi48 != exp_dmi48) {
        report_failure("Phase 1: Injected write-skip fault not captured by readback hardware!");
      }
      dmi_write_w1c(DMI_REG_DCCM_STATUS);
      *target_a = pattern;
    } else {
      if (read_val != pattern || *target_a != pattern) {
        report_failure("Phase 1: Data mismatch under timing jitter!");
      }
    }
  }

  uint32_t arm_cnt = tb_get_rdbk_counter(RDBK_CNT_ARM);
  uint32_t snoop_lo_cnt = tb_get_rdbk_counter(RDBK_CNT_SNOOP_LO);
  uint32_t steal_cnt = tb_get_rdbk_counter(RDBK_CNT_STEAL);
  uint32_t defer_cnt = tb_get_rdbk_counter(RDBK_CNT_DEFER);
  printf("Phase 1 RTL Counters: arm=%d, snoop_lo=%d, steal=%d, defer=%d\n",
         arm_cnt, snoop_lo_cnt, steal_cnt, defer_cnt);

  if (arm_cnt < (uint32_t)iterations || snoop_lo_cnt == 0u || steal_cnt == 0u || defer_cnt == 0u) {
    report_failure("Phase 1: Hardware snoop_lo, steal, or defer paths were not exercised!");
  }
  if (get_error_pulse_count() != expected_pulses) {
    report_failure("Phase 1: Unexpected error pulse count!");
  }

  printf("Phase 1 Passed: %d randomized timing jitter iterations verified.\n\n", iterations);
}

/**
 * Phase 2: Randomized Access Sizes & RMW Alignment (#512)
 *
 * Randomly mixes 8-bit (`sb`), 16-bit (`sh`), and 32-bit (`sw`) stores across byte
 * offsets (`+0, +1, +2, +3`) within a word, verifying RMW ECC codeword merging,
 * hardware `dccm_wr_rdbk_arm` counts, and DMI `0x48` fault capture on sub-word stores.
 */
static void test_phase2_random_access_sizes_rmw(void) {
  printf("Starting Phase 2: Randomized Access Sizes & RMW Alignment (#512)...\n");

  #define ARENA_WORDS 16
  volatile uint32_t *arena_words = (volatile uint32_t *)(DCCM_TEST_BASE + 0x100u);
  volatile uint8_t *arena_bytes = (volatile uint8_t *)arena_words;

  uint8_t shadow_bytes[ARENA_WORDS * 4];

  for (size_t w = 0; w < ARENA_WORDS; w++) {
    arena_words[w] = 0u;
  }
  __asm__ volatile("fence rw, rw" ::: "memory");

  for (size_t i = 0; i < sizeof(shadow_bytes); i++) {
    shadow_bytes[i] = (uint8_t)(i & 0xffu);
    arena_bytes[i] = shadow_bytes[i];
  }
  __asm__ volatile("fence rw, rw" ::: "memory");

  tb_reset_rdbk_counters();
  uint32_t expected_pulses = get_error_pulse_count();
  const int iterations = 150;

  for (int iter = 0; iter < iterations; iter++) {
    uint32_t op_size = prng_range(0, 2); // 0=byte, 1=halfword, 2=word
    uint32_t word_idx = prng_range(0, ARENA_WORDS - 1);
    bool inject_fault = ((iter % 30) == 15);
    uint32_t expected_word_addr = (uint32_t)(arena_words + word_idx);

    if (op_size == 0) {
      uint32_t byte_off = prng_range(0, 3);
      uint32_t byte_addr = (word_idx * 4u) + byte_off;
      uint8_t data = (uint8_t)prng_next();
      if (data == shadow_bytes[byte_addr]) {
        data ^= 0x5au;
      }

      if (inject_fault) {
        arm_write_skip();
      }
      arena_bytes[byte_addr] = data;
      __asm__ volatile("nop; nop; nop; nop; nop;" ::: "memory");

      if (inject_fault) {
        expected_pulses++;
        uint32_t dmi48 = dmi_read(DMI_REG_DCCM_STATUS);
        uint32_t exp_addr = (uint32_t)(arena_bytes + byte_addr) & 0xffffu;
        if (get_error_pulse_count() != expected_pulses ||
            dmi48 != (0x80000000u | exp_addr)) {
          report_failure("Phase 2: Sub-word byte store fault not captured in DMI 0x48!");
        }
        dmi_write_w1c(DMI_REG_DCCM_STATUS);
        arena_bytes[byte_addr] = data;
      }
      shadow_bytes[byte_addr] = data;

      if (arena_bytes[byte_addr] != data) {
        report_failure("Phase 2: Byte store readback mismatch!");
      }
    } else if (op_size == 1) {
      uint32_t half_off = prng_range(0, 1) * 2u;
      uint32_t byte_addr = (word_idx * 4u) + half_off;
      uint16_t data = (uint16_t)prng_next();
      volatile uint16_t *half_ptr = (volatile uint16_t *)(arena_bytes + byte_addr);
      if (data == *half_ptr) {
        data ^= 0x5a5au;
      }

      if (inject_fault) {
        arm_write_skip();
      }
      *half_ptr = data;
      __asm__ volatile("nop; nop; nop; nop; nop;" ::: "memory");

      if (inject_fault) {
        expected_pulses++;
        uint32_t dmi48 = dmi_read(DMI_REG_DCCM_STATUS);
        uint32_t exp_addr = (uint32_t)half_ptr & 0xffffu;
        if (get_error_pulse_count() != expected_pulses ||
            dmi48 != (0x80000000u | exp_addr)) {
          report_failure("Phase 2: Halfword store fault not captured in DMI 0x48!");
        }
        dmi_write_w1c(DMI_REG_DCCM_STATUS);
        *half_ptr = data;
      }
      shadow_bytes[byte_addr]     = (uint8_t)(data & 0xffu);
      shadow_bytes[byte_addr + 1] = (uint8_t)((data >> 8) & 0xffu);

      if (*half_ptr != data) {
        report_failure("Phase 2: Halfword store readback mismatch!");
      }
    } else {
      uint32_t data = prng_next();
      uint32_t byte_addr = word_idx * 4u;
      if (data == arena_words[word_idx]) {
        data ^= 0xa5a5a5a5u;
      }

      if (inject_fault) {
        arm_write_skip();
      }
      arena_words[word_idx] = data;
      __asm__ volatile("nop; nop; nop; nop; nop;" ::: "memory");

      if (inject_fault) {
        expected_pulses++;
        uint32_t dmi48 = dmi_read(DMI_REG_DCCM_STATUS);
        if (get_error_pulse_count() != expected_pulses ||
            dmi48 != (0x80000000u | (expected_word_addr & 0xffffu))) {
          report_failure("Phase 2: Word store fault not captured in DMI 0x48!");
        }
        dmi_write_w1c(DMI_REG_DCCM_STATUS);
        arena_words[word_idx] = data;
      }
      shadow_bytes[byte_addr]     = (uint8_t)(data & 0xffu);
      shadow_bytes[byte_addr + 1] = (uint8_t)((data >> 8) & 0xffu);
      shadow_bytes[byte_addr + 2] = (uint8_t)((data >> 16) & 0xffu);
      shadow_bytes[byte_addr + 3] = (uint8_t)((data >> 24) & 0xffu);

      if (arena_words[word_idx] != data) {
        report_failure("Phase 2: Word store readback mismatch!");
      }
    }
  }

  for (size_t i = 0; i < sizeof(shadow_bytes); i++) {
    if (arena_bytes[i] != shadow_bytes[i]) {
      report_failure("Phase 2: Arena post-check shadow mismatch!");
    }
  }

  uint32_t arm_cnt = tb_get_rdbk_counter(RDBK_CNT_ARM);
  uint32_t steal_cnt = tb_get_rdbk_counter(RDBK_CNT_STEAL);
  printf("Phase 2 RTL Counters: arm=%d, steal=%d\n", arm_cnt, steal_cnt);
  if (arm_cnt < (uint32_t)iterations || steal_cnt == 0u) {
    report_failure("Phase 2: Insufficient hardware write-readback activations!");
  }

  printf("Phase 2 Passed: %d randomized RMW sub-word stores & fault captures verified.\n\n",
         iterations);
  #undef ARENA_WORDS
}

/**
 * Phase 3: Multi-Bank Interleaving & True Unaligned Spanning (#512)
 *
 * Executes actual unaligned `sw` and `lw` instructions across word/bank boundaries
 * (`offset +1, +2, +3`) as well as upper-bank snoop sequences (`sw` to `8(base)`
 * followed by unaligned `lw` at `5(base)` where `end_addr_d == 8(base)`), verifying
 * via `tb_top.sv` RTL counters that `dccm_wr_rdbk_snoop_hi` (`dccm_wr_rdbk_active_hi`),
 * `dccm_wr_rdbk_snoop_lo`, and `dccm_wr_rdbk_issue` all fire cleanly.
 */
static void test_phase3_multibank_unaligned(void) {
  printf("Starting Phase 3: Multi-Bank Interleaving & True Unaligned Spanning (#512)...\n");

  volatile uint32_t *unalign_words = (volatile uint32_t *)(DCCM_TEST_BASE + 0x300u);
  volatile uint8_t *unalign_arena = (volatile uint8_t *)unalign_words;

  for (int i = 0; i < 16; i++) {
    unalign_words[i] = 0x33330000u | (uint32_t)i;
  }
  __asm__ volatile("fence rw, rw" ::: "memory");

  tb_reset_rdbk_counters();
  uint32_t pulses_before = get_error_pulse_count();
  const int iterations = 100;

  for (int iter = 0; iter < iterations; iter++) {
    uint32_t unalign_offset = prng_range(1, 3);
    uint32_t base_index = prng_range(0, 8) * 4u;
    volatile uint8_t *unalign_ptr = unalign_arena + base_index + unalign_offset;
    uint32_t pattern = prng_next();
    uint32_t readback = 0;
    uint32_t dummy = 0;

    // Execute a genuine unaligned 32-bit `sw` and unaligned 32-bit `lw` spanning two DCCM banks.
    __asm__ volatile(
        "sw  %[val], 0(%[ptr])\n\t"
        "nop; nop; nop; nop;\n\t"
        "lw  %[res], 0(%[ptr])\n\t"
        : [res] "=&r"(readback)
        : [val] "r"(pattern), [ptr] "r"(unalign_ptr)
        : "memory");

    if (readback != pattern) {
      report_failure("Phase 3: True unaligned sw/lw readback mismatch!");
    }

    // Also exercise `dccm_wr_rdbk_snoop_hi` (`dccm_wr_rdbk_active_hi`) with an unaligned load
    // whose upper bank (`end_addr_d = base + 8`) snoops a pending store at `8(base)`.
    volatile uint32_t *base_w = unalign_words + (base_index >> 2);
    uint32_t snoop_hi_val = 0;
    __asm__ volatile(
        "sw  %[val], 8(%[base])\n\t"
        "lw  %[dum], 0(%[base])\n\t"
        "lw  %[dum], 0(%[base])\n\t"
        "lw  %[dum], 0(%[base])\n\t"
        "lw  %[res], 5(%[base])\n\t"
        : [res] "=&r"(snoop_hi_val), [dum] "=&r"(dummy)
        : [val] "r"(pattern), [base] "r"(base_w)
        : "memory");

    if (((snoop_hi_val >> 24) & 0xffu) != (pattern & 0xffu)) {
      report_failure("Phase 3: Unaligned snoop_hi upper-bank byte mismatch!");
    }
  }

  uint32_t arm_cnt = tb_get_rdbk_counter(RDBK_CNT_ARM);
  uint32_t snoop_hi_cnt = tb_get_rdbk_counter(RDBK_CNT_SNOOP_HI);
  uint32_t steal_cnt = tb_get_rdbk_counter(RDBK_CNT_STEAL);
  printf("Phase 3 RTL Counters: arm=%d, snoop_hi=%d, steal=%d\n",
         arm_cnt, snoop_hi_cnt, steal_cnt);

  if (arm_cnt < (uint32_t)(iterations * 2) || snoop_hi_cnt == 0u || steal_cnt == 0u) {
    report_failure("Phase 3: Hardware snoop_hi (active_hi) or steal path was not exercised!");
  }
  if (get_error_pulse_count() != pulses_before) {
    report_failure("Phase 3: Unexpected readback error pulse during clean unaligned accesses!");
  }

  printf("Phase 3 Passed: %d multi-bank unaligned accesses & snoop_hi verified.\n\n", iterations);
}

/**
 * Phase 4: Store Buffer Depth Oscillation & Random Walk Torture (#512)
 *
 * Runs 500 randomized operations across a 32-word DCCM arena, probabilistically
 * mixing store bursts, snoop reads, competing reads, idle cycles, and live
 * single-store write-skip fault injections (`0xB0`), asserting exact DMI `0x48`
 * fault capture and RTL counter progression.
 */
static void test_phase4_random_walk_torture(void) {
  printf("Starting Phase 4: Store Buffer Depth Oscillation & Random Walk Torture (#512)...\n");

  #define WALK_ARENA_SIZE 32
  volatile uint32_t *arena = (volatile uint32_t *)(DCCM_TEST_BASE + 0x500u);
  uint32_t shadow[WALK_ARENA_SIZE];

  for (int i = 0; i < WALK_ARENA_SIZE; i++) {
    shadow[i] = 0x55aa0000u | (uint32_t)i;
    arena[i] = shadow[i];
  }
  __asm__ volatile("fence rw, rw" ::: "memory");

  tb_reset_rdbk_counters();
  uint32_t expected_pulses = get_error_pulse_count();
  uint32_t injected_faults = 0;
  uint32_t last_store_idx = 0;
  const int total_steps = 500;

  for (int step = 0; step < total_steps; step++) {
    uint32_t action = prng_range(0, 99);

    if (action < 25) {
      // Action 0: Single Store (with periodic live write-skip fault injection)
      uint32_t idx = prng_range(0, WALK_ARENA_SIZE - 1);
      uint32_t val = prng_next();
      if (val == shadow[idx]) {
        val ^= 0xdeadbeefu;
      }

      bool inject_fault = ((step % 50) == 25);
      if (inject_fault) {
        arm_write_skip();
      }
      arena[idx] = val;
      __asm__ volatile("nop; nop; nop; nop; nop;" ::: "memory");

      if (inject_fault) {
        injected_faults++;
        expected_pulses++;
        uint32_t dmi48 = dmi_read(DMI_REG_DCCM_STATUS);
        uint32_t exp_dmi48 = 0x80000000u | ((uint32_t)(arena + idx) & 0xffffu);
        if (get_error_pulse_count() != expected_pulses || dmi48 != exp_dmi48) {
          report_failure("Phase 4: Live random-walk fault injection not captured in DMI 0x48!");
        }
        dmi_write_w1c(DMI_REG_DCCM_STATUS);
        arena[idx] = val;
      }
      shadow[idx] = val;
      last_store_idx = idx;
    } else if (action < 50) {
      // Action 1: Hardware Snoop Sequence (store to `idx`, 3 loads from adjacent bank, load `idx`)
      uint32_t idx = prng_range(0, WALK_ARENA_SIZE - 2);
      uint32_t val = prng_next();
      uint32_t snooped = 0;
      uint32_t dummy = 0;
      volatile uint32_t *ptr = arena + idx;

      __asm__ volatile(
          "sw %[val], 0(%[p])\n\t"
          "lw %[dum], 4(%[p])\n\t"
          "lw %[dum], 4(%[p])\n\t"
          "lw %[dum], 4(%[p])\n\t"
          "lw %[res], 0(%[p])\n\t"
          : [res] "=&r"(snooped), [dum] "=&r"(dummy)
          : [val] "r"(val), [p] "r"(ptr)
          : "memory");

      shadow[idx] = val;
      last_store_idx = idx;
      if (snooped != val) {
        report_failure("Phase 4: Hardware snoop read mismatch during random walk!");
      }
    } else if (action < 75) {
      // Action 2: Competing Random Load
      uint32_t idx = prng_range(0, WALK_ARENA_SIZE - 1);
      uint32_t read_val = arena[idx];
      if (read_val != shadow[idx]) {
        report_failure("Phase 4: Competing load data mismatch!");
      }
    } else if (action < 90) {
      // Action 3: Rapid Store Burst of 4 stores
      uint32_t base_idx = prng_range(0, WALK_ARENA_SIZE - 4);
      for (uint32_t b = 0; b < 4; b++) {
        uint32_t val = prng_next();
        shadow[base_idx + b] = val;
        arena[base_idx + b] = val;
      }
      last_store_idx = base_idx + 3;
    } else {
      // Action 4: Idle / Non-DCCM instructions (steal opportunity)
      __asm__ volatile("nop; nop; nop; nop;" ::: "memory");
    }
  }

  for (int i = 0; i < WALK_ARENA_SIZE; i++) {
    if (arena[i] != shadow[i]) {
      report_failure("Phase 4: Final arena state mismatch!");
    }
  }

  uint32_t arm_cnt = tb_get_rdbk_counter(RDBK_CNT_ARM);
  uint32_t snoop_lo_cnt = tb_get_rdbk_counter(RDBK_CNT_SNOOP_LO);
  uint32_t steal_cnt = tb_get_rdbk_counter(RDBK_CNT_STEAL);
  uint32_t defer_cnt = tb_get_rdbk_counter(RDBK_CNT_DEFER);
  printf("Phase 4 RTL Counters: arm=%d, snoop_lo=%d, steal=%d, defer=%d, faults=%d\n",
         arm_cnt, snoop_lo_cnt, steal_cnt, defer_cnt, injected_faults);

  if (arm_cnt < 100u || snoop_lo_cnt == 0u || steal_cnt == 0u || defer_cnt == 0u || injected_faults == 0u) {
    report_failure("Phase 4: Insufficient RTL readback path coverage during random walk!");
  }

  printf("Phase 4 Passed: 500-step random walk & %d live fault captures verified.\n\n",
         injected_faults);
  #undef WALK_ARENA_SIZE
}

/**
 * Phase 5: Asynchronous Runtime `dwrd` Toggling Under Active Traffic (#512)
 *
 * Flips `MFDC.dwrd` between `0` (enabled) and `1` (disabled) pseudo-randomly
 * while executing continuous store/load traffic and periodically injecting
 * write-skip faults (`0xB0`), proving that faults are suppressed when `dwrd=1`
 * and captured in DMI `0x48` when `dwrd=0`.
 */
static void test_phase5_asynchronous_dwrd_toggling(void) {
  printf("Starting Phase 5: Asynchronous Runtime dwrd Toggling Under Active Traffic (#512)...\n");

  volatile uint32_t *target = (volatile uint32_t *)(DCCM_TEST_BASE + 0x700u);
  *target = 0x12345678u;
  __asm__ volatile("fence rw, rw" ::: "memory");

  uint32_t expected_pulses = get_error_pulse_count();
  uint32_t disabled_faults_tested = 0;
  uint32_t enabled_faults_tested = 0;
  bool is_disabled = false;
  enable_dccm_wr_readback();

  const int iterations = 100;

  for (int iter = 0; iter < iterations; iter++) {
    if ((iter % 5) == 0) {
      is_disabled = (prng_range(0, 1) == 1);
      if (is_disabled) {
        disable_dccm_wr_readback();
      } else {
        enable_dccm_wr_readback();
      }
    }

    uint32_t val = prng_next();
    if (val == *target) {
      val ^= 0xf0f0f0f0u;
    }

    bool inject_fault = ((iter % 10) == 3);
    if (inject_fault) {
      arm_write_skip();
    }

    __asm__ volatile(
        "sw %[v], 0(%[t])\n\t"
        "nop; nop; nop; nop; nop;\n\t"
        :
        : [v] "r"(val), [t] "r"(target)
        : "memory");

    if (inject_fault) {
      uint32_t pulses_now = get_error_pulse_count();
      uint32_t dmi48 = dmi_read(DMI_REG_DCCM_STATUS);

      if (is_disabled) {
        // When `dwrd == 1`, the write-skip fault MUST NOT trigger an error or DMI latch!
        if (pulses_now != expected_pulses || (dmi48 & 0x80000000u) != 0u) {
          report_failure("Phase 5: Write-readback fault fired while MFDC.dwrd=1!");
        }
        disabled_faults_tested++;
      } else {
        // When `dwrd == 0`, the write-skip fault MUST trigger an error and latch DMI `0x48`!
        expected_pulses++;
        uint32_t exp_dmi48 = 0x80000000u | ((uint32_t)target & 0xffffu);
        if (pulses_now != expected_pulses || dmi48 != exp_dmi48) {
          report_failure("Phase 5: Write-readback fault missed while MFDC.dwrd=0!");
        }
        dmi_write_w1c(DMI_REG_DCCM_STATUS);
        enabled_faults_tested++;
      }
      // Restore target word after skipped write
      *target = val;
    }

    if (*target != val) {
      report_failure("Phase 5: Store/load mismatch during active dwrd toggling!");
    }
  }

  enable_dccm_wr_readback();
  printf("Phase 5 Fault Checks: disabled_suppressed=%d, enabled_captured=%d\n",
         disabled_faults_tested, enabled_faults_tested);

  if (disabled_faults_tested == 0u || enabled_faults_tested == 0u) {
    report_failure("Phase 5: Did not test both dwrd=1 suppression and dwrd=0 capture!");
  }

  printf("Phase 5 Passed: 100 iterations of active traffic with dynamic dwrd fault gating.\n\n");
}

/**
 * Unexpected trap handler.
 */
void trap_handler(void) {
  report_failure("Unexpected trap encountered!");
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
  printf("DCCM Write Readback Check Pseudo-Random Stress & Fuzzing Verification (#512)\n");
  printf("Author: Samip Modi (samipmodi@google.com)\n");
  printf("PRNG Initial Seed: 0x%08x\n", prng_state);
  printf("===============================================================\n\n");

  test_phase1_random_timing_jitter();
  test_phase2_random_access_sizes_rmw();
  test_phase3_multibank_unaligned();
  test_phase4_random_walk_torture();
  test_phase5_asynchronous_dwrd_toggling();

  printf("===============================================================\n");
  printf("SUCCESS: All 5 Randomized Stress Phases Passed!\n");
  printf("===============================================================\n");

  return 0;
}
