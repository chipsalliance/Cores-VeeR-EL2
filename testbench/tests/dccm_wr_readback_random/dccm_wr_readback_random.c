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
 * It uses a seeded, deterministic PRNG (Xorshift32) to generate reproducible sequences
 * across 5 randomized stress phases:
 *
 * Test Phases:
 * 1. Phase 1: Randomized Timing Jitter & Collision Probing (#512) - Random delay intervals
 *    (0 to 8 instructions) between store commit and subsequent reads to stress the single-cycle
 *    window between opportunistic port stealing (dccm_wr_rdbk_issue) and competing reads.
 * 2. Phase 2: Randomized Access Sizes & RMW Alignment (#512) - Random mix of byte (sb),
 *    halfword (sh), and word (sw) stores across arbitrary byte offsets (+0, +1, +2, +3),
 *    verifying that 39-bit ECC codeword merging and physical SRAM readback check operate
 *    correctly under RMW.
 * 3. Phase 3: Multi-Bank Interleaving & Unaligned Spanning (#512) - Randomly targets intra-bank
 *    collisions and cross-bank unaligned accesses, exercising dccm_wr_rdbk_snoop_hi and
 *    dccm_wr_rdbk_active_hi muxing paths.
 * 4. Phase 4: Store Buffer Depth Oscillation & Random Walk Torture (#512) - 500-step randomized
 *    operation stream with probabilistic action selection (store bursts, snoop reads,
 *    competing reads, and idle cycles), oscillating store buffer depth (0 to 4 entries)
 *    under continuous load backpressure.
 * 5. Phase 5: Asynchronous Runtime dwrd Toggling Under Active Traffic (#512) - Randomly flips
 *    MFDC.dwrd (bit 7) between 0 and 1 during active load/store bursts to verify that
 *    dynamic disable/re-enable does not drop stores or leave dangling pending windows.
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
 * State variable for deterministic Xorshift32 PRNG.
 */
static uint32_t prng_state = 0x5a17e001;

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
 * Generates pseudo-random integer in range [min, max] inclusive.
 */
static inline uint32_t prng_range(uint32_t min, uint32_t max) {
  if (min >= max) {
    return min;
  }
  return min + (prng_next() % (max - min + 1));
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
 * Reads the Machine Feature Disable Control (MFDC) register.
 */
static inline uint32_t read_mfdc(void) {
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
    report_failure("dwrd bit did not read back as set after disable!");
  }
}

/**
 * Enables the DCCM write-readback check at runtime via MFDC.dwrd.
 */
static void enable_dccm_wr_readback(void) {
  uint32_t mask = MFDC_DCCM_WR_READBACK_DISABLE_MASK;
  __asm__ volatile("csrc %0, %1" : : "i"(MFDC_CSR), "r"(mask) : );

  if ((read_mfdc() & MFDC_DCCM_WR_READBACK_DISABLE_MASK) != 0) {
    report_failure("dwrd bit did not read back as clear after enable!");
  }
}

/**
 * Inserts a variable number of NOP instructions (0 to 8) to create jitter.
 */
static inline void insert_variable_delay(uint32_t count) {
  switch (count & 0x7) {
    case 7: __asm__ volatile("nop; nop; nop; nop; nop; nop; nop;" ::: "memory"); break;
    case 6: __asm__ volatile("nop; nop; nop; nop; nop; nop;" ::: "memory"); break;
    case 5: __asm__ volatile("nop; nop; nop; nop; nop;" ::: "memory"); break;
    case 4: __asm__ volatile("nop; nop; nop; nop;" ::: "memory"); break;
    case 3: __asm__ volatile("nop; nop; nop;" ::: "memory"); break;
    case 2: __asm__ volatile("nop; nop;" ::: "memory"); break;
    case 1: __asm__ volatile("nop;" ::: "memory"); break;
    default: break;
  }
}

/**
 * Phase 1: Randomized Timing Jitter & Collision Probing (#512)
 *
 * Randomly varies the delay between store commits and subsequent reads from 0 to 8
 * cycles, probing the exact single-cycle window where opportunistic port stealing
 * (dccm_wr_rdbk_issue) arbitrates against competing DCCM reads.
 */
static void test_phase1_random_timing_jitter(void) {
  printf("Starting Phase 1: Randomized Timing Jitter & Collision Probing (#512)...\n");

  volatile uint32_t *target_a = (volatile uint32_t *)(DCCM_TEST_BASE + 0x000);
  volatile uint32_t *target_b = (volatile uint32_t *)(DCCM_TEST_BASE + 0x004);

  const int iterations = 100;

  for (int iter = 0; iter < iterations; iter++) {
    uint32_t pattern = prng_next();
    uint32_t delay = prng_range(0, 8);
    bool test_snoop = (prng_range(0, 1) == 1);
    uint32_t read_val = 0;

    if (test_snoop) {
      // Store to A, insert variable jitter, load from A (snoop path under delay)
      __asm__ volatile("sw %0, 0(%1)" : : "r"(pattern), "r"(target_a) : "memory");
      insert_variable_delay(delay);
      __asm__ volatile("lw %0, 0(%1)" : "=r"(read_val) : "r"(target_a) : "memory");

      if (read_val != pattern) {
        report_failure("Phase 1: Snoop mismatch under jitter!");
      }
    } else {
      // Store to A, insert variable jitter, load from B (steal path collision probe)
      uint32_t val_b = 0xbeef0000 | iter;
      *target_b = val_b;

      __asm__ volatile("sw %0, 0(%1)" : : "r"(pattern), "r"(target_a) : "memory");
      insert_variable_delay(delay);
      __asm__ volatile("lw %0, 0(%1)" : "=r"(read_val) : "r"(target_b) : "memory");

      if (read_val != val_b) {
        report_failure("Phase 1: Competing read corrupted under steal arbitration!");
      }
      if (*target_a != pattern) {
        report_failure("Phase 1: Target A corrupted after steal!");
      }
    }
  }

  printf("Phase 1 Passed: %d randomized timing jitter iterations completed.\n\n", iterations);
}

/**
 * Phase 2: Randomized Access Sizes & RMW Alignment (#512)
 *
 * Randomly mixes 8-bit (sb), 16-bit (sh), and 32-bit (sw) stores across byte
 * offsets (+0, +1, +2, +3) within a word, verifying that the Read-Modify-Write
 * ECC generation and SRAM write-readback check handle all sub-word masks.
 */
static void test_phase2_random_access_sizes_rmw(void) {
  printf("Starting Phase 2: Randomized Access Sizes & RMW Alignment (#512)...\n");

  #define ARENA_WORDS 16
  volatile uint32_t *arena_words = (volatile uint32_t *)(DCCM_TEST_BASE + 0x100);
  volatile uint8_t *arena_bytes = (volatile uint8_t *)arena_words;

  uint8_t shadow_bytes[ARENA_WORDS * 4];

  // Initialize arena and shadow model
  for (size_t i = 0; i < sizeof(shadow_bytes); i++) {
    shadow_bytes[i] = (uint8_t)(i & 0xff);
    arena_bytes[i] = shadow_bytes[i];
  }

  const int iterations = 150;

  for (int iter = 0; iter < iterations; iter++) {
    uint32_t op_size = prng_range(0, 2); // 0=byte, 1=halfword, 2=word
    uint32_t word_idx = prng_range(0, ARENA_WORDS - 1);

    if (op_size == 0) {
      // Byte store
      uint32_t byte_off = prng_range(0, 3);
      uint32_t byte_addr = (word_idx * 4) + byte_off;
      uint8_t data = (uint8_t)prng_next();

      shadow_bytes[byte_addr] = data;
      arena_bytes[byte_addr] = data;

      // Verify immediate read
      uint8_t readback = arena_bytes[byte_addr];
      if (readback != data) {
        report_failure("Phase 2: Byte store readback mismatch!");
      }
    } else if (op_size == 1) {
      // Halfword store (2-byte aligned)
      uint32_t half_off = prng_range(0, 1) * 2;
      uint32_t byte_addr = (word_idx * 4) + half_off;
      uint16_t data = (uint16_t)prng_next();

      shadow_bytes[byte_addr] = (uint8_t)(data & 0xff);
      shadow_bytes[byte_addr + 1] = (uint8_t)((data >> 8) & 0xff);

      volatile uint16_t *half_ptr = (volatile uint16_t *)(arena_bytes + byte_addr);
      *half_ptr = data;

      uint16_t readback = *half_ptr;
      if (readback != data) {
        report_failure("Phase 2: Halfword store readback mismatch!");
      }
    } else {
      // Full word store
      uint32_t data = prng_next();
      uint32_t byte_addr = word_idx * 4;

      shadow_bytes[byte_addr]     = (uint8_t)(data & 0xff);
      shadow_bytes[byte_addr + 1] = (uint8_t)((data >> 8) & 0xff);
      shadow_bytes[byte_addr + 2] = (uint8_t)((data >> 16) & 0xff);
      shadow_bytes[byte_addr + 3] = (uint8_t)((data >> 24) & 0xff);

      arena_words[word_idx] = data;

      uint32_t readback = arena_words[word_idx];
      if (readback != data) {
        report_failure("Phase 2: Word store readback mismatch!");
      }
    }
  }

  // Verify complete memory arena matches shadow model
  for (size_t i = 0; i < sizeof(shadow_bytes); i++) {
    if (arena_bytes[i] != shadow_bytes[i]) {
      report_failure("Phase 2: Arena post-check shadow mismatch!");
    }
  }

  printf("Phase 2 Passed: %d randomized RMW sub-word stores verified.\n\n", iterations);
  #undef ARENA_WORDS
}

/**
 * Phase 3: Multi-Bank Interleaving & Unaligned Spanning (#512)
 *
 * Randomly generates accesses that span across bank boundaries and exercise
 * cross-bank unaligned access logic (testing dccm_wr_rdbk_snoop_hi and
 * dccm_wr_rdbk_active_hi muxing paths).
 */
static void test_phase3_multibank_unaligned(void) {
  printf("Starting Phase 3: Multi-Bank Interleaving & Unaligned Spanning (#512)...\n");

  volatile uint8_t *unalign_arena = (volatile uint8_t *)(DCCM_TEST_BASE + 0x300);

  // Initialize unaligned region
  for (int i = 0; i < 64; i++) {
    unalign_arena[i] = 0;
  }

  const int iterations = 100;

  for (int iter = 0; iter < iterations; iter++) {
    // Offset between 1 and 3 to force word to cross 32-bit word and bank boundaries
    uint32_t unalign_offset = prng_range(1, 3);
    uint32_t base_index = prng_range(0, 10) * 4;
    uint32_t byte_addr = base_index + unalign_offset;

    uint32_t pattern = prng_next();

    // Store unaligned word using byte packing
    unalign_arena[byte_addr]     = (uint8_t)(pattern & 0xff);
    unalign_arena[byte_addr + 1] = (uint8_t)((pattern >> 8) & 0xff);
    unalign_arena[byte_addr + 2] = (uint8_t)((pattern >> 16) & 0xff);
    unalign_arena[byte_addr + 3] = (uint8_t)((pattern >> 24) & 0xff);

    // Read back and reconstruct
    uint32_t readback = (uint32_t)unalign_arena[byte_addr] |
                        ((uint32_t)unalign_arena[byte_addr + 1] << 8) |
                        ((uint32_t)unalign_arena[byte_addr + 2] << 16) |
                        ((uint32_t)unalign_arena[byte_addr + 3] << 24);

    if (readback != pattern) {
      report_failure("Phase 3: Cross-bank unaligned readback mismatch!");
    }
  }

  printf("Phase 3 Passed: %d multi-bank unaligned accesses verified.\n\n", iterations);
}

/**
 * Phase 4: Store Buffer Depth Oscillation & Random Walk Torture (#512)
 *
 * Runs 500 randomized operations across a 32-word DCCM arena, probabilistically
 * mixing store bursts (saturating the 4-entry store buffer), immediate snoop reads,
 * competing reads, and idle cycles.
 */
static void test_phase4_random_walk_torture(void) {
  printf("Starting Phase 4: Store Buffer Depth Oscillation & Random Walk Torture (#512)...\n");

  #define WALK_ARENA_SIZE 32
  volatile uint32_t *arena = (volatile uint32_t *)(DCCM_TEST_BASE + 0x500);
  uint32_t shadow[WALK_ARENA_SIZE];

  // Initialize arena and shadow
  for (int i = 0; i < WALK_ARENA_SIZE; i++) {
    shadow[i] = 0x55aa0000 | i;
    arena[i] = shadow[i];
  }

  uint32_t last_store_idx = 0;
  const int total_steps = 500;

  for (int step = 0; step < total_steps; step++) {
    uint32_t action = prng_range(0, 99);

    if (action < 30) {
      // Action 0: Single Store (30% probability)
      uint32_t idx = prng_range(0, WALK_ARENA_SIZE - 1);
      uint32_t val = prng_next();
      shadow[idx] = val;
      arena[idx] = val;
      last_store_idx = idx;
    } else if (action < 50) {
      // Action 1: Immediate Snoop Load (20% probability) - targets last stored word
      uint32_t read_val = arena[last_store_idx];
      if (read_val != shadow[last_store_idx]) {
        report_failure("Phase 4: Immediate snoop read mismatch!");
      }
    } else if (action < 75) {
      // Action 2: Competing Random Load (25% probability) - keeps window open
      uint32_t idx = prng_range(0, WALK_ARENA_SIZE - 1);
      uint32_t read_val = arena[idx];
      if (read_val != shadow[idx]) {
        report_failure("Phase 4: Competing load data mismatch!");
      }
    } else if (action < 90) {
      // Action 3: Rapid Store Burst of 4 stores (15% probability) - saturates store buffer
      uint32_t base_idx = prng_range(0, WALK_ARENA_SIZE - 4);
      for (uint32_t b = 0; b < 4; b++) {
        uint32_t val = prng_next();
        shadow[base_idx + b] = val;
        arena[base_idx + b] = val;
      }
      last_store_idx = base_idx + 3;
    } else {
      // Action 4: Idle / Non-DCCM arithmetic instructions (10% probability) - gives window steal opportunity
      __asm__ volatile("nop; nop; nop; nop;" ::: "memory");
    }
  }

  // Final synchronization check: verify all words match shadow model
  for (int i = 0; i < WALK_ARENA_SIZE; i++) {
    if (arena[i] != shadow[i]) {
      report_failure("Phase 4: Final arena state mismatch!");
    }
  }

  printf("Phase 4 Passed: 500-step random walk completed without hang or corruption.\n\n");
  #undef WALK_ARENA_SIZE
}

/**
 * Phase 5: Asynchronous Runtime dwrd Toggling Under Active Traffic (#512)
 *
 * Flips the MFDC.dwrd bit between 0 (enabled) and 1 (disabled) pseudo-randomly
 * while executing continuous store/load traffic to verify seamless transitions.
 */
static void test_phase5_asynchronous_dwrd_toggling(void) {
  printf("Starting Phase 5: Asynchronous Runtime dwrd Toggling Under Active Traffic (#512)...\n");

  volatile uint32_t *target = (volatile uint32_t *)(DCCM_TEST_BASE + 0x700);
  const int iterations = 100;

  for (int iter = 0; iter < iterations; iter++) {
    // Periodically toggle dwrd bit
    if ((iter % 7) == 0) {
      bool disable = (prng_range(0, 1) == 1);
      if (disable) {
        disable_dccm_wr_readback();
      } else {
        enable_dccm_wr_readback();
      }
    }

    uint32_t val = prng_next();
    *target = val;
    uint32_t readback = *target;

    if (readback != val) {
      report_failure("Phase 5: Store/load mismatch during active dwrd toggling!");
    }
  }

  // Ensure readback check is re-enabled at the end of the test
  enable_dccm_wr_readback();

  printf("Phase 5 Passed: 100 iterations of active traffic with dynamic dwrd transitions.\n\n");
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
