/* SPDX-License-Identifier: Apache-2.0
 * Copyright 2026 Google LLC
 *
 * DCCM Write Readback Autonomous Co-Simulation Fuzzing & Chaos Monkey Verification (#572)
 * Author: Samip Modi (samipmodi@google.com)
 *
 * Description:
 * Autonomous hardware/software co-simulation fuzzing suite for the VeeR-EL2 DCCM
 * write-readback countermeasure (`RV_DCCM_WR_READBACK`), implementing Issue #572:
 * - Phase A (`WR_FI_005`): Executes >10,000 randomized CPU DCCM operations (`sb`,
 *   `sh`, `sw`, unaligned `sh`/`sw`, `lb`, `lbu`, `lh`, `lhu`, `lw`, unaligned
 *   `lh`/`lw`, explicit snoop-lo/snoop-hi sequences, store-buffer bursts, and
 *   runtime `MFDC.dwrd` bit-7 toggles) concurrently with an autonomous LFSR-driven
 *   background DMA traffic engine (`0xBE`) in `tb_top.sv`. Verifies every load and
 *   final memory state against a byte-accurate shadow memory (`shadow_mem[]`) and
 *   asserts zero false-positive `dccm_write_readback_error` pulses.
 * - Phase B (Chaos Monkey Random Fault Injection): Enables the autonomous LFSR-driven
 *   Chaos Monkey fault injector (`0xBF`) in `tb_top.sv` (randomly injecting write-enable
 *   suppression, 1-bit data flips, multi-bit data flips, and ECC syndrome bit flips on
 *   armed CPU stores) alongside background DMA traffic. Verifies 100% 1-to-1 scoreboard
 *   equivalence (`chaos_resolved_err_cnt == chaos_injected_cnt`), sticky first-fault-wins
 *   capture in DMI `0x48`-`0x4A`, W1C clearing (`0xB2`), and subsequent fault capture
 *   in a second Chaos wave.
 *
 * Test Phases:
 * 1. Phase A: 10,000+ Op Shadow-Memory Co-Simulation Fuzzing under Autonomous DMA (`WR_FI_005`).
 * 2. Phase B: Chaos Monkey Random Fault Injection Scoreboard & Sticky DMI Verification (`#572`).
 */

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include "defines.h"

extern volatile uint32_t tohost;
extern int printf(const char *format, ...);
extern int putchar(int c);

#define MFDC_CSR                            0x7f9
#define MFDC_DCCM_WR_READBACK_DISABLE_MASK  (1u << 7)

#define TEST_PASSED                         0xff
#define TEST_FAILED                         0x01

#define DCCM_SADDR                          ((uint32_t)RV_DCCM_SADR)
#define DCCM_ADDR_MASK                      ((1u << RV_DCCM_BITS) - 1u)
#define DCCM_ARENA_OFFSET                   (1u << (RV_DCCM_BITS - 1))
#define DCCM_TEST_BASE                      (DCCM_SADDR + DCCM_ARENA_OFFSET)

#define CPU_FUZZ_BASE                       (DCCM_TEST_BASE + 0x0000u)
#define CPU_FUZZ_BYTES                      512u
#define CPU_FUZZ_WORDS                      (CPU_FUZZ_BYTES / 4u)
#define DMA_RW_BASE                         (DCCM_TEST_BASE + 0x0200u)
#define DMA_RW_WORDS                        128u

#define COMM_SCRATCHPAD_ADDR                (DCCM_TEST_BASE + 0x0C00u)
#define COMM_HANDSHAKE_ADDR                 (DCCM_TEST_BASE + 0x0C04u)

#define MAILBOX_CMD_DMI_READ                0xB1u
#define MAILBOX_CMD_DMI_WRITE               0xB2u
#define MAILBOX_CMD_GET_PULSES              0xB4u
#define MAILBOX_CMD_RDBK_COUNTERS           0xBBu
#define MAILBOX_CMD_FUZZ_DMA_CTRL           0xBEu
#define MAILBOX_CMD_FUZZ_FAULT_CTRL         0xBFu

#define RDBK_CNT_RESET                      0u
#define RDBK_CNT_ARM                        1u
#define RDBK_CNT_SNOOP_LO                   2u
#define RDBK_CNT_SNOOP_HI                   3u
#define RDBK_CNT_STEAL                      4u
#define RDBK_CNT_DEFER                      5u
#define RDBK_CNT_STBUF_FULL                 6u
#define RDBK_CNT_CHAOS_INJ                  11u
#define RDBK_CNT_CHAOS_RES                  12u
#define RDBK_CNT_CHAOS_FIRST_ADDR           13u
#define RDBK_CNT_FUZZ_DMA_TRXN              14u

#define DMI_REG_DMCONTROL                   0x10u
#define DMI_REG_DCCM_STATUS                 0x48u
#define DMI_REG_DCCM_DATA                   0x49u
#define DMI_REG_DCCM_ECC                    0x4Au

static volatile uint32_t *const kScratchpad = (volatile uint32_t *)COMM_SCRATCHPAD_ADDR;
static volatile uint32_t *const kHandshake  = (volatile uint32_t *)COMM_HANDSHAKE_ADDR;

static uint8_t g_shadow_mem[CPU_FUZZ_BYTES] __attribute__((aligned(4)));
static uint32_t g_seq_id = 0;
static uint32_t g_rng_state = 0xC0FFEE01u;
static volatile uint32_t g_chaos_load_ecc_traps = 0;

/**
 * Halts execution and reports test failure to `tb_top.sv`.
 */
static void report_failure(void) {
  printf("Test FAILED!\n");
  putchar(TEST_FAILED);
  while (true) {}
}

/**
 * Deterministic 32-bit Xorshift PRNG.
 */
static inline uint32_t xorshift32(void) {
  uint32_t x = g_rng_state;
  x ^= x << 13;
  x ^= x >> 17;
  x ^= x << 5;
  g_rng_state = x;
  return x;
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
 * Queries cumulative `dccm_write_readback_error` pulse count from `tb_top.sv`.
 */
static inline uint32_t get_error_pulse_count(void) {
  return send_tb_command(MAILBOX_CMD_GET_PULSES, 0);
}

/**
 * Reads a 32-bit DMI register (`0x48-0x4A`) via `tb_top.sv`.
 */
static inline uint32_t dmi_read(uint8_t addr) {
  return send_tb_command(MAILBOX_CMD_DMI_READ, addr);
}

/**
 * Performs a DMI write (`dmactive=1` for `0x10`, W1C for `0x48`).
 */
static inline void dmi_write(uint8_t addr) {
  (void)send_tb_command(MAILBOX_CMD_DMI_WRITE, addr);
}

/**
 * Enables or disables autonomous background DMA traffic (`0xBE`) in `tb_top.sv`.
 */
static inline void tb_set_fuzz_dma(bool enable) {
  (void)send_tb_command(MAILBOX_CMD_FUZZ_DMA_CTRL, enable ? 1u : 0u);
}

/**
 * Enables or disables the Chaos Monkey random fault injector (`0xBF`) in `tb_top.sv`.
 */
static inline void tb_set_chaos_fault(bool enable) {
  (void)send_tb_command(MAILBOX_CMD_FUZZ_FAULT_CTRL, enable ? 1u : 0u);
}

/**
 * Writes a 16-bit halfword to both `CPU_FUZZ_BASE + byte_off` and `g_shadow_mem`.
 */
static inline void fuzz_store_u16(uint32_t byte_off, uint16_t val) {
  volatile uint16_t *hw_ptr = (volatile uint16_t *)(CPU_FUZZ_BASE + byte_off);
  *hw_ptr = val;
  g_shadow_mem[byte_off + 0u] = (uint8_t)(val & 0xFFu);
  g_shadow_mem[byte_off + 1u] = (uint8_t)((val >> 8) & 0xFFu);
}

/**
 * Writes a 32-bit word to both `CPU_FUZZ_BASE + byte_off` and `g_shadow_mem`.
 */
static inline void fuzz_store_u32(uint32_t byte_off, uint32_t val) {
  volatile uint32_t *w_ptr = (volatile uint32_t *)(CPU_FUZZ_BASE + byte_off);
  *w_ptr = val;
  g_shadow_mem[byte_off + 0u] = (uint8_t)(val & 0xFFu);
  g_shadow_mem[byte_off + 1u] = (uint8_t)((val >> 8) & 0xFFu);
  g_shadow_mem[byte_off + 2u] = (uint8_t)((val >> 16) & 0xFFu);
  g_shadow_mem[byte_off + 3u] = (uint8_t)((val >> 24) & 0xFFu);
}

/**
 * Reads a 16-bit halfword from `g_shadow_mem` at `byte_off`.
 */
static inline uint16_t shadow_load_u16(uint32_t byte_off) {
  return (uint16_t)g_shadow_mem[byte_off + 0u] |
         ((uint16_t)g_shadow_mem[byte_off + 1u] << 8);
}

/**
 * Reads a 32-bit word from `g_shadow_mem` at `byte_off`.
 */
static inline uint32_t shadow_load_u32(uint32_t byte_off) {
  return (uint32_t)g_shadow_mem[byte_off + 0u] |
         ((uint32_t)g_shadow_mem[byte_off + 1u] << 8) |
         ((uint32_t)g_shadow_mem[byte_off + 2u] << 16) |
         ((uint32_t)g_shadow_mem[byte_off + 3u] << 24);
}

/**
 * Phase A (`WR_FI_005`): 10,000+ Randomized Operations + Shadow Memory Verification
 * under Autonomous Background DMA Traffic.
 */
static void test_phase_a_shadow_fuzz(void) {
  printf("[TEST] Phase A (WR_FI_005): Starting 10,000+ op shadow-memory fuzzing with autonomous DMA...\n");

  volatile uint32_t *cpu_words = (volatile uint32_t *)CPU_FUZZ_BASE;
  volatile uint32_t *dma_words = (volatile uint32_t *)DMA_RW_BASE;

  for (uint32_t i = 0; i < CPU_FUZZ_WORDS; i++) {
    uint32_t init_val = 0xA5000000u ^ (i * 0x01010101u);
    fuzz_store_u32(i * 4u, init_val);
  }
  for (uint32_t i = 0; i < DMA_RW_WORDS; i++) {
    dma_words[i] = 0xD0000000u | i;
  }
  __asm__ volatile("fence rw, rw" ::: "memory");

  dmi_write(DMI_REG_DCCM_STATUS);
  tb_reset_rdbk_counters();
  uint32_t pulses_before = get_error_pulse_count();

  // Start autonomous LFSR-driven background DMA traffic (`0xBE` subcmd `1`)
  tb_set_fuzz_dma(true);

  uint32_t total_ops = 0;
  bool dwrd_disabled = false;

  for (uint32_t iter = 0; iter < 10000u; iter++) {
    // Periodically exercise runtime `MFDC.dwrd` disable/re-enable under live traffic
    if ((iter & 0x1FFu) == 0x1C0u && !dwrd_disabled) {
      uint32_t mask = MFDC_DCCM_WR_READBACK_DISABLE_MASK;
      __asm__ volatile("csrs %0, %1" : : "i"(MFDC_CSR), "r"(mask));
      dwrd_disabled = true;
    } else if ((iter & 0x1FFu) == 0x1E0u && dwrd_disabled) {
      uint32_t mask = MFDC_DCCM_WR_READBACK_DISABLE_MASK;
      __asm__ volatile("csrc %0, %1" : : "i"(MFDC_CSR), "r"(mask));
      dwrd_disabled = false;
    }

    uint32_t r = xorshift32();
    uint32_t action = r & 0x7u;
    uint32_t val = xorshift32();

    if (action == 0u) {
      // Aligned 32-bit word store (`sw`)
      uint32_t word_off = ((r >> 3) & 0x7Fu) * 4u;
      fuzz_store_u32(word_off, val);
      total_ops++;
    } else if (action == 1u) {
      // Aligned 16-bit halfword store (`sh`) -> triggers DCCM RMW ECC
      uint32_t hw_off = ((r >> 3) & 0xFFu) * 2u;
      fuzz_store_u16(hw_off, (uint16_t)val);
      total_ops++;
    } else if (action == 2u) {
      // 8-bit byte store (`sb`) -> triggers DCCM RMW ECC
      uint32_t byte_off = (r >> 3) & 0x1FFu;
      volatile uint8_t *b_ptr = (volatile uint8_t *)(CPU_FUZZ_BASE + byte_off);
      uint8_t b_val = (uint8_t)val;
      *b_ptr = b_val;
      g_shadow_mem[byte_off] = b_val;
      total_ops++;
    } else if (action == 3u) {
      // Unaligned `sh` or `sw` within `0..507`
      uint32_t byte_off = ((r >> 3) % 505u) + 1u;
      if ((byte_off & 0x3u) == 0u) {
        byte_off += 1u;
      }
      if ((r & 0x8u) != 0u) {
        fuzz_store_u32(byte_off, val);
      } else {
        fuzz_store_u16(byte_off, (uint16_t)val);
      }
      total_ops++;
    } else if (action == 4u) {
      // Randomized load (`lb`, `lbu`, `lh`, `lhu`, `lw`, including unaligned) + shadow check
      uint32_t byte_off = (r >> 3) % 508u;
      uint32_t ld_kind = (r >> 12) & 0x3u;
      if (ld_kind == 0u) {
        uint8_t hw_b = *(volatile uint8_t *)(CPU_FUZZ_BASE + byte_off);
        uint8_t exp_b = g_shadow_mem[byte_off];
        if (hw_b != exp_b) {
          printf("[FAIL] Phase A load u8 mismatch at +0x%x: got 0x%02x, exp 0x%02x\n",
                 byte_off, hw_b, exp_b);
          report_failure();
        }
      } else if (ld_kind == 1u) {
        int8_t hw_sb = *(volatile int8_t *)(CPU_FUZZ_BASE + byte_off);
        int8_t exp_sb = (int8_t)g_shadow_mem[byte_off];
        if (hw_sb != exp_sb) {
          printf("[FAIL] Phase A load s8 mismatch at +0x%x\n", byte_off);
          report_failure();
        }
      } else if (ld_kind == 2u) {
        uint16_t hw_h = *(volatile uint16_t *)(CPU_FUZZ_BASE + byte_off);
        uint16_t exp_h = shadow_load_u16(byte_off);
        if (hw_h != exp_h) {
          printf("[FAIL] Phase A load u16 mismatch at +0x%x: got 0x%04x, exp 0x%04x\n",
                 byte_off, hw_h, exp_h);
          report_failure();
        }
      } else {
        uint32_t hw_w = *(volatile uint32_t *)(CPU_FUZZ_BASE + byte_off);
        uint32_t exp_w = shadow_load_u32(byte_off);
        if (hw_w != exp_w) {
          printf("[FAIL] Phase A load u32 mismatch at +0x%x: got 0x%08x, exp 0x%08x\n",
                 byte_off, hw_w, exp_w);
          report_failure();
        }
      }
      total_ops++;
    } else if (action == 5u) {
      // Explicit Snoop-Lo sequence (`sw 0(addr)` + 3 adjacent loads + `lw 0(addr)`)
      uint32_t word_idx = (r >> 3) & 0x7Eu;
      uint32_t byte_off = word_idx * 4u;
      volatile uint32_t *target_ptr = (volatile uint32_t *)(CPU_FUZZ_BASE + byte_off);
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
          : [val] "r"(val), [addr] "r"(target_ptr)
          : "memory");

      g_shadow_mem[byte_off + 0u] = (uint8_t)(val & 0xFFu);
      g_shadow_mem[byte_off + 1u] = (uint8_t)((val >> 8) & 0xFFu);
      g_shadow_mem[byte_off + 2u] = (uint8_t)((val >> 16) & 0xFFu);
      g_shadow_mem[byte_off + 3u] = (uint8_t)((val >> 24) & 0xFFu);

      if (snooped_val != val) {
        printf("[FAIL] Phase A Snoop-Lo mismatch at +0x%x: got 0x%08x, exp 0x%08x\n",
               byte_off, snooped_val, val);
        report_failure();
      }
      total_ops += 5u;
    } else if (action == 6u) {
      // Explicit Snoop-Hi sequence (`sw 8(base)` + 3 loads `0(base)` + unaligned `lw 5(base)`)
      uint32_t base_word_idx = (r >> 3) % 120u;
      uint32_t base_off = base_word_idx * 4u;
      uint32_t st_off = base_off + 8u;
      volatile uint32_t *base_ptr = (volatile uint32_t *)(CPU_FUZZ_BASE + base_off);
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
          : [val] "r"(val), [base] "r"(base_ptr)
          : "memory");

      g_shadow_mem[st_off + 0u] = (uint8_t)(val & 0xFFu);
      g_shadow_mem[st_off + 1u] = (uint8_t)((val >> 8) & 0xFFu);
      g_shadow_mem[st_off + 2u] = (uint8_t)((val >> 16) & 0xFFu);
      g_shadow_mem[st_off + 3u] = (uint8_t)((val >> 24) & 0xFFu);

      uint32_t exp_unaligned = shadow_load_u32(base_off + 5u);
      if (unaligned_val != exp_unaligned) {
        printf("[FAIL] Phase A Snoop-Hi mismatch at +0x%x: got 0x%08x, exp 0x%08x\n",
               base_off + 5u, unaligned_val, exp_unaligned);
        report_failure();
      }
      total_ops += 5u;
    } else {
      // Back-to-back store burst + immediate load verification
      uint32_t base_idx = (r >> 3) & 0x7Cu;
      fuzz_store_u32((base_idx + 0u) * 4u, val ^ 0x11111111u);
      fuzz_store_u16((base_idx + 1u) * 4u, (uint16_t)(val ^ 0x2222u));
      fuzz_store_u32((base_idx + 2u) * 4u, val ^ 0x33333333u);
      fuzz_store_u16((base_idx + 3u) * 4u + 2u, (uint16_t)(val >> 16));

      uint32_t check_idx = base_idx + ((r >> 10) & 0x3u);
      uint32_t hw_w = cpu_words[check_idx];
      uint32_t exp_w = shadow_load_u32(check_idx * 4u);
      if (hw_w != exp_w) {
        printf("[FAIL] Phase A burst load mismatch at word %u: got 0x%08x, exp 0x%08x\n",
               check_idx, hw_w, exp_w);
        report_failure();
      }
      total_ops += 5u;
    }
  }

  // Ensure `MFDC.dwrd` is enabled (`0`) after the fuzzing loop
  if (dwrd_disabled) {
    uint32_t mask = MFDC_DCCM_WR_READBACK_DISABLE_MASK;
    __asm__ volatile("csrc %0, %1" : : "i"(MFDC_CSR), "r"(mask));
  }
  __asm__ volatile("fence rw, rw" ::: "memory");

  // Stop autonomous background DMA traffic (`0xBE` subcmd `0`)
  tb_set_fuzz_dma(false);

  // Full 128-word sweep verifying `CPU_FUZZ_BASE` matches `g_shadow_mem`
  for (uint32_t i = 0; i < CPU_FUZZ_WORDS; i++) {
    uint32_t hw_w = cpu_words[i];
    uint32_t exp_w = shadow_load_u32(i * 4u);
    if (hw_w != exp_w) {
      printf("[FAIL] Phase A final sweep mismatch at word %u: got 0x%08x, exp 0x%08x\n",
             i, hw_w, exp_w);
      report_failure();
    }
  }

  uint32_t arm_cnt      = tb_get_rdbk_counter(RDBK_CNT_ARM);
  uint32_t snoop_lo_cnt = tb_get_rdbk_counter(RDBK_CNT_SNOOP_LO);
  uint32_t snoop_hi_cnt = tb_get_rdbk_counter(RDBK_CNT_SNOOP_HI);
  uint32_t steal_cnt    = tb_get_rdbk_counter(RDBK_CNT_STEAL);
  uint32_t defer_cnt    = tb_get_rdbk_counter(RDBK_CNT_DEFER);
  uint32_t dma_cnt      = tb_get_rdbk_counter(RDBK_CNT_FUZZ_DMA_TRXN);
  uint32_t pulses_after = get_error_pulse_count();
  uint32_t dmi_status   = dmi_read(DMI_REG_DCCM_STATUS);

  printf("[TEST] Phase A Summary: total_ops=%u, arm=%u, snoop_lo=%u, snoop_hi=%u, steal=%u, defer=%u, dma_trxn=%u, pulses=%u\n",
         total_ops, arm_cnt, snoop_lo_cnt, snoop_hi_cnt, steal_cnt, defer_cnt,
         dma_cnt, pulses_after - pulses_before);

  if (pulses_after != pulses_before || (dmi_status & 0x80000000u) != 0u) {
    printf("[FAIL] Phase A: False-positive write-readback error detected (pulses=%u, dmi48=0x%08x)!\n",
           pulses_after - pulses_before, dmi_status);
    report_failure();
  }
  if (total_ops < 10000u || arm_cnt < 1000u || snoop_lo_cnt < 50u ||
      snoop_hi_cnt == 0u || steal_cnt < 100u || defer_cnt < 10u || dma_cnt < 100u) {
    printf("[FAIL] Phase A: Coverage threshold not met!\n");
    report_failure();
  }

  printf("[PASS] Phase A (WR_FI_005) Passed: %u ops verified against shadow memory with 0 false errors under %u DMA transactions.\n\n",
         total_ops, dma_cnt);
}

/**
 * Machine trap handler for Phase B Chaos Monkey mode.
 * If a CPU load snoops a Chaos-faulted store on the exact cycle a multi-bit
 * fault is active in SRAM (`mcause = 0x5`), advances `mepc` past the load and
 * returns via `mret`.
 */
void __attribute__((interrupt("machine"), aligned(4))) chaos_trap_handler(void) {
  uint32_t mcause = 0;
  uint32_t mepc = 0;
  __asm__ volatile("csrr %0, mcause" : "=r"(mcause));
  __asm__ volatile("csrr %0, mepc" : "=r"(mepc));

  if (mcause == 5u) {
    uint16_t inst16 = *(const uint16_t *)mepc;
    if ((inst16 & 0x3u) == 0x3u) {
      mepc += 4u;
    } else {
      mepc += 2u;
    }
    __asm__ volatile("csrw mepc, %0" : : "r"(mepc));
    g_chaos_load_ecc_traps++;
    return;
  }

  printf("ERROR: Unexpected trap in chaos_trap_handler (mcause=0x%08x, mepc=0x%08x)!\n",
         mcause, mepc);
  report_failure();
}

/**
 * Phase B: Chaos Monkey Continuous Random Fault Injection + Scoreboard Verification.
 */
static void test_phase_b_chaos_monkey(void) {
  printf("[TEST] Phase B: Starting Chaos Monkey random fault injection & scoreboard verification...\n");

  uint32_t orig_mtvec = 0;
  __asm__ volatile("csrr %0, mtvec" : "=r"(orig_mtvec));
  __asm__ volatile("csrw mtvec, %0" : : "r"((uint32_t)&chaos_trap_handler));

  dmi_write(DMI_REG_DCCM_STATUS);
  tb_reset_rdbk_counters();
  uint32_t pulses_before_w1 = get_error_pulse_count();

  // Wave 1: Enable autonomous DMA (`0xBE`) + Chaos Monkey fault injector (`0xBF`)
  tb_set_fuzz_dma(true);
  tb_set_chaos_fault(true);

  for (uint32_t iter = 0; iter < 600u; iter++) {
    uint32_t r = xorshift32();
    uint32_t word_idx = (r >> 3) & 0x7Eu;
    volatile uint32_t *target_ptr = (volatile uint32_t *)(CPU_FUZZ_BASE + word_idx * 4u);
    // Ensure written value differs from current value so write-skip (`2'b00`) always corrupts
    uint32_t val = 0xB0000000u ^ (iter * 0x00010001u) ^ r;

    if ((r & 0x3u) == 0u) {
      // Snoop-Lo resolution under Chaos Monkey
      uint32_t dummy = 0;
      uint32_t res = 0;
      __asm__ volatile(
          ".balign 16\n\t"
          "sw   %[val], 0(%[addr])\n\t"
          "lw   %[dum], 4(%[addr])\n\t"
          "lw   %[dum], 4(%[addr])\n\t"
          "lw   %[dum], 4(%[addr])\n\t"
          "lw   %[res], 0(%[addr])\n\t"
          "nop\n\t"
          "nop\n\t"
          "nop\n\t"
          "nop\n\t"
          : [res] "=&r"(res), [dum] "=&r"(dummy)
          : [val] "r"(val), [addr] "r"(target_ptr)
          : "memory");
    } else {
      // Steal path resolution under Chaos Monkey
      __asm__ volatile(
          "sw   %[val], 0(%[addr])\n\t"
          "nop\n\t"
          "nop\n\t"
          "nop\n\t"
          "nop\n\t"
          "nop\n\t"
          "nop\n\t"
          :
          : [val] "r"(val), [addr] "r"(target_ptr)
          : "memory");
    }
  }

  tb_set_chaos_fault(false);
  tb_set_fuzz_dma(false);
  __asm__ volatile("fence rw, rw" ::: "memory");

  uint32_t chaos_inj_w1   = tb_get_rdbk_counter(RDBK_CNT_CHAOS_INJ);
  uint32_t chaos_res_w1   = tb_get_rdbk_counter(RDBK_CNT_CHAOS_RES);
  uint32_t chaos_addr_w1  = tb_get_rdbk_counter(RDBK_CNT_CHAOS_FIRST_ADDR);
  uint32_t pulses_after_w1 = get_error_pulse_count();
  uint32_t dmi48_w1       = dmi_read(DMI_REG_DCCM_STATUS);
  uint32_t dmi49_w1       = dmi_read(DMI_REG_DCCM_DATA);
  uint32_t dmi4a_w1       = dmi_read(DMI_REG_DCCM_ECC);

  printf("[TEST] Phase B Wave 1: chaos_inj=%u, chaos_res=%u, pulses_delta=%u, dmi48=0x%08x (exp_addr=0x%04x), dmi49=0x%08x, dmi4a=0x%02x\n",
         chaos_inj_w1, chaos_res_w1, pulses_after_w1 - pulses_before_w1,
         dmi48_w1, chaos_addr_w1, dmi49_w1, dmi4a_w1);

  if (chaos_inj_w1 < 20u || chaos_res_w1 != chaos_inj_w1 ||
      (pulses_after_w1 - pulses_before_w1) != chaos_inj_w1) {
    printf("[FAIL] Phase B Wave 1: Scoreboard mismatch (inj=%u, res=%u, pulses=%u)!\n",
           chaos_inj_w1, chaos_res_w1, pulses_after_w1 - pulses_before_w1);
    report_failure();
  }
  if ((dmi48_w1 & 0x80000000u) == 0u ||
      (dmi48_w1 & DCCM_ADDR_MASK) != (chaos_addr_w1 & DCCM_ADDR_MASK)) {
    printf("[FAIL] Phase B Wave 1: Sticky DMI 0x48 first-fault-wins mismatch (dmi48=0x%08x, exp_addr=0x%04x)!\n",
           dmi48_w1, chaos_addr_w1);
    report_failure();
  }

  // Clear DMI 0x48 via W1C (`0xB2`) and verify valid bit clears
  dmi_write(DMI_REG_DCCM_STATUS);
  uint32_t dmi48_cleared = dmi_read(DMI_REG_DCCM_STATUS);
  if ((dmi48_cleared & 0x80000000u) != 0u) {
    printf("[FAIL] Phase B: DMI 0x48 valid bit did not clear after W1C (0x%08x)!\n",
           dmi48_cleared);
    report_failure();
  }

  // Wave 2: Re-enable Chaos Monkey + DMA after W1C and verify subsequent fault capture
  tb_set_fuzz_dma(true);
  tb_set_chaos_fault(true);

  for (uint32_t iter = 0; iter < 300u; iter++) {
    uint32_t r = xorshift32();
    uint32_t word_idx = (r >> 3) & 0x7Eu;
    volatile uint32_t *target_ptr = (volatile uint32_t *)(CPU_FUZZ_BASE + word_idx * 4u);
    uint32_t val = 0xC0000000u ^ (iter * 0x00020002u) ^ r;

    __asm__ volatile(
        "sw   %[val], 0(%[addr])\n\t"
        "nop\n\t"
        "nop\n\t"
        "nop\n\t"
        "nop\n\t"
        "nop\n\t"
        "nop\n\t"
        :
        : [val] "r"(val), [addr] "r"(target_ptr)
        : "memory");
  }

  tb_set_chaos_fault(false);
  tb_set_fuzz_dma(false);
  __asm__ volatile("fence rw, rw" ::: "memory");

  uint32_t chaos_inj_w2   = tb_get_rdbk_counter(RDBK_CNT_CHAOS_INJ);
  uint32_t chaos_res_w2   = tb_get_rdbk_counter(RDBK_CNT_CHAOS_RES);
  uint32_t chaos_addr_w2  = tb_get_rdbk_counter(RDBK_CNT_CHAOS_FIRST_ADDR);
  uint32_t pulses_after_w2 = get_error_pulse_count();
  uint32_t dmi48_w2       = dmi_read(DMI_REG_DCCM_STATUS);

  printf("[TEST] Phase B Wave 2: cumulative chaos_inj=%u, chaos_res=%u, dmi48=0x%08x (exp_addr=0x%04x)\n",
         chaos_inj_w2, chaos_res_w2, dmi48_w2, chaos_addr_w2);

  if (chaos_inj_w2 <= chaos_inj_w1 + 5u || chaos_res_w2 != chaos_inj_w2 ||
      (pulses_after_w2 - pulses_before_w1) != chaos_inj_w2) {
    printf("[FAIL] Phase B Wave 2: Cumulative scoreboard mismatch (inj=%u, res=%u, pulses=%u)!\n",
           chaos_inj_w2, chaos_res_w2, pulses_after_w2 - pulses_before_w1);
    report_failure();
  }
  if ((dmi48_w2 & 0x80000000u) == 0u ||
      (dmi48_w2 & DCCM_ADDR_MASK) != (chaos_addr_w2 & DCCM_ADDR_MASK)) {
    printf("[FAIL] Phase B Wave 2: Post-W1C DMI 0x48 capture mismatch (dmi48=0x%08x, exp_addr=0x%04x)!\n",
           dmi48_w2, chaos_addr_w2);
    report_failure();
  }

  dmi_write(DMI_REG_DCCM_STATUS);
  __asm__ volatile("csrw mtvec, %0" : : "r"(orig_mtvec));

  printf("[PASS] Phase B Passed: %u random Chaos Monkey faults injected and 100%% caught by hardware write-readback.\n\n",
         chaos_inj_w2);
}

/**
 * Default unexpected trap handler.
 */
void trap_handler(void) {
  printf("ERROR: Unexpected trap encountered!\n");
  report_failure();
}

/**
 * Main entry point.
 */
int main(void) {
  *kScratchpad = 0u;
  *kHandshake  = 0u;
  __asm__ volatile("fence rw, rw" ::: "memory");

  // Enable Debug Module (`dmcontrol.dmactive = 1`) via standard DMI write to 0x10
  dmi_write(DMI_REG_DMCONTROL);

  printf("================================================================\n");
  printf("=== DCCM Write Readback Autonomous Fuzzing & Chaos Suite (#572) ===\n");
  printf("================================================================\n\n");

  test_phase_a_shadow_fuzz();
  test_phase_b_chaos_monkey();

  printf("================================================================\n");
  printf("=== ALL PHASES PASSED: Autonomous Co-Sim Fuzzing Verified ======\n");
  printf("================================================================\n");

  return 0;
}
