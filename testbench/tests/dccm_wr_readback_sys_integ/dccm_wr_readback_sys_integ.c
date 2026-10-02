/* SPDX-License-Identifier: Apache-2.0
 * Copyright 2026 Google LLC
 *
 * DCCM Write Readback System Integration (DMA & ECC) Verification (#512)
 * Author: Samip Modi (samipmodi@google.com)
 *
 * Description:
 * Comprehensive bare-metal verification of the VeeR EL2 DCCM write-readback
 * hardware countermeasure interacting with real top-level DMA slave bus traffic
 * and real DCCM SRAM single-bit ECC error corrections, verifying Issue #512
 * system interaction requirements via architectural state, CSRs (`mdccmect`),
 * DMI diagnostic registers (`0x48`), RTL event counters (`0xBB`), and concurrent
 * SystemVerilog Assertions (`assert property` in `tb_top.sv`).
 *
 * Test Phases:
 * 1. Phase 1: DMA Write Collision (WR_SYS_001 #512) - verify `dccm_ready` holds off
 *    a real top-level DMA write while write-readback check is pending, and that
 *    the DMA write (`0xAABBCCDD`) completes cleanly once the check resolves via steal.
 * 2. Phase 2: DMA Read Collision Snoop Path (WR_SYS_002A #512) - verify a real
 *    top-level DMA read to a matching store address resolves the check via snoop
 *    (`snoop_lo >= 1`, `steal == 0`) without a redundant port steal.
 * 3. Phase 3: DMA Read Collision Steal Deferral (WR_SYS_002B #512) - verify a real
 *    top-level DMA read to a different address takes priority and defers the core
 *    readback steal (`defer >= 1`, `steal >= 1`) to the next idle cycle.
 * 4. Phase 4: ECC 1-Bit Correction Snoop Path (WR_SYS_003A #512) - verify readback
 *    check snoops load data when a load hits a real 1-bit SRAM ECC error (`snoop_lo >= 1`),
 *    detects the raw SRAM corruption (`dccm_write_readback_error` + DMI `0x48`), and
 *    hardware ECC corrects (`mdccmect` + 1) and scrubs the word in-place.
 * 5. Phase 5: ECC 1-Bit Correction Steal Deferral (WR_SYS_003B #512) - verify a
 *    real 1-bit ECC correction write-back (`ld_single_ecc_error_r_ff`, `mdccmect` + 1)
 *    defers a concurrent core readback steal (`defer >= 1`, `steal >= 1`) to the next cycle.
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

extern volatile uint32_t tohost;

// Dedicated non-colliding mailbox opcodes
#define MAILBOX_CMD_DMI_READ           0xB1u
#define MAILBOX_CMD_DMI_WRITE          0xB2u
#define MAILBOX_CMD_GET_PULSES         0xB4u
#define MAILBOX_CMD_ARM_DMA_WR_COLL    0xB5u
#define MAILBOX_CMD_ARM_DMA_RD_SNOOP   0xB6u
#define MAILBOX_CMD_ARM_DMA_RD_STEAL   0xB7u
#define MAILBOX_CMD_ARM_ECC_SNOOP      0xB8u
#define MAILBOX_CMD_ARM_ECC_STEAL      0xB9u
#define MAILBOX_CMD_RDBK_COUNTERS      0xBBu

#define RDBK_CNT_RESET                 0u
#define RDBK_CNT_ARM                   1u
#define RDBK_CNT_SNOOP_LO              2u
#define RDBK_CNT_SNOOP_HI              3u
#define RDBK_CNT_STEAL                 4u
#define RDBK_CNT_DEFER                 5u

#define DMI_REG_DMCONTROL              0x10u
#define DMI_REG_FAULT_STATUS           0x48u
#define CSR_MDCCMECT                   0x7F2

#define COMM_SCRATCHPAD_ADDR           0xF0047000u
#define COMM_HANDSHAKE_ADDR            0xF0047004u

#define TARGET_ADDR_PHASE1             0xF0047400u
#define TARGET_ADDR_PHASE2             0xF0047410u
#define TARGET_ADDR_PHASE3             0xF0047420u
#define TARGET_ADDR_PHASE4             0xF0047430u
#define TARGET_ADDR_PHASE5             0xF0047440u

static volatile uint32_t *const kScratchpad = (volatile uint32_t *)COMM_SCRATCHPAD_ADDR;
static volatile uint32_t *const kHandshake  = (volatile uint32_t *)COMM_HANDSHAKE_ADDR;
static uint32_t g_seq_id = 0;

/**
 * Sends a command to the testbench via `tohost` mailbox and waits for handshake.
 *
 * @param cmd Opcode (bits 7:0)
 * @param payload Additional payload (bits 15:8)
 * @return Value returned by testbench in scratchpad (`0xF0047000`)
 */
static uint32_t send_tb_command(uint8_t cmd, uint8_t payload) {
  g_seq_id++;
  uint32_t msg = ((uint32_t)g_seq_id << 16) | ((uint32_t)payload << 8) | (uint32_t)cmd;
  tohost = msg;
  while (*kHandshake != g_seq_id) {
    // Wait for testbench to complete transaction
  }
  return *kScratchpad;
}

/**
 * Arms a verification stimulus in the testbench.
 *
 * @param cmd Arm mailbox opcode (0xB5 - 0xB9)
 */
static inline void arm_phase(uint8_t cmd) {
  (void)send_tb_command(cmd, 0);
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
 * Queries cumulative `dccm_write_readback_error` pulse count from testbench.
 */
static inline uint32_t get_error_pulse_count(void) {
  return send_tb_command(MAILBOX_CMD_GET_PULSES, 0);
}

/**
 * Reads the DCCM correctable ECC error counter CSR (`mdccmect`, `0x7F2`).
 */
static inline uint32_t read_mdccmect(void) {
  uint32_t val;
  __asm__ volatile("csrr %0, %1" : "=r"(val) : "i"(CSR_MDCCMECT));
  return val;
}

/**
 * Default trap handler.
 */
void trap_handler(void) {
  uint32_t mcause;
  __asm__ volatile("csrr %0, mcause" : "=r"(mcause));
  printf("[TRAP] Unexpected trap encountered! mcause=0x%08x\n", mcause);
  tohost = 1;
  while (true) {}
}

int main(void) {
  *kScratchpad = 0u;
  *kHandshake  = 0u;
  __asm__ volatile("fence rw, rw" ::: "memory");

  printf("\n================================================================\n");
  printf("=== Starting DCCM Write Readback System Integration Tests (#512) ===\n");
  printf("================================================================\n\n");

  // Enable Debug Module (`dmcontrol.dmactive = 1`) via standard DMI write to 0x10
  (void)send_tb_command(MAILBOX_CMD_DMI_WRITE, DMI_REG_DMCONTROL);

  // -------------------------------------------------------------
  // Phase 1: DMA Write Collision (WR_SYS_001 #512)
  // -------------------------------------------------------------
  printf("[TEST] Phase 1: Real DMA Write Collision while check pending (WR_SYS_001)...\n");
  volatile uint32_t *target_p1 = (volatile uint32_t *)TARGET_ADDR_PHASE1;
  *target_p1 = 0x11112222u;
  __asm__ volatile("fence rw, rw" ::: "memory");

  tb_reset_rdbk_counters();
  uint32_t pulses_before_p1 = get_error_pulse_count();
  arm_phase(MAILBOX_CMD_ARM_DMA_WR_COLL);
  uint32_t val_p1 = 0x33334444u;
  __asm__ volatile(
      ".balign 16\n\t"
      "sw   %[val], 0(%[addr])\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      :
      : [val] "r"(val_p1), [addr] "r"(target_p1)
      : "memory");
  __asm__ volatile("fence rw, rw" ::: "memory");

  uint32_t p1_arm   = tb_get_rdbk_counter(RDBK_CNT_ARM);
  uint32_t p1_steal = tb_get_rdbk_counter(RDBK_CNT_STEAL);
  uint32_t p1_mem   = *target_p1;
  if (p1_arm == 0u || p1_steal == 0u || p1_mem != 0xAABBCCDDu ||
      get_error_pulse_count() != pulses_before_p1) {
    printf("[FAIL] Phase 1: DMA write collision failed (arm=%u, steal=%u, mem=0x%08x, exp=0xAABBCCDD)!\n",
           p1_arm, p1_steal, p1_mem);
    tohost = 1;
    return 1;
  }
  printf("[PASS] Phase 1 complete: DMA write stalled during check (arm=%u, steal=%u) and committed 0x%08x afterward.\n\n",
         p1_arm, p1_steal, p1_mem);

  // -------------------------------------------------------------
  // Phase 2: DMA Read Collision - Snoop Path (WR_SYS_002A #512)
  // -------------------------------------------------------------
  printf("[TEST] Phase 2: Real DMA Read Collision Snoop Path (WR_SYS_002A)...\n");
  volatile uint32_t *target_p2 = (volatile uint32_t *)TARGET_ADDR_PHASE2;
  *target_p2 = 0x55556666u;
  __asm__ volatile("fence rw, rw" ::: "memory");

  tb_reset_rdbk_counters();
  uint32_t pulses_before_p2 = get_error_pulse_count();
  arm_phase(MAILBOX_CMD_ARM_DMA_RD_SNOOP);
  uint32_t val_p2 = 0x77778888u;
  __asm__ volatile(
      ".balign 16\n\t"
      "sw   %[val], 0(%[addr])\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      :
      : [val] "r"(val_p2), [addr] "r"(target_p2)
      : "memory");
  __asm__ volatile("fence rw, rw" ::: "memory");

  uint32_t p2_arm      = tb_get_rdbk_counter(RDBK_CNT_ARM);
  uint32_t p2_snoop_lo = tb_get_rdbk_counter(RDBK_CNT_SNOOP_LO);
  uint32_t p2_steal    = tb_get_rdbk_counter(RDBK_CNT_STEAL);
  uint32_t p2_mem      = *target_p2;
  if (p2_arm != 1u || p2_snoop_lo != 1u || p2_steal != 0u ||
      p2_mem != val_p2 || get_error_pulse_count() != pulses_before_p2) {
    printf("[FAIL] Phase 2: DMA read snoop path failed (arm=%u, snoop_lo=%u, steal=%u, mem=0x%08x)!\n",
           p2_arm, p2_snoop_lo, p2_steal, p2_mem);
    tohost = 1;
    return 2;
  }
  printf("[PASS] Phase 2 complete: Real DMA read snoop path verified (arm=%u, snoop_lo=%u, steal=%u).\n\n",
         p2_arm, p2_snoop_lo, p2_steal);

  // -------------------------------------------------------------
  // Phase 3: DMA Read Collision - Steal Deferral (WR_SYS_002B #512)
  // -------------------------------------------------------------
  printf("[TEST] Phase 3: Real DMA Read Collision Steal Deferral (WR_SYS_002B)...\n");
  volatile uint32_t *target_p3 = (volatile uint32_t *)TARGET_ADDR_PHASE3;
  *target_p3 = 0x9999AAAAu;
  __asm__ volatile("fence rw, rw" ::: "memory");

  tb_reset_rdbk_counters();
  uint32_t pulses_before_p3 = get_error_pulse_count();
  arm_phase(MAILBOX_CMD_ARM_DMA_RD_STEAL);
  uint32_t val_p3 = 0xBBBBCCCCu;
  __asm__ volatile(
      ".balign 16\n\t"
      "sw   %[val], 0(%[addr])\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      :
      : [val] "r"(val_p3), [addr] "r"(target_p3)
      : "memory");
  __asm__ volatile("fence rw, rw" ::: "memory");

  uint32_t p3_arm   = tb_get_rdbk_counter(RDBK_CNT_ARM);
  uint32_t p3_defer = tb_get_rdbk_counter(RDBK_CNT_DEFER);
  uint32_t p3_steal = tb_get_rdbk_counter(RDBK_CNT_STEAL);
  uint32_t p3_mem   = *target_p3;
  if (p3_arm != 1u || p3_defer == 0u || p3_steal != 1u ||
      p3_mem != val_p3 || get_error_pulse_count() != pulses_before_p3) {
    printf("[FAIL] Phase 3: DMA read steal priority deferral failed (arm=%u, defer=%u, steal=%u, mem=0x%08x)!\n",
           p3_arm, p3_defer, p3_steal, p3_mem);
    tohost = 1;
    return 3;
  }
  printf("[PASS] Phase 3 complete: Real DMA read priority over steal verified (defer=%u, steal=%u).\n\n",
         p3_defer, p3_steal);

  // -------------------------------------------------------------
  // Phase 4: ECC 1-Bit Correction - Snoop Path (WR_SYS_003A #512)
  // -------------------------------------------------------------
  printf("[TEST] Phase 4: Real ECC 1-Bit Correction Snoop Path (WR_SYS_003A)...\n");
  volatile uint32_t *target_p4 = (volatile uint32_t *)TARGET_ADDR_PHASE4;
  volatile uint32_t *adj_p4    = (volatile uint32_t *)(TARGET_ADDR_PHASE4 + 4u);
  *target_p4 = 0xCAFE0001u;
  *adj_p4    = 0x11223344u;
  __asm__ volatile("fence rw, rw" ::: "memory");

  tb_reset_rdbk_counters();
  uint32_t ecc_cnt_before_p4 = read_mdccmect();
  uint32_t pulses_before_p4  = get_error_pulse_count();
  arm_phase(MAILBOX_CMD_ARM_ECC_SNOOP);

  uint32_t val_p4 = 0xCAFE0002u;
  uint32_t snooped_ecc_val = 0;
  uint32_t dummy_p4 = 0;
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
      "nop\n\t"
      "nop\n\t"
      : [res] "=&r"(snooped_ecc_val), [dum] "=&r"(dummy_p4)
      : [val] "r"(val_p4), [addr] "r"(target_p4)
      : "memory");
  __asm__ volatile("fence rw, rw" ::: "memory");

  uint32_t ecc_cnt_after_p4  = read_mdccmect();
  uint32_t p4_snoop_lo       = tb_get_rdbk_counter(RDBK_CNT_SNOOP_LO);
  uint32_t p4_steal          = tb_get_rdbk_counter(RDBK_CNT_STEAL);
  uint32_t pulses_after_p4   = get_error_pulse_count();
  uint32_t dmi_status_p4     = send_tb_command(MAILBOX_CMD_DMI_READ, DMI_REG_FAULT_STATUS);
  // Clear sticky DMI fault status after verifying Phase 4 snoop fault detection
  (void)send_tb_command(MAILBOX_CMD_DMI_WRITE, DMI_REG_FAULT_STATUS);

  // Re-read `target_p4` to confirm the 1-bit ECC correction scrubbed the word in-place in DCCM SRAM
  uint32_t scrubbed_p4_val       = *target_p4;
  uint32_t ecc_cnt_after_p4_rerd = read_mdccmect();

  if (p4_snoop_lo != 1u || p4_steal != 0u ||
      snooped_ecc_val != val_p4 || scrubbed_p4_val != val_p4 ||
      ecc_cnt_after_p4 != (ecc_cnt_before_p4 + 1u) ||
      ecc_cnt_after_p4_rerd != ecc_cnt_after_p4 ||
      pulses_after_p4 != (pulses_before_p4 + 1u) ||
      (dmi_status_p4 & 0x80000000u) == 0u ||
      (dmi_status_p4 & 0xFFFFu) != (TARGET_ADDR_PHASE4 & 0xFFFFu)) {
    printf("[FAIL] Phase 4: ECC snoop path failed (snoop_lo=%u, steal=%u, val=0x%08x, ecc_cnt=%u->%u->%u, dmi=0x%08x)!\n",
           p4_snoop_lo, p4_steal, snooped_ecc_val,
           ecc_cnt_before_p4, ecc_cnt_after_p4, ecc_cnt_after_p4_rerd, dmi_status_p4);
    tohost = 1;
    return 4;
  }
  printf("[PASS] Phase 4 complete: ECC 1-bit snoop path, fault detection (dmi=0x%08x), and scrub verified.\n\n",
         dmi_status_p4);

  // -------------------------------------------------------------
  // Phase 5: ECC 1-Bit Correction - Steal Deferral (WR_SYS_003B #512)
  // -------------------------------------------------------------
  printf("[TEST] Phase 5: Real ECC 1-Bit Correction Steal Deferral (WR_SYS_003B)...\n");
  volatile uint32_t *target_p5 = (volatile uint32_t *)TARGET_ADDR_PHASE5;
  volatile uint32_t *ecc_p5    = (volatile uint32_t *)(TARGET_ADDR_PHASE5 + 4u);
  *target_p5 = 0xBEEF0001u;
  __asm__ volatile("fence rw, rw" ::: "memory");

  tb_reset_rdbk_counters();
  uint32_t ecc_cnt_before_p5 = read_mdccmect();
  uint32_t pulses_before_p5  = get_error_pulse_count();
  arm_phase(MAILBOX_CMD_ARM_ECC_STEAL);

  uint32_t val_p5 = 0xBEEF0002u;
  uint32_t corrected_p5_val = 0;
  __asm__ volatile(
      ".balign 16\n\t"
      "sw   %[val], 0(%[addr])\n\t"
      "lw   %[res], 4(%[addr])\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      : [res] "=&r"(corrected_p5_val)
      : [val] "r"(val_p5), [addr] "r"(target_p5)
      : "memory");
  __asm__ volatile("fence rw, rw" ::: "memory");

  uint32_t ecc_cnt_after_p5 = read_mdccmect();
  uint32_t p5_defer         = tb_get_rdbk_counter(RDBK_CNT_DEFER);
  uint32_t p5_steal         = tb_get_rdbk_counter(RDBK_CNT_STEAL);
  // Read scrubbed word at 0xF0047444 again to confirm SRAM was scrubbed in-place
  uint32_t scrubbed_p5_val       = *ecc_p5;
  uint32_t ecc_cnt_after_rescrub = read_mdccmect();

  if (p5_defer == 0u || p5_steal != 1u ||
      *target_p5 != val_p5 ||
      corrected_p5_val != 0x12345678u ||
      scrubbed_p5_val != 0x12345678u ||
      ecc_cnt_after_p5 != (ecc_cnt_before_p5 + 1u) ||
      ecc_cnt_after_rescrub != ecc_cnt_after_p5 ||
      get_error_pulse_count() != pulses_before_p5) {
    printf("[FAIL] Phase 5: ECC steal deferral failed (defer=%u, steal=%u, corr=0x%08x, scrub=0x%08x, ecc_cnt=%u->%u->%u)!\n",
           p5_defer, p5_steal, corrected_p5_val, scrubbed_p5_val,
           ecc_cnt_before_p5, ecc_cnt_after_p5, ecc_cnt_after_rescrub);
    tohost = 1;
    return 5;
  }
  printf("[PASS] Phase 5 complete: Real ECC 1-bit correction steal deferral (defer=%u, steal=%u) & SRAM scrub verified.\n\n",
         p5_defer, p5_steal);

  printf("================================================================\n");
  printf("=== ALL 5 PHASES PASSED: System Integration (DMA & ECC) Verified ===\n");
  printf("================================================================\n");
  printf("TEST_PASSED\n");

  tohost = 0xFFu;  // Signal completion
  return 0;
}
