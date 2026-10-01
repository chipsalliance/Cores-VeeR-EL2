/* SPDX-License-Identifier: Apache-2.0
 * Copyright 2026 Google LLC
 *
 * DCCM Write Readback Fault Injection & DMI Diagnostic Verification (#512)
 * Author: Samip Modi (samipmodi@google.com)
 *
 * Description:
 * Comprehensive bare-metal verification of the VeeR EL2 DCCM write-readback
 * fault injection, DMI diagnostic registers (0x48-0x4A), and Dual-Core Lockstep
 * (DCLS) asymmetric comparator detection.
 *
 * Test Phases:
 * 1. Phase 1: Enable DMI `dmcontrol.dmactive` (0x10) and verify pristine reset state of DMI 0x48-0x4A (all zero).
 * 2. Phase 2: Inject write-skip fault, verify `dccm_write_readback_error` pulse and fault capture in 0x48-0x4A.
 * 3. Phase 3: First-fault-wins retention: inject second fault, verify 0x48-0x4A retain original fault.
 * 4. Phase 4: W1C clear on 0x48[31], verify valid bit returns to 0.
 * 5. Phase 5: Subsequent fault capture: inject fault after clear, verify new fault captured in 0x48-0x4A.
 * 6. Phase 6: DCLS lockstep comparator verification: perturb subordinate `dccm_wr_rdbk_data_ff` via
 *    mailbox 0x92 (case 206), execute a real DCCM store so the shadow core naturally computes
 *    `dccm_write_readback_error = 1`, and verify the resulting `corruption_detected_o` PIC IRQ #2 trap.
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <defines.h>

extern volatile uint32_t tohost;
extern void _trap_handler(void);

#define CMD_INJ_LOCKSTEP          0x92u
#define CMD_INJ_CLEAR             0x95u
#define DCLS_CASE_RDBK_DATA_FF    206u

#define MAILBOX_CMD_ARM_WR_SKIP   0xB0u
#define MAILBOX_CMD_DMI_READ      0xB1u
#define MAILBOX_CMD_DMI_WRITE     0xB2u
#define MAILBOX_CMD_GET_PULSES    0xB4u

#define DMI_REG_DMCONTROL         0x10u
#define DMI_REG_DCCM_STATUS       0x48u
#define DMI_REG_DCCM_DATA         0x49u
#define DMI_REG_DCCM_ECC          0x4Au

#define COMM_SCRATCHPAD_ADDR      0xF0047000u
#define COMM_HANDSHAKE_ADDR       0xF0047004u

#define TARGET_ADDR_PHASE2        0xF0047400u
#define TARGET_ADDR_PHASE3        0xF0047500u
#define TARGET_ADDR_PHASE5        0xF0047600u
#define MEIVT_BASE_ADDR           0xF0047800u

#define MCAUSE_M_EXT_INT          0x8000000Bu

static volatile uint32_t *const kScratchpad = (volatile uint32_t *)COMM_SCRATCHPAD_ADDR;
static volatile uint32_t *const kHandshake  = (volatile uint32_t *)COMM_HANDSHAKE_ADDR;

static volatile uint32_t *const kPicThreshold  = (volatile uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIPT_OFFSET);
static volatile uint32_t *const kPicGateway    = (volatile uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIGWCTRL_OFFSET);
static volatile uint32_t *const kPicClrGateway = (volatile uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIGWCLR_OFFSET);
static volatile uint32_t *const kPicPriority   = (volatile uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIPL_OFFSET);
static volatile uint32_t *const kPicEnable     = (volatile uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIE_OFFSET);

static uint32_t g_seq_id = 0;
static volatile bool g_expect_dcls_trap = false;

/**
 * Sends a command to the testbench via `tohost` and waits for completion.
 *
 * @param cmd Opcode (0xB0 - 0xB4)
 * @param dmi_addr 7-bit DMI address (for B1/B2)
 * @return Value written to scratchpad by testbench
 */
static uint32_t send_tb_command(uint8_t cmd, uint8_t dmi_addr) {
  g_seq_id++;
  uint32_t payload = ((uint32_t)g_seq_id << 16) |
                     ((uint32_t)(dmi_addr & 0x7Fu) << 8) |
                     (uint32_t)cmd;
  tohost = payload;
  while (*kHandshake != g_seq_id) {
    // Wait for testbench to complete transaction
  }
  return *kScratchpad;
}

/**
 * Reads a 32-bit DMI register via testbench mailbox cycle.
 *
 * @param addr 7-bit DMI register address
 * @return Register contents
 */
static inline uint32_t dmi_read(uint8_t addr) {
  return send_tb_command(MAILBOX_CMD_DMI_READ, addr);
}

/**
 * Performs a DMI write to the specified register (`dmactive=1` for `0x10`, W1C for `0x48`).
 *
 * @param addr 7-bit DMI register address
 */
static inline void dmi_write(uint8_t addr) {
  (void)send_tb_command(MAILBOX_CMD_DMI_WRITE, addr);
}

/**
 * Arms DCCM write-skip for the next DCCM store.
 */
static inline void arm_write_skip(void) {
  (void)send_tb_command(MAILBOX_CMD_ARM_WR_SKIP, 0);
}

/**
 * Queries cumulative `dccm_write_readback_error` pulse count from testbench.
 *
 * @return Cumulative pulse count
 */
static inline uint32_t get_error_pulse_count(void) {
  return send_tb_command(MAILBOX_CMD_GET_PULSES, 0);
}

/**
 * Trap handler for expected Phase 6 DCLS lockstep interrupt and unexpected exceptions.
 */
void trap_handler(void) {
  uint32_t mcause;
  __asm__ volatile("csrr %0, mcause" : "=r"(mcause));

  if (g_expect_dcls_trap && mcause == MCAUSE_M_EXT_INT) {
    tohost = CMD_INJ_CLEAR;
    __asm__ volatile("csrw mstatus, zero");
    kPicClrGateway[2] = 0;
    printf("[TEST] Caught expected DCLS lockstep interrupt trap (mcause=0x%08x)\n", mcause);
    printf("[PASS] Phase 6 complete: DCLS comparator verified.\n\n");
    printf("================================================================\n");
    printf("=== ALL 6 PHASES PASSED: DCCM Write Readback & DMI Verified ====\n");
    printf("================================================================\n");
    tohost = 0xFFu;
    while (true) {}
  }

  printf("[TRAP] Unexpected trap encountered! mcause=0x%08x\n", mcause);
  tohost = 1;
  while (true) {}
}

int main(void) {
  *kScratchpad = 0u;
  *kHandshake = 0u;
  __asm__ volatile("fence rw, rw" ::: "memory");

  printf("\n================================================================\n");
  printf("=== Starting DCCM Write Readback Fault & DMI Tests (#512) ===\n");
  printf("================================================================\n\n");

  // Enable Debug Module (`dmcontrol.dmactive = 1`) via standard DMI write to 0x10
  dmi_write(DMI_REG_DMCONTROL);

  // -------------------------------------------------------------
  // Phase 1: Pristine Reset State Verification
  // -------------------------------------------------------------
  printf("[TEST] Phase 1: Checking pristine reset state of DMI 0x48-0x4A...\n");
  uint32_t pulses = get_error_pulse_count();
  if (pulses != 0) {
    printf("[FAIL] Initial error pulse count non-zero: %d\n", pulses);
    tohost = 1;
    return 1;
  }

  uint32_t r48 = dmi_read(DMI_REG_DCCM_STATUS);
  uint32_t r49 = dmi_read(DMI_REG_DCCM_DATA);
  uint32_t r4a = dmi_read(DMI_REG_DCCM_ECC);
  printf("[TEST] Pristine DMI: 0x48=0x%08x, 0x49=0x%08x, 0x4A=0x%08x\n", r48, r49, r4a);

  if (r48 != 0 || r49 != 0 || r4a != 0) {
    printf("[FAIL] DMI registers not zero on reset!\n");
    tohost = 1;
    return 1;
  }
  printf("[PASS] Phase 1 complete: Pristine reset state verified.\n\n");

  // -------------------------------------------------------------
  // Phase 2: Write-Skip Fault Injection & Capture
  // -------------------------------------------------------------
  printf("[TEST] Phase 2: Injecting write-skip fault at 0x%08x...\n", TARGET_ADDR_PHASE2);
  volatile uint32_t *target_p2 = (volatile uint32_t *)TARGET_ADDR_PHASE2;
  *target_p2 = 0x00000000u;
  __asm__ volatile("fence rw, rw" ::: "memory");

  // Arm write-skip and perform store
  arm_write_skip();
  *target_p2 = 0xAABBCCDDu;
  __asm__ volatile("fence rw, rw" ::: "memory");

  // Verify error pulse
  pulses = get_error_pulse_count();
  if (pulses != 1) {
    printf("[FAIL] Expected 1 error pulse, got %d\n", pulses);
    tohost = 1;
    return 2;
  }

  // Verify DMI registers
  r48 = dmi_read(DMI_REG_DCCM_STATUS);
  r49 = dmi_read(DMI_REG_DCCM_DATA);
  r4a = dmi_read(DMI_REG_DCCM_ECC);
  printf("[TEST] Captured DMI: 0x48=0x%08x, 0x49=0x%08x, 0x4A=0x%08x\n", r48, r49, r4a);

  if ((r48 & 0x80000000u) == 0) {
    printf("[FAIL] 0x48 bit 31 (valid) not set!\n");
    tohost = 1;
    return 2;
  }
  uint16_t captured_addr = (uint16_t)(r48 & 0xFFFFu);
  if (captured_addr != (TARGET_ADDR_PHASE2 & 0xFFFFu)) {
    printf("[FAIL] 0x48 address mismatch: expected 0x%04x, got 0x%04x\n",
           (uint32_t)(TARGET_ADDR_PHASE2 & 0xFFFFu), captured_addr);
    tohost = 1;
    return 2;
  }
#ifdef RV_DCCM_ADDR_XOR
  uint32_t p2_idx = (TARGET_ADDR_PHASE2 >> 2) & ((1u << (RV_DCCM_BITS - 2)) - 1u);
  uint32_t expected_r49 = (p2_idx << (RV_DCCM_BITS - 2)) | p2_idx;
#else
  uint32_t expected_r49 = 0u;
#endif
  if (r49 != expected_r49) {
    printf("[FAIL] 0x49 data mismatch: expected 0x%08x, got 0x%08x\n", expected_r49, r49);
    tohost = 1;
    return 2;
  }
  printf("[PASS] Phase 2 complete: Write-skip fault captured in 0x48-0x4A.\n\n");

  // -------------------------------------------------------------
  // Phase 3: First-Fault-Wins Retention
  // -------------------------------------------------------------
  printf("[TEST] Phase 3: First-fault-wins retention with second fault...\n");
  volatile uint32_t *target_p3 = (volatile uint32_t *)TARGET_ADDR_PHASE3;
  *target_p3 = 0x00000000u;
  __asm__ volatile("fence rw, rw" ::: "memory");

  arm_write_skip();
  *target_p3 = 0x11223344u;
  __asm__ volatile("fence rw, rw" ::: "memory");

  pulses = get_error_pulse_count();
  if (pulses != 2) {
    printf("[FAIL] Expected 2 error pulses, got %d\n", pulses);
    tohost = 1;
    return 3;
  }

  // 0x48-0x4A must still retain Phase 2 fault
  r48 = dmi_read(DMI_REG_DCCM_STATUS);
  r49 = dmi_read(DMI_REG_DCCM_DATA);
  r4a = dmi_read(DMI_REG_DCCM_ECC);
  printf("[TEST] Retained DMI: 0x48=0x%08x, 0x49=0x%08x, 0x4A=0x%08x\n", r48, r49, r4a);

  captured_addr = (uint16_t)(r48 & 0xFFFFu);
  if (captured_addr != (TARGET_ADDR_PHASE2 & 0xFFFFu)) {
    printf("[FAIL] First fault not retained! Addr changed to 0x%04x\n", captured_addr);
    tohost = 1;
    return 3;
  }
  if (r49 != expected_r49) {
    printf("[FAIL] First fault data not retained! Data changed to 0x%08x\n", r49);
    tohost = 1;
    return 3;
  }
  printf("[PASS] Phase 3 complete: First fault successfully retained across second fault.\n\n");

  // -------------------------------------------------------------
  // Phase 4: W1C Clear on 0x48[31]
  // -------------------------------------------------------------
  printf("[TEST] Phase 4: Clearing fault register via DMI W1C on 0x48...\n");
  dmi_write(DMI_REG_DCCM_STATUS);

  r48 = dmi_read(DMI_REG_DCCM_STATUS);
  printf("[TEST] After clear DMI: 0x48=0x%08x\n", r48);
  if ((r48 & 0x80000000u) != 0) {
    printf("[FAIL] 0x48 bit 31 still set after W1C clear!\n");
    tohost = 1;
    return 4;
  }
  printf("[PASS] Phase 4 complete: W1C clear successfully cleared valid bit.\n\n");

  // -------------------------------------------------------------
  // Phase 5: Subsequent Fault Capture
  // -------------------------------------------------------------
  printf("[TEST] Phase 5: Subsequent fault capture at 0x%08x...\n", TARGET_ADDR_PHASE5);
  volatile uint32_t *target_p5 = (volatile uint32_t *)TARGET_ADDR_PHASE5;
  *target_p5 = 0x00000000u;
  __asm__ volatile("fence rw, rw" ::: "memory");

  arm_write_skip();
  *target_p5 = 0x55667788u;
  __asm__ volatile("fence rw, rw" ::: "memory");

  pulses = get_error_pulse_count();
  if (pulses != 3) {
    printf("[FAIL] Expected 3 error pulses, got %d\n", pulses);
    tohost = 1;
    return 5;
  }

  r48 = dmi_read(DMI_REG_DCCM_STATUS);
  r49 = dmi_read(DMI_REG_DCCM_DATA);
  r4a = dmi_read(DMI_REG_DCCM_ECC);
  printf("[TEST] Subsequent DMI: 0x48=0x%08x, 0x49=0x%08x, 0x4A=0x%08x\n", r48, r49, r4a);

  if ((r48 & 0x80000000u) == 0) {
    printf("[FAIL] 0x48 valid bit not set after subsequent fault!\n");
    tohost = 1;
    return 5;
  }
  captured_addr = (uint16_t)(r48 & 0xFFFFu);
  if (captured_addr != (TARGET_ADDR_PHASE5 & 0xFFFFu)) {
    printf("[FAIL] 0x48 address mismatch: expected 0x%04x, got 0x%04x\n",
           (uint32_t)(TARGET_ADDR_PHASE5 & 0xFFFFu), captured_addr);
    tohost = 1;
    return 5;
  }
  printf("[PASS] Phase 5 complete: Subsequent fault captured after W1C clear.\n\n");

  // -------------------------------------------------------------
  // Phase 6: DCLS Asymmetric Lockstep Comparison
  // -------------------------------------------------------------
#ifdef RV_LOCKSTEP_ENABLE
  printf("[TEST] Phase 6: Testing DCLS asymmetric lockstep error detection (Case 206)...\n");
  volatile uint32_t *fir_table = (volatile uint32_t *)MEIVT_BASE_ADDR;
  fir_table[2] = (uint32_t)&_trap_handler;
  __asm__ volatile("fence rw, rw" ::: "memory");
  __asm__ volatile("csrw 0xbc8, %0" : : "r"(MEIVT_BASE_ADDR));

  *kPicThreshold = 1;
  kPicGateway[2] = (1u << 1) | 0u;
  kPicClrGateway[2] = 0;
  kPicPriority[2] = 7;
  kPicEnable[2] = 1;

  __asm__ volatile(
      "li t0, 0x800\n\t"
      "csrs mie, t0\n\t"
      "csrsi mstatus, 8\n\t"
      :
      :
      : "t0");

  g_expect_dcls_trap = true;
  tohost = (DCLS_CASE_RDBK_DATA_FF << 8) | CMD_INJ_LOCKSTEP;
  *target_p5 = 0x12345678u;
  __asm__ volatile("fence rw, rw" ::: "memory");

  for (volatile int i = 0; i < 500; i++) {
    __asm__ volatile("nop");
  }

  printf("[FAIL] Phase 6: DCLS comparator failed to trigger lockstep interrupt trap!\n");
  tohost = 1;
  return 6;
#else
  printf("[TEST] Phase 6: DCLS lockstep disabled in build; skipping asymmetric trap check.\n");
  printf("================================================================\n");
  printf("=== ALL PHASES PASSED: DCCM Write Readback & DMI Verified ======\n");
  printf("================================================================\n");
  return 0;
#endif
}
