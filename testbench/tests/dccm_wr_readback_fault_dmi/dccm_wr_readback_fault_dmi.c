/* SPDX-License-Identifier: Apache-2.0
 * Copyright 2026 Google LLC
 *
 * DCCM Write Readback Fault Injection & DMI Diagnostic Verification (#512)
 * Author: Samip Modi (samipmodi@google.com)
 *
 * Description:
 * Comprehensive bare-metal verification of the VeeR EL2 DCCM write-readback
 * fault injection, DMI diagnostic registers (0x48-0x4A), and Dual-Core Lockstep
 * (DCLS) delayed comparator equivalence and directional mismatch detection.
 *
 * Test Phases:
 * 1. Phase 1: Enable DMI `dmcontrol.dmactive` (0x10) and verify pristine reset state of DMI 0x48-0x4A (all zero).
 * 2. Phase 2: Inject write-skip fault, verify `dccm_write_readback_error` pulse and fault capture in 0x48-0x4A.
 * 3. Phase 3: First-fault-wins retention: inject second fault, verify 0x48-0x4A retain original fault.
 * 4. Phase 4: W1C clear on 0x48[31], verify valid bit returns to 0.
 * 5. Phase 5: Subsequent fault capture: inject fault after clear, verify new fault captured in 0x48-0x4A.
 * 6. Phase 6: Comprehensive DCLS delayed lockstep comparator verification:
 *    - Phase 6A: Verify symmetric/no-fault lockstep equivalence across Phases 1-5 (`sym_err_match == 3`,
 *      zero directional mismatches) and clear Phase 5 DMI status via W1C.
 *    - Phase 6B: Perturb main-core `dccm_wr_rdbk_data_ff` via mailbox 0x91 (case 206), execute a real DCCM
 *      store so `delayed_main_core_outputs.dccm_write_readback_error == 1` vs `shadow == 0` across the
 *      `LockstepDelay` pipeline, and verify PIC IRQ #2 trap #1 and RTL counter `main_err_mismatch == 1`.
 *    - Phase 6C: Read DMI `0x48` while only main core holds the latched fault from Phase 6B, verifying
 *      `delayed_main_core_outputs.dmi_reg_rdata != shadow_core_outputs.dmi_reg_rdata` triggers PIC IRQ #2
 *      trap #2 and RTL counter `dmi_rdata_mismatch >= 1`.
 *    - Phase 6D: Perturb shadow-core `dccm_wr_rdbk_data_ff` via mailbox 0x92 (case 206), execute a real DCCM
 *      store so `delayed_main == 0` vs `shadow_core_outputs.dccm_write_readback_error == 1`, and verify
 *      PIC IRQ #2 trap #3 and RTL counter `shadow_err_mismatch == 1`.
 *    - Phase 6E: Re-arm clean lockstep equivalence and verify subsequent stores and DMI reads complete with
 *      zero false DCLS traps.
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <defines.h>

extern volatile uint32_t tohost;
extern void _trap_handler(void);

#define CMD_INJ_VEER              0x91u
#define CMD_INJ_LOCKSTEP          0x92u
#define CMD_INJ_CLEAR             0x95u
#define DCLS_CASE_RDBK_DATA_FF    206u

#define MAILBOX_CMD_ARM_WR_SKIP   0xB0u
#define MAILBOX_CMD_DMI_READ      0xB1u
#define MAILBOX_CMD_DMI_WRITE     0xB2u
#define MAILBOX_CMD_GET_PULSES    0xB4u
#define MAILBOX_CMD_RDBK_COUNTERS 0xBBu

#define RDBK_CNT_RESET            0u
#define RDBK_CNT_DCLS_SYM_MATCH   7u
#define RDBK_CNT_DCLS_MAIN_MISM   8u
#define RDBK_CNT_DCLS_SHDW_MISM   9u
#define RDBK_CNT_DCLS_DMI_MISM    10u

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
static volatile bool g_dcls_clear_dmi_in_trap = false;
static volatile uint32_t g_dcls_trap_count = 0;

/**
 * Sends a command to the testbench via `tohost` and waits for completion.
 *
 * @param cmd Opcode (0xB0 - 0xBB)
 * @param subcmd 7-bit DMI address (for B1/B2) or counter selector (for BB)
 * @return Value written to scratchpad by testbench
 */
static uint32_t send_tb_command(uint8_t cmd, uint8_t subcmd) {
  g_seq_id++;
  uint32_t seq = g_seq_id;
  uint32_t payload = (seq << 16) |
                     ((uint32_t)(subcmd & 0x7Fu) << 8) |
                     (uint32_t)cmd;
  tohost = payload;
  while (*kHandshake != seq) {
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
 * Queries or resets testbench RTL event counters (`0xBB`).
 *
 * @param sel Counter selector (`0` = reset, `7..10` = DCLS counters)
 * @return Counter value
 */
static inline uint32_t rdbk_counter_cmd(uint8_t sel) {
  return send_tb_command(MAILBOX_CMD_RDBK_COUNTERS, sel);
}

/**
 * Computes the 7-bit SECDED ECC syndrome for a 32-bit DCCM word (`rvecc_encode`).
 *
 * @param data 32-bit data word (before `RV_DCCM_ADDR_XOR` infection)
 * @return 7-bit ECC syndrome (`[6:0]`)
 */
static uint32_t compute_dccm_ecc32(uint32_t data) {
  uint32_t p0 = (uint32_t)__builtin_parity(data & 0x56AAAD5Bu);
  uint32_t p1 = (uint32_t)__builtin_parity(data & 0x9B33366Du);
  uint32_t p2 = (uint32_t)__builtin_parity(data & 0xE3C3C78Eu);
  uint32_t p3 = (uint32_t)__builtin_parity(data & 0x03FC07F0u);
  uint32_t p4 = (uint32_t)__builtin_parity(data & 0x03FFF800u);
  uint32_t p5 = (uint32_t)__builtin_parity(data & 0xFC000000u);
  uint32_t synd5_0 = p0 | (p1 << 1) | (p2 << 2) | (p3 << 3) | (p4 << 4) | (p5 << 5);
  uint32_t p6 = (uint32_t)__builtin_parity(data) ^ (uint32_t)__builtin_parity(synd5_0);
  return synd5_0 | (p6 << 6);
}

/**
 * Machine-mode interrupt handler for expected Phase 6 DCLS lockstep interrupts (`mcause=0x8000000B`).
 * Clears active fault injection forces, optionally clears asymmetric DMI status via W1C, clears the
 * PIC gateway, increments `g_dcls_trap_count`, and returns via `mret`.
 */
void __attribute__((interrupt("machine"))) trap_handler(void) {
  uint32_t mcause;
  __asm__ volatile("csrr %0, mcause" : "=r"(mcause));

  if (g_expect_dcls_trap && mcause == MCAUSE_M_EXT_INT) {
    tohost = CMD_INJ_CLEAR;
    if (g_dcls_clear_dmi_in_trap) {
      dmi_write(DMI_REG_DCCM_STATUS);
      (void)dmi_read(DMI_REG_DCCM_STATUS);
      g_dcls_clear_dmi_in_trap = false;
    }
    for (volatile int i = 0; i < 40; i++) {
      __asm__ volatile("nop");
    }
    kPicClrGateway[2] = 0;
    __asm__ volatile("fence rw, rw" ::: "memory");
    g_dcls_trap_count++;
    g_expect_dcls_trap = false;
    return;
  }

  printf("[TRAP] Unexpected trap encountered! mcause=0x%08x\n", mcause);
  tohost = 1;
  while (true) {}
}

int main(void) {
  const uint32_t dccm_addr_mask = (1u << RV_DCCM_BITS) - 1u;
  const uint32_t r48_rsvd_mask  = 0x7FFFFFFFu & ~dccm_addr_mask;
  const uint32_t r4a_rsvd_mask  = 0xFFFFFF80u;

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

  // Verify DMI registers (0x48: [31]=valid, [30:DCCM_BITS]=0, [DCCM_BITS-1:0]=addr;
  // 0x49: [31:0]=data; 0x4A: [31:7]=0, [6:0]=ecc)
  r48 = dmi_read(DMI_REG_DCCM_STATUS);
  r49 = dmi_read(DMI_REG_DCCM_DATA);
  r4a = dmi_read(DMI_REG_DCCM_ECC);
  printf("[TEST] Captured DMI: 0x48=0x%08x, 0x49=0x%08x, 0x4A=0x%08x\n", r48, r49, r4a);

  if ((r48 & 0x80000000u) == 0u) {
    printf("[FAIL] 0x48 bit 31 (valid) not set!\n");
    tohost = 1;
    return 2;
  }
  if ((r48 & r48_rsvd_mask) != 0u) {
    printf("[FAIL] 0x48 reserved bits [30:DCCM_BITS] non-zero: 0x%08x\n", r48);
    tohost = 1;
    return 2;
  }
  uint32_t captured_addr = r48 & dccm_addr_mask;
  if (captured_addr != (TARGET_ADDR_PHASE2 & dccm_addr_mask)) {
    printf("[FAIL] 0x48 address mismatch: expected 0x%04x, got 0x%04x\n",
           (uint32_t)(TARGET_ADDR_PHASE2 & dccm_addr_mask), captured_addr);
    tohost = 1;
    return 2;
  }
#ifdef RV_DCCM_ADDR_XOR
  uint32_t p2_idx = (TARGET_ADDR_PHASE2 >> 2) & ((1u << (RV_DCCM_BITS - 2)) - 1u);
  uint32_t expected_r49 = (p2_idx << (RV_DCCM_BITS - 2)) | p2_idx;
#else
  uint32_t expected_r49 = 0u;
#endif
  uint32_t expected_r4a = compute_dccm_ecc32(0x00000000u);
  if (r49 != expected_r49) {
    printf("[FAIL] 0x49 data mismatch: expected 0x%08x, got 0x%08x\n", expected_r49, r49);
    tohost = 1;
    return 2;
  }
  if ((r4a & r4a_rsvd_mask) != 0u || r4a != expected_r4a) {
    printf("[FAIL] 0x4A ECC mismatch: expected 0x%08x, got 0x%08x\n", expected_r4a, r4a);
    tohost = 1;
    return 2;
  }
  printf("[PASS] Phase 2 complete: Write-skip fault captured in 0x48-0x4A.\n\n");

  // -------------------------------------------------------------
  // Phase 3: First-Fault-Wins Retention
  // -------------------------------------------------------------
  printf("[TEST] Phase 3: First-fault-wins retention with second fault...\n");
  volatile uint32_t *target_p3 = (volatile uint32_t *)TARGET_ADDR_PHASE3;
  *target_p3 = 0xDEADBEEFu;
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

  // 0x48-0x4A must still retain Phase 2 fault (address, data, and ECC)
  r48 = dmi_read(DMI_REG_DCCM_STATUS);
  r49 = dmi_read(DMI_REG_DCCM_DATA);
  r4a = dmi_read(DMI_REG_DCCM_ECC);
  printf("[TEST] Retained DMI: 0x48=0x%08x, 0x49=0x%08x, 0x4A=0x%08x\n", r48, r49, r4a);

  captured_addr = r48 & dccm_addr_mask;
  if ((r48 & 0x80000000u) == 0u || (r48 & r48_rsvd_mask) != 0u ||
      captured_addr != (TARGET_ADDR_PHASE2 & dccm_addr_mask)) {
    printf("[FAIL] First fault status/addr not retained! 0x48=0x%08x\n", r48);
    tohost = 1;
    return 3;
  }
  if (r49 != expected_r49) {
    printf("[FAIL] First fault data not retained! Data changed to 0x%08x\n", r49);
    tohost = 1;
    return 3;
  }
  if (r4a != expected_r4a) {
    printf("[FAIL] First fault ECC not retained! ECC changed to 0x%08x\n", r4a);
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
  if ((r48 & 0x80000000u) != 0u) {
    printf("[FAIL] 0x48 bit 31 still set after W1C clear!\n");
    tohost = 1;
    return 4;
  }
  if ((r48 & r48_rsvd_mask) != 0u) {
    printf("[FAIL] 0x48 reserved bits [30:DCCM_BITS] non-zero after W1C clear: 0x%08x\n", r48);
    tohost = 1;
    return 4;
  }
  printf("[PASS] Phase 4 complete: W1C clear successfully cleared valid bit.\n\n");

  // -------------------------------------------------------------
  // Phase 5: Subsequent Fault Capture (Non-Zero Data & 7-Bit ECC)
  // -------------------------------------------------------------
  printf("[TEST] Phase 5: Subsequent fault capture at 0x%08x...\n", TARGET_ADDR_PHASE5);
  volatile uint32_t *target_p5 = (volatile uint32_t *)TARGET_ADDR_PHASE5;
  const uint32_t p5_seed_data = 0xCAFEBABEu;
  *target_p5 = p5_seed_data;
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

  if ((r48 & 0x80000000u) == 0u) {
    printf("[FAIL] 0x48 valid bit not set after subsequent fault!\n");
    tohost = 1;
    return 5;
  }
  if ((r48 & r48_rsvd_mask) != 0u) {
    printf("[FAIL] 0x48 reserved bits [30:DCCM_BITS] non-zero: 0x%08x\n", r48);
    tohost = 1;
    return 5;
  }
  captured_addr = r48 & dccm_addr_mask;
  if (captured_addr != (TARGET_ADDR_PHASE5 & dccm_addr_mask)) {
    printf("[FAIL] 0x48 address mismatch: expected 0x%04x, got 0x%04x\n",
           (uint32_t)(TARGET_ADDR_PHASE5 & dccm_addr_mask), captured_addr);
    tohost = 1;
    return 5;
  }
#ifdef RV_DCCM_ADDR_XOR
  uint32_t p5_idx = (TARGET_ADDR_PHASE5 >> 2) & ((1u << (RV_DCCM_BITS - 2)) - 1u);
  uint32_t expected_p5_r49 = p5_seed_data ^ ((p5_idx << (RV_DCCM_BITS - 2)) | p5_idx);
#else
  uint32_t expected_p5_r49 = p5_seed_data;
#endif
  uint32_t expected_p5_r4a = compute_dccm_ecc32(p5_seed_data);
  if (r49 != expected_p5_r49) {
    printf("[FAIL] 0x49 data mismatch: expected 0x%08x, got 0x%08x\n", expected_p5_r49, r49);
    tohost = 1;
    return 5;
  }
  if ((r4a & r4a_rsvd_mask) != 0u || r4a != expected_p5_r4a) {
    printf("[FAIL] 0x4A ECC mismatch: expected 0x%08x, got 0x%08x\n", expected_p5_r4a, r4a);
    tohost = 1;
    return 5;
  }
  printf("[PASS] Phase 5 complete: Subsequent fault (addr, non-zero data & 7-bit ECC) captured after W1C clear.\n\n");

  // -------------------------------------------------------------
  // Phase 6: DCLS Delayed Comparator Equivalence & Directional Mismatch Verification
  // -------------------------------------------------------------
#ifdef RV_LOCKSTEP_ENABLE
  printf("[TEST] Phase 6A: Verifying DCLS symmetric/no-fault equivalence across Phases 1-5...\n");
  uint32_t sym_match_cnt = rdbk_counter_cmd(RDBK_CNT_DCLS_SYM_MATCH);
  uint32_t main_mism_cnt = rdbk_counter_cmd(RDBK_CNT_DCLS_MAIN_MISM);
  uint32_t shdw_mism_cnt = rdbk_counter_cmd(RDBK_CNT_DCLS_SHDW_MISM);
  uint32_t dmi_mism_cnt  = rdbk_counter_cmd(RDBK_CNT_DCLS_DMI_MISM);
  printf("[TEST] Phase 6A DCLS counters: sym_match=%d, main_mism=%d, shdw_mism=%d, dmi_mism=%d\n",
         sym_match_cnt, main_mism_cnt, shdw_mism_cnt, dmi_mism_cnt);
  if (sym_match_cnt != 3u || main_mism_cnt != 0u || shdw_mism_cnt != 0u || dmi_mism_cnt != 0u) {
    printf("[FAIL] Phase 6A: DCLS symmetric equivalence counters unexpected!\n");
    tohost = 1;
    return 6;
  }

  // Clear Phase 5 DMI status via W1C before directional DCLS fault injection
  dmi_write(DMI_REG_DCCM_STATUS);
  r48 = dmi_read(DMI_REG_DCCM_STATUS);
  if ((r48 & 0x80000000u) != 0u) {
    printf("[FAIL] Phase 6A: 0x48 valid bit not cleared before directional DCLS tests!\n");
    tohost = 1;
    return 6;
  }
  printf("[PASS] Phase 6A complete: Symmetric lockstep equivalence verified across Phases 1-5.\n\n");

  // Configure PIC IRQ #2 (`corruption_detected_o`) vectored external interrupt
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

  // Phase 6B: Main-Core Asymmetric Readback Mismatch (`delayed_main == 1` vs `shadow == 0`)
  printf("[TEST] Phase 6B: Testing DCLS main-core delayed readback mismatch (0x91 Case 206)...\n");
  g_expect_dcls_trap = true;
  g_dcls_clear_dmi_in_trap = false;
  __asm__ volatile(
      "fence rw, rw\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      ::: "memory");
  tohost = (DCLS_CASE_RDBK_DATA_FF << 8) | CMD_INJ_VEER;
  __asm__ volatile("fence rw, rw" ::: "memory");
  *target_p5 = 0x12345678u;
  __asm__ volatile("fence rw, rw" ::: "memory");

  for (int i = 0; i < 500 && g_dcls_trap_count < 1u; i++) {
    __asm__ volatile("nop");
  }
  main_mism_cnt = rdbk_counter_cmd(RDBK_CNT_DCLS_MAIN_MISM);
  shdw_mism_cnt = rdbk_counter_cmd(RDBK_CNT_DCLS_SHDW_MISM);
  if (g_dcls_trap_count != 1u || main_mism_cnt == 0u || shdw_mism_cnt != 0u) {
    printf("[FAIL] Phase 6B: Main-core DCLS mismatch failed (traps=%d, main_mism=%d, shdw_mism=%d)!\n",
           g_dcls_trap_count, main_mism_cnt, shdw_mism_cnt);
    tohost = 1;
    return 6;
  }
  printf("[PASS] Phase 6B complete: Main-core delayed readback mismatch caught (traps=%d, main_mism=%d).\n\n",
         g_dcls_trap_count, main_mism_cnt);

  // Phase 6C: DMI Diagnostic Register (`0x48`) Delayed Main-vs-Shadow Comparison (`dmi_reg_rdata`)
  // Because Phase 6B faulted only the main core, main core `0x48[31] == 1` while shadow core `0x48[31] == 0`.
  // Mask MIE briefly while `dmi_read(0x48)` completes its mailbox handshake, then unmask MIE to take the
  // resulting `dmi_reg_rdata` DCLS comparator interrupt and clear `0x48` via W1C inside `trap_handler`.
  printf("[TEST] Phase 6C: Testing DCLS delayed DMI 0x48 register comparison...\n");
  __asm__ volatile("csrci mstatus, 8");
  r48 = dmi_read(DMI_REG_DCCM_STATUS);
  if (r48 != (0x80000000u | (TARGET_ADDR_PHASE5 & dccm_addr_mask))) {
    printf("[FAIL] Phase 6C: Main core 0x48 did not latch Phase 6B fault: 0x%08x\n", r48);
    tohost = 1;
    return 6;
  }
  g_expect_dcls_trap = true;
  g_dcls_clear_dmi_in_trap = true;
  __asm__ volatile("csrsi mstatus, 8");

  for (int i = 0; i < 500 && g_dcls_trap_count < 2u; i++) {
    __asm__ volatile("nop");
  }
  dmi_mism_cnt = rdbk_counter_cmd(RDBK_CNT_DCLS_DMI_MISM);
  if (g_dcls_trap_count != 2u || dmi_mism_cnt == 0u) {
    printf("[FAIL] Phase 6C: DCLS DMI 0x48 mismatch failed (traps=%d, dmi_mism=%d)!\n",
           g_dcls_trap_count, dmi_mism_cnt);
    tohost = 1;
    return 6;
  }
  printf("[PASS] Phase 6C complete: Delayed DMI 0x48 comparison mismatch caught & cleared (traps=%d, dmi_mism=%d).\n\n",
         g_dcls_trap_count, dmi_mism_cnt);

  // Phase 6D: Shadow-Core Asymmetric Readback Mismatch (`delayed_main == 0` vs `shadow == 1`)
  printf("[TEST] Phase 6D: Testing DCLS shadow-core readback mismatch (0x92 Case 206)...\n");
  uint32_t main_mism_before_6d = rdbk_counter_cmd(RDBK_CNT_DCLS_MAIN_MISM);
  g_expect_dcls_trap = true;
  g_dcls_clear_dmi_in_trap = false;
  __asm__ volatile(
      "fence rw, rw\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      "nop\n\t"
      ::: "memory");
  tohost = (DCLS_CASE_RDBK_DATA_FF << 8) | CMD_INJ_LOCKSTEP;
  __asm__ volatile("fence rw, rw" ::: "memory");
  *target_p5 = 0x87654321u;
  __asm__ volatile("fence rw, rw" ::: "memory");

  for (int i = 0; i < 500 && g_dcls_trap_count < 3u; i++) {
    __asm__ volatile("nop");
  }
  main_mism_cnt = rdbk_counter_cmd(RDBK_CNT_DCLS_MAIN_MISM);
  shdw_mism_cnt = rdbk_counter_cmd(RDBK_CNT_DCLS_SHDW_MISM);
  if (g_dcls_trap_count != 3u || shdw_mism_cnt == 0u || main_mism_cnt != main_mism_before_6d) {
    printf("[FAIL] Phase 6D: Shadow-core DCLS mismatch failed (traps=%d, shdw_mism=%d, main_mism=%d)!\n",
           g_dcls_trap_count, shdw_mism_cnt, main_mism_cnt);
    tohost = 1;
    return 6;
  }
  printf("[PASS] Phase 6D complete: Shadow-core readback mismatch caught (traps=%d, shdw_mism=%d).\n\n",
         g_dcls_trap_count, shdw_mism_cnt);

  // Phase 6E: Post-Recovery Clean Equivalence Check
  printf("[TEST] Phase 6E: Verifying post-recovery lockstep equivalence...\n");
  __asm__ volatile("csrci mstatus, 8");
  dmi_write(DMI_REG_DCCM_STATUS);
  (void)dmi_read(DMI_REG_DCCM_STATUS);
  for (volatile int i = 0; i < 20; i++) {
    __asm__ volatile("nop");
  }
  kPicClrGateway[2] = 0;
  (void)rdbk_counter_cmd(RDBK_CNT_RESET);
  __asm__ volatile("csrsi mstatus, 8");

  *target_p5 = 0xA5A55A5Au;
  __asm__ volatile("fence rw, rw" ::: "memory");
  r48 = dmi_read(DMI_REG_DCCM_STATUS);
  if (*target_p5 != 0xA5A55A5Au || (r48 & 0x80000000u) != 0u || g_dcls_trap_count != 3u) {
    printf("[FAIL] Phase 6E: Post-recovery equivalence check failed (r48=0x%08x, traps=%d)!\n",
           r48, g_dcls_trap_count);
    tohost = 1;
    return 6;
  }
  printf("[PASS] Phase 6E complete: Post-recovery no-fault lockstep equivalence verified.\n\n");
  printf("================================================================\n");
  printf("=== ALL 6 PHASES PASSED: DCCM Write Readback & DMI Verified ====\n");
  printf("================================================================\n");
  return 0;
#else
  printf("[TEST] Phase 6: DCLS lockstep disabled in build; skipping asymmetric trap check.\n");
  printf("================================================================\n");
  printf("=== ALL PHASES PASSED: DCCM Write Readback & DMI Verified ======\n");
  printf("================================================================\n");
  return 0;
#endif
}
