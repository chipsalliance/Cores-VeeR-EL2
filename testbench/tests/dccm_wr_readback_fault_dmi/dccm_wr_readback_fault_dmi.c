/* SPDX-License-Identifier: Apache-2.0
 * Copyright 2026 Google LLC
 *
 * DCCM Write Readback Fault Injection & DMI Diagnostic Verification (#512)
 * Author: Samip Modi (samipmodi@google.com)
 *
 * Description:
 * Comprehensive bare-metal verification of the VeeR EL2 DCCM write-readback
 * fault injection and DMI diagnostic registers (0x70-0x72).
 *
 * Test Phases:
 * 1. Phase 1: Verify pristine reset state of DMI registers 0x70, 0x71, 0x72 (all zero).
 * 2. Phase 2: Inject write-skip fault, verify dccm_write_readback_error pulse and fault capture in 0x70-0x72.
 * 3. Phase 3: First-fault-wins retention: inject second fault, verify 0x70-0x72 retain original fault.
 * 4. Phase 4: W1C clear on 0x70[31], verify valid bit returns to 0.
 * 5. Phase 5: Subsequent fault capture: inject fault after clear, verify new fault captured in 0x70-0x72.
 * 6. Phase 6: DCLS lockstep comparator verification: verify asymmetric write-readback divergence triggers corruption detection.
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

extern volatile uint32_t tohost;

#define MAILBOX_CMD_ARM_WR_SKIP   0xB0
#define MAILBOX_CMD_DMI_READ      0xB1
#define MAILBOX_CMD_DMI_WRITE     0xB2
#define MAILBOX_CMD_DCLS_ASYMM    0xB3
#define MAILBOX_CMD_GET_PULSES    0xB4

#define DMI_REG_DCCM_STATUS       0x70
#define DMI_REG_DCCM_DATA         0x71
#define DMI_REG_DCCM_ECC          0x72

#define COMM_SCRATCHPAD_ADDR      0xF0047000
#define COMM_HANDSHAKE_ADDR       0xF0047004

#define TARGET_ADDR_PHASE2        0xF0047400
#define TARGET_ADDR_PHASE3        0xF0047500
#define TARGET_ADDR_PHASE5        0xF0047600

static volatile uint32_t * const kScratchpad = (volatile uint32_t *)COMM_SCRATCHPAD_ADDR;
static volatile uint32_t * const kHandshake  = (volatile uint32_t *)COMM_HANDSHAKE_ADDR;

static uint32_t g_seq_id = 0;

/**
 * Sends a command to the testbench via tohost and waits for completion.
 *
 * @param cmd Opcode (0xB0 - 0xB4)
 * @param dmi_addr 7-bit DMI address (for B1/B2)
 * @return Value written to scratchpad by testbench
 */
static uint32_t send_tb_command(uint8_t cmd, uint8_t dmi_addr) {
    g_seq_id++;
    uint32_t payload = ((uint32_t)g_seq_id << 16) |
                       ((uint32_t)(dmi_addr & 0x7F) << 8) |
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
 * Performs a DMI write with bit 31 set (W1C clear) to specified register.
 *
 * @param addr 7-bit DMI register address
 */
static inline void dmi_write_w1c(uint8_t addr) {
    (void)send_tb_command(MAILBOX_CMD_DMI_WRITE, addr);
}

/**
 * Arms DCCM write-skip for the next DCCM store.
 */
static inline void arm_write_skip(void) {
    (void)send_tb_command(MAILBOX_CMD_ARM_WR_SKIP, 0);
}

/**
 * Queries cumulative dccm_write_readback_error pulse count from testbench.
 *
 * @return Cumulative pulse count
 */
static inline uint32_t get_error_pulse_count(void) {
    return send_tb_command(MAILBOX_CMD_GET_PULSES, 0);
}

/**
 * Tests asymmetric DCLS comparator response to single-core write-readback divergence.
 *
 * @return 1 if corruption detected by lockstep comparator, 0 otherwise
 */
static inline uint32_t test_dcls_asymmetric(void) {
    return send_tb_command(MAILBOX_CMD_DCLS_ASYMM, 0);
}

/**
 * Default trap handler for unexpected exceptions/interrupts.
 */
void trap_handler(void) {
    uint32_t mcause;
    __asm__ volatile ("csrr %0, mcause" : "=r" (mcause));
    printf("[TRAP] Unexpected trap encountered! mcause=0x%08x\n", mcause);
    tohost = 1;
    while (true) {}
}

int main(void) {
    printf("\n================================================================\n");
    printf("=== Starting DCCM Write Readback Fault & DMI Tests (#512) ===\n");
    printf("================================================================\n\n");

    // -------------------------------------------------------------
    // Phase 1: Pristine Reset State Verification
    // -------------------------------------------------------------
    printf("[TEST] Phase 1: Checking pristine reset state of DMI 0x70-0x72...\n");
    uint32_t pulses = get_error_pulse_count();
    if (pulses != 0) {
        printf("[FAIL] Initial error pulse count non-zero: %d\n", pulses);
        tohost = 1;
        return 1;
    }

    uint32_t r70 = dmi_read(DMI_REG_DCCM_STATUS);
    uint32_t r71 = dmi_read(DMI_REG_DCCM_DATA);
    uint32_t r72 = dmi_read(DMI_REG_DCCM_ECC);
    printf("[TEST] Pristine DMI: 0x70=0x%08x, 0x71=0x%08x, 0x72=0x%08x\n", r70, r71, r72);

    if (r70 != 0 || r71 != 0 || r72 != 0) {
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
    *target_p2 = 0x00000000;
    __asm__ volatile ("fence rw, rw" ::: "memory");

    // Arm write-skip and perform store
    arm_write_skip();
    *target_p2 = 0xAABBCCDD;
    __asm__ volatile ("fence rw, rw" ::: "memory");

    // Verify error pulse
    pulses = get_error_pulse_count();
    if (pulses != 1) {
        printf("[FAIL] Expected 1 error pulse, got %d\n", pulses);
        tohost = 1;
        return 2;
    }

    // Verify DMI registers
    r70 = dmi_read(DMI_REG_DCCM_STATUS);
    r71 = dmi_read(DMI_REG_DCCM_DATA);
    r72 = dmi_read(DMI_REG_DCCM_ECC);
    printf("[TEST] Captured DMI: 0x70=0x%08x, 0x71=0x%08x, 0x72=0x%08x\n", r70, r71, r72);

    if ((r70 & 0x80000000) == 0) {
        printf("[FAIL] 0x70 bit 31 (valid) not set!\n");
        tohost = 1;
        return 2;
    }
    uint16_t captured_addr = (uint16_t)(r70 & 0xFFFF);
    if (captured_addr != (TARGET_ADDR_PHASE2 & 0xFFFF)) {
        printf("[FAIL] 0x70 address mismatch: expected 0x%04x, got 0x%04x\n",
               (uint32_t)(TARGET_ADDR_PHASE2 & 0xFFFF), captured_addr);
        tohost = 1;
        return 2;
    }
    if (r71 != 0) {
        printf("[FAIL] 0x71 data mismatch: expected 0x0, got 0x%08x\n", r71);
        tohost = 1;
        return 2;
    }
    printf("[PASS] Phase 2 complete: Write-skip fault captured in 0x70-0x72.\n\n");

    // -------------------------------------------------------------
    // Phase 3: First-Fault-Wins Retention
    // -------------------------------------------------------------
    printf("[TEST] Phase 3: First-fault-wins retention with second fault...\n");
    volatile uint32_t *target_p3 = (volatile uint32_t *)TARGET_ADDR_PHASE3;
    *target_p3 = 0x00000000;
    __asm__ volatile ("fence rw, rw" ::: "memory");

    arm_write_skip();
    *target_p3 = 0x11223344;
    __asm__ volatile ("fence rw, rw" ::: "memory");

    pulses = get_error_pulse_count();
    if (pulses != 2) {
        printf("[FAIL] Expected 2 error pulses, got %d\n", pulses);
        tohost = 1;
        return 3;
    }

    // 0x70-0x72 must still retain Phase 2 fault
    r70 = dmi_read(DMI_REG_DCCM_STATUS);
    r71 = dmi_read(DMI_REG_DCCM_DATA);
    r72 = dmi_read(DMI_REG_DCCM_ECC);
    printf("[TEST] Retained DMI: 0x70=0x%08x, 0x71=0x%08x, 0x72=0x%08x\n", r70, r71, r72);

    captured_addr = (uint16_t)(r70 & 0xFFFF);
    if (captured_addr != (TARGET_ADDR_PHASE2 & 0xFFFF)) {
        printf("[FAIL] First fault not retained! Addr changed to 0x%04x\n", captured_addr);
        tohost = 1;
        return 3;
    }
    if (r71 != 0) {
        printf("[FAIL] First fault data not retained! Data changed to 0x%08x\n", r71);
        tohost = 1;
        return 3;
    }
    printf("[PASS] Phase 3 complete: First fault successfully retained across second fault.\n\n");

    // -------------------------------------------------------------
    // Phase 4: W1C Clear on 0x70[31]
    // -------------------------------------------------------------
    printf("[TEST] Phase 4: Clearing fault register via DMI W1C on 0x70...\n");
    dmi_write_w1c(DMI_REG_DCCM_STATUS);

    r70 = dmi_read(DMI_REG_DCCM_STATUS);
    printf("[TEST] After clear DMI: 0x70=0x%08x\n", r70);
    if ((r70 & 0x80000000) != 0) {
        printf("[FAIL] 0x70 bit 31 still set after W1C clear!\n");
        tohost = 1;
        return 4;
    }
    printf("[PASS] Phase 4 complete: W1C clear successfully cleared valid bit.\n\n");

    // -------------------------------------------------------------
    // Phase 5: Subsequent Fault Capture
    // -------------------------------------------------------------
    printf("[TEST] Phase 5: Subsequent fault capture at 0x%08x...\n", TARGET_ADDR_PHASE5);
    volatile uint32_t *target_p5 = (volatile uint32_t *)TARGET_ADDR_PHASE5;
    *target_p5 = 0x00000000;
    __asm__ volatile ("fence rw, rw" ::: "memory");

    arm_write_skip();
    *target_p5 = 0x55667788;
    __asm__ volatile ("fence rw, rw" ::: "memory");

    pulses = get_error_pulse_count();
    if (pulses != 3) {
        printf("[FAIL] Expected 3 error pulses, got %d\n", pulses);
        tohost = 1;
        return 5;
    }

    r70 = dmi_read(DMI_REG_DCCM_STATUS);
    r71 = dmi_read(DMI_REG_DCCM_DATA);
    r72 = dmi_read(DMI_REG_DCCM_ECC);
    printf("[TEST] Subsequent DMI: 0x70=0x%08x, 0x71=0x%08x, 0x72=0x%08x\n", r70, r71, r72);

    if ((r70 & 0x80000000) == 0) {
        printf("[FAIL] 0x70 valid bit not set after subsequent fault!\n");
        tohost = 1;
        return 5;
    }
    captured_addr = (uint16_t)(r70 & 0xFFFF);
    if (captured_addr != (TARGET_ADDR_PHASE5 & 0xFFFF)) {
        printf("[FAIL] 0x70 address mismatch: expected 0x%04x, got 0x%04x\n",
               (uint32_t)(TARGET_ADDR_PHASE5 & 0xFFFF), captured_addr);
        tohost = 1;
        return 5;
    }
    printf("[PASS] Phase 5 complete: Subsequent fault captured after W1C clear.\n\n");

    // -------------------------------------------------------------
    // Phase 6: DCLS Asymmetric Lockstep Comparison
    // -------------------------------------------------------------
    printf("[TEST] Phase 6: Testing DCLS asymmetric lockstep error detection...\n");
    uint32_t dcls_detected = test_dcls_asymmetric();
    printf("[TEST] DCLS asymmetric detection result: %d\n", dcls_detected);
    if (dcls_detected != 1) {
        printf("[FAIL] DCLS comparator failed to detect asymmetric fault divergence!\n");
        tohost = 1;
        return 6;
    }
    printf("[PASS] Phase 6 complete: DCLS comparator verified.\n\n");

    printf("================================================================\n");
    printf("=== ALL 6 PHASES PASSED: DCCM Write Readback & DMI Verified ====\n");
    printf("================================================================\n");
    return 0;
}
