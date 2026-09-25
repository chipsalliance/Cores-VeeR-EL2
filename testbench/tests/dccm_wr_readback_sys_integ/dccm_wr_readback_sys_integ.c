/* SPDX-License-Identifier: Apache-2.0
 * Copyright 2026 Google LLC
 *
 * DCCM Write Readback System Integration (DMA & ECC) Verification (#512)
 * Author: Samip Modi (samipmodi@google.com)
 *
 * Description:
 * Comprehensive bare-metal verification of the VeeR EL2 DCCM write-readback
 * hardware countermeasure interacting with external DMA traffic and single-bit
 * ECC error corrections, verifying Issue #512 system interaction requirements.
 *
 * Test Phases:
 * 1. Phase 1: DMA Write Collision (WR_SYS_001 #512) - verify dccm_ready holds off
 *    DMA write while write-readback check is pending, and completes once check resolves.
 * 2. Phase 2: DMA Read Collision Snoop Path (WR_SYS_002A #512) - verify DMA read to
 *    matching store address resolves check via snoop without port steal.
 * 3. Phase 3: DMA Read Collision Steal Deferral (WR_SYS_002B #512) - verify DMA read to
 *    different address has priority and defers core readback steal to next idle cycle.
 * 4. Phase 4: ECC 1-Bit Correction Snoop Path (WR_SYS_003A #512) - verify readback check
 *    snoops load data when load hits single-bit ECC error.
 * 5. Phase 5: ECC 1-Bit Correction Steal Deferral (WR_SYS_003B #512) - verify single-bit
 *    correction write-back (ld_single_ecc_error_r_ff) defers core readback steal.
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

extern volatile uint32_t tohost;

// Dedicated non-colliding mailbox opcodes (0xB5-0xBA)
#define MAILBOX_CMD_ARM_DMA_WR_COLL    0xB5
#define MAILBOX_CMD_ARM_DMA_RD_SNOOP   0xB6
#define MAILBOX_CMD_ARM_DMA_RD_STEAL   0xB7
#define MAILBOX_CMD_ARM_ECC_SNOOP      0xB8
#define MAILBOX_CMD_ARM_ECC_STEAL      0xB9
#define MAILBOX_CMD_GET_STATUS         0xBA

#define COMM_SCRATCHPAD_ADDR       0xF0047000
#define COMM_HANDSHAKE_ADDR        0xF0047004

#define TARGET_ADDR_PHASE1         0xF0047400
#define TARGET_ADDR_PHASE2         0xF0047410
#define TARGET_ADDR_PHASE3         0xF0047420
#define TARGET_ADDR_PHASE4         0xF0047430
#define TARGET_ADDR_PHASE5         0xF0047440

static volatile uint32_t *comm_result    = (volatile uint32_t *)COMM_SCRATCHPAD_ADDR;
static volatile uint32_t *comm_handshake = (volatile uint32_t *)COMM_HANDSHAKE_ADDR;
static uint16_t current_seq_id = 0;

/**
 * Sends a command to the testbench via tohost mailbox and waits for handshake.
 *
 * @param cmd Opcode (bits 7:0)
 * @param payload Additional payload (bits 15:8)
 * @return Value returned by testbench in scratchpad (0xF0047000)
 */
static uint32_t send_tb_command(uint8_t cmd, uint8_t payload) {
    uint16_t seq = ++current_seq_id;
    uint32_t msg = ((uint32_t)seq << 16) | ((uint32_t)payload << 8) | cmd;

    *comm_handshake = 0xDEADBEEF;
    __asm__ volatile ("fence rw, rw" ::: "memory");

    tohost = msg;
    __asm__ volatile ("fence rw, rw" ::: "memory");

    while (*comm_handshake != (uint32_t)seq) {
        __asm__ volatile ("nop");
    }

    uint32_t res = *comm_result;
    __asm__ volatile ("fence rw, rw" ::: "memory");
    return res;
}

/**
 * Arms a verification phase in the testbench.
 *
 * @param cmd Arm mailbox opcode (0xB5 - 0xB9)
 */
static inline void arm_phase(uint8_t cmd) {
    (void)send_tb_command(cmd, 0);
}

/**
 * Queries the verification status of a phase from the testbench.
 *
 * @param phase Phase ID (1 - 5)
 * @return 1 on pass, 0 on fail
 */
static inline uint32_t get_phase_status(uint8_t phase) {
    return send_tb_command(MAILBOX_CMD_GET_STATUS, phase);
}

/**
 * Default trap handler.
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
    printf("=== Starting DCCM Write Readback System Integration Tests (#512) ===\n");
    printf("================================================================\n\n");

    // -------------------------------------------------------------
    // Phase 1: DMA Write Collision (WR_SYS_001 #512)
    // -------------------------------------------------------------
    printf("[TEST] Phase 1: DMA Write Collision while check pending (WR_SYS_001)...\n");
    volatile uint32_t *target_p1 = (volatile uint32_t *)TARGET_ADDR_PHASE1;
    *target_p1 = 0x11112222;
    __asm__ volatile ("fence rw, rw" ::: "memory");

    arm_phase(MAILBOX_CMD_ARM_DMA_WR_COLL);
    // Perform store to open pending window
    *target_p1 = 0x33334444;
    __asm__ volatile ("fence rw, rw" ::: "memory");

    uint32_t p1_res = get_phase_status(1);
    if (p1_res != 1) {
        printf("[FAIL] Phase 1: DMA write collision verification failed (res=%d)!\n", p1_res);
        tohost = 1;
        return 1;
    }
    printf("[PASS] Phase 1 complete: DMA write stall & clean resolution verified.\n\n");

    // -------------------------------------------------------------
    // Phase 2: DMA Read Collision - Snoop Path (WR_SYS_002A #512)
    // -------------------------------------------------------------
    printf("[TEST] Phase 2: DMA Read Collision Snoop Path (WR_SYS_002A)...\n");
    volatile uint32_t *target_p2 = (volatile uint32_t *)TARGET_ADDR_PHASE2;
    *target_p2 = 0x55556666;
    __asm__ volatile ("fence rw, rw" ::: "memory");

    arm_phase(MAILBOX_CMD_ARM_DMA_RD_SNOOP);
    *target_p2 = 0x77778888;
    __asm__ volatile ("fence rw, rw" ::: "memory");

    uint32_t p2_res = get_phase_status(2);
    if (p2_res != 1) {
        printf("[FAIL] Phase 2: DMA read snoop path verification failed (res=%d)!\n", p2_res);
        tohost = 1;
        return 2;
    }
    printf("[PASS] Phase 2 complete: DMA read snoop path verified.\n\n");

    // -------------------------------------------------------------
    // Phase 3: DMA Read Collision - Steal Deferral (WR_SYS_002B #512)
    // -------------------------------------------------------------
    printf("[TEST] Phase 3: DMA Read Collision Steal Deferral (WR_SYS_002B)...\n");
    volatile uint32_t *target_p3 = (volatile uint32_t *)TARGET_ADDR_PHASE3;
    *target_p3 = 0x9999AAAA;
    __asm__ volatile ("fence rw, rw" ::: "memory");

    arm_phase(MAILBOX_CMD_ARM_DMA_RD_STEAL);
    *target_p3 = 0xBBBBCCCC;
    __asm__ volatile ("fence rw, rw" ::: "memory");

    uint32_t p3_res = get_phase_status(3);
    if (p3_res != 1) {
        printf("[FAIL] Phase 3: DMA read steal priority deferral failed (res=%d)!\n", p3_res);
        tohost = 1;
        return 3;
    }
    printf("[PASS] Phase 3 complete: DMA read priority over steal verified.\n\n");

    // -------------------------------------------------------------
    // Phase 4: ECC 1-Bit Correction - Snoop Path (WR_SYS_003A #512)
    // -------------------------------------------------------------
    printf("[TEST] Phase 4: ECC 1-Bit Correction Snoop Path (WR_SYS_003A)...\n");
    volatile uint32_t *target_p4 = (volatile uint32_t *)TARGET_ADDR_PHASE4;
    *target_p4 = 0xCAFE0001;
    __asm__ volatile ("fence rw, rw" ::: "memory");

    arm_phase(MAILBOX_CMD_ARM_ECC_SNOOP);
    *target_p4 = 0xCAFE0002;
    __asm__ volatile ("fence rw, rw" ::: "memory");

    uint32_t p4_res = get_phase_status(4);
    if (p4_res != 1) {
        printf("[FAIL] Phase 4: ECC 1-bit snoop path verification failed (res=%d)!\n", p4_res);
        tohost = 1;
        return 4;
    }
    printf("[PASS] Phase 4 complete: ECC 1-bit snoop path verified.\n\n");

    // -------------------------------------------------------------
    // Phase 5: ECC 1-Bit Correction - Steal Deferral (WR_SYS_003B #512)
    // -------------------------------------------------------------
    printf("[TEST] Phase 5: ECC 1-Bit Correction Steal Deferral (WR_SYS_003B)...\n");
    volatile uint32_t *target_p5 = (volatile uint32_t *)TARGET_ADDR_PHASE5;
    *target_p5 = 0xBEEF0001;
    __asm__ volatile ("fence rw, rw" ::: "memory");

    arm_phase(MAILBOX_CMD_ARM_ECC_STEAL);
    *target_p5 = 0xBEEF0002;
    __asm__ volatile ("fence rw, rw" ::: "memory");

    uint32_t p5_res = get_phase_status(5);
    if (p5_res != 1) {
        printf("[FAIL] Phase 5: ECC 1-bit correction steal deferral failed (res=%d)!\n", p5_res);
        tohost = 1;
        return 5;
    }
    printf("[PASS] Phase 5 complete: ECC 1-bit correction steal deferral verified.\n\n");

    printf("================================================================\n");
    printf("=== ALL 5 PHASES PASSED: System Integration (DMA & ECC) Verified ===\n");
    printf("================================================================\n");
    printf("TEST_PASSED\n");

    tohost = 0xFF; // Signal completion
    return 0;
}
