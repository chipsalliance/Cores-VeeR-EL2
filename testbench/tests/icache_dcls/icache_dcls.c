/* SPDX-License-Identifier: Apache-2.0
 * Copyright 2024 Google LLC
 *
 * ICache Dual Core Lockstep (DCLS) Mismatch Test
 *
 * Architecture & Test Intent:
 * When Dual Core Lockstep is enabled (`lockstep_enable=1`), the active core (VEER)
 * and shadow core (LOCKSTEP) run identical instruction streams in parallel.
 *
 * This test verifies:
 * 1. Divergent fault injection asserting `lockstep_err_injection_en_i` (mailbox 0x0293)
 *    causes the DCLS hardware comparator (el2_veer_lockstep.sv) to detect output trace
 *    divergence between the active and shadow cores.
 * 2. The DCLS comparator asserts `corruption_detected_o == El2MuBiTrue` (0x02).
 * 3. The testbench 0xFE monitor evaluates `corruption_detected_o` and outputs TEST_PASSED.
 */

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

#define STDOUT_ADDR 0xD0580000
volatile uint32_t *mailbox = (uint32_t *)STDOUT_ADDR;

// Mailbox Command Protocols
#define CMD_ENABLE_LOCKSTEP_ERR_INJ 0x0293  // Set lockstep_err_injection_en_i = 0x02 (El2MuBiTrue)
#define CMD_CHECK_CORRUPTION_STATUS 0xFE    // Verify corruption_detected_o == El2MuBiTrue and exit

static volatile uint32_t counter = 0;

void trap_handler(void) {
    // Default trap handler stub
}

static inline void delay_nops(uint32_t count) {
    for (uint32_t i = 0; i < count; i++) {
        __asm__ volatile ("nop");
    }
}

// Function aligned to 16-byte boundary to isolate instruction cache line fetch
__attribute__((noinline, aligned(16)))
void target_inst(void) {
    counter++;
}

int main(void) {
    printf("=====================================================\n");
    printf(" Starting ICache Dual Core Lockstep (DCLS) C Test   \n");
    printf("=====================================================\n");

    // Phase 1: Warm up target instruction in ICache (populates cache line)
    target_inst();
    printf("[Phase 1] Cache line warmup complete. Counter = %u\n", counter);

    // Phase 2: Enable lockstep hardware error injection (0x0293)
    printf("[Phase 2] Enabling DCLS hardware error injection (0x0293)...\n");
    *mailbox = CMD_ENABLE_LOCKSTEP_ERR_INJ;
    target_inst();

    // Delay loop for DCLS hardware comparator pipeline propagation (RV_LOCKSTEP_DELAY)
    delay_nops(20);

    // Phase 3: Verify corruption detection via testbench 0xFE monitor
    printf("[Phase 3] Sending 0xFE to monitor corruption_detected_o status...\n");
    *mailbox = CMD_CHECK_CORRUPTION_STATUS;

    // The testbench terminates the simulation at 0xFE; fallback failure if not reached
    return 0;
}
