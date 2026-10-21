/* SPDX-License-Identifier: Apache-2.0
 * Copyright 2026 Google LLC
 *
 * EL2_IC_DATA Outside-DCLS Boundary Control, Rotator & Bank-Select Fault Test
 * Author: Samip Modi (samipmodi@google.com)
 *
 * Description:
 * Verifies that single-point control, byte-rotator, and physical bank-select
 * faults inside `EL2_IC_DATA` (`design/ifu/el2_ifu_ic_mem.sv`, outside the DCLS
 * lockstep boundary) are blocked at the DCLS boundary by core-side ECC, Parity,
 * Address-XOR (`RV_ICACHE_ADDR_XOR`), and DCLS-protected control signals inside
 * `el2_ifu_mem_ctl.sv`.
 *
 * Background (Bug #569 / PR #571):
 * Commit 7dd5354d ("Move iCache ECC and parity check into DCLS") moved
 * `rvecc_decode_64`, `rveven_paritycheck`, and the 64-bit byte rotator into
 * `el2_ifu_mem_ctl.sv` (inside DCLS), but initially left three sets of steering
 * and check-enable signals driven from `EL2_IC_DATA` (`el2_ifu_ic_mem.sv`,
 * outside DCLS):
 *   1. `ic_b_rden_ff` -> `bank_check_en` (`ic_rd_bank_check_en[1:0]`),
 *   2. `ic_rw_addr_ff[2:1]` (`ic_rd_addr_lo[1:0]` byte-rotator offset), and
 *   3. `ic_rw_addr_ff[3]` (physical Bank 0 / Bank 1 read order on `ic_rd_data`).
 * PR #571 registers `{ic_rd_bank_sel, ic_rd_rot_sel[1:0]}` and computes
 * `ic_bank_check_en[1:0]` inside the DCLS-protected `el2_ifu_mem_ctl.sv`.
 *
 * Test Phases:
 * 1. Sub-test 1 (Mailbox 0x8F, Mode 1): False `ic_cacheline_wrap_ff` / check-enable
 *    suppression (`ic_b_rden_ff = 2'b00`, `ic_rw_addr_ff[5:3] = 3'b111`) in
 *    `EL2_IC_DATA` (outside DCLS) during a 1-bit upper-bank data flip (`ic_rd_data`
 *    bit 75 flipped, turning `addi a0, a0, 1` into `addi a0, a0, 0` at `0x8000b006`).
 *    - Expected: Core-side `ic_bank_check_en[1]` inside DCLS remains enabled,
 *      catches the 1-bit corruption (`micect` +1), refetches, and returns `1`.
 * 2. Sub-test 2 (Mailbox 0x8F, Mode 2): Single-bit fault `ic_b_rden[1] = 1'b0`
 *    in `EL2_IC_DATA` (outside DCLS) during a cross-bank straddling fetch at
 *    `0x8000b406` (`addr[2:1] == 2'b11`).
 *    - Expected: Stale Bank-1 SRAM output (`0x8000bc28`) has an Address-XOR /
 *      ECC / Parity mismatch against `0x8000b400`, which is caught by core-side
 *      `ic_bank_check_en[1]` (`micect` +1), refetched, and returns `1`.
 * 3. Sub-test 3 (Mailbox 0x8F, Mode 3): Single-bit fault on `ic_rw_addr_ff[2:1]`
 *    (`2'b10` instead of `2'b00`) in `EL2_IC_DATA` (outside DCLS) during an
 *    aligned cache hit at `0x8000d000`.
 *    - Expected: Core-side byte rotator uses DCLS-protected `ic_rd_rot_sel`
 *      (`2'b00`), executing `addi a0, a0, 1` and returning `1`.
 * 4. Sub-test 4 (Mailbox 0x8F, Mode 4): Single-bit fault on `ic_rw_addr_ff[3]`
 *    (`1'b1` instead of `1'b0`) in `EL2_IC_DATA` (outside DCLS) during an
 *    aligned cache hit at `0x8000d000` after priming Bank-1 SRAM with a valid
 *    same-line `ret` instruction (`0x8000d018..0x8000d038`).
 *    - Expected: `ic_rd_data` keeps physical bank order `{bank1, bank0}` and
 *      core-side DCLS `ic_rd_bank_sel` (`1'b0`) selects Bank 0, executing
 *      `addi a0, a0, 1` and returning `1`.
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include "defines.h"  // Generated.

#define STDOUT_ADDR 0xD0580000
volatile uint32_t *mailbox = (uint32_t *)STDOUT_ADDR;

// Mailbox Command Protocols
#define CMD_INJECT_IC_DCLS_BOUNDARY 0x8FU
#define CMD_TEST_PASSED             0xFFU
#define CMD_TEST_FAILED             0x01U

// Sub-modes for `CMD_INJECT_IC_DCLS_BOUNDARY` (0x8F) in bits [10:8]
#define MODE_BANK_CHECK_EN_FAULT 1U
#define MODE_BANK1_RDEN_FAULT    2U
#define MODE_ADDR_LO_ROT_FAULT   3U
#define MODE_BANK_SEL_SWAP_FAULT 4U

// CSR Definitions
#define MICECT_CSR_ADDR 0x7F0  // ICache Error Counter CSR (`micect`)

#define STR(x)  #x
#define XSTR(x) STR(x)

#define read_csr(csr) ({ \
    unsigned long res_; \
    __asm__ volatile ("csrr %0, " XSTR(csr) : "=r"(res_)); \
    res_; \
})

#define write_csr(csr, val) do { \
    __asm__ volatile ("csrw " XSTR(csr) ", %0" : : "r"(val)); \
} while (false)

/**
 * Default trap handler stub.
 */
void trap_handler(void) {
}

/**
 * Sub-test 1 target function placed at `0x8000b000` (`.subtest1_text`):
 * - Offset 0x00..0x02: `c.nop` (`0x0001`)
 * - Offset 0x04: `c.j +2` (`0xa009`) -> redirects fetch PC to Offset 0x06 (`addr[2:1] == 2'b11`)
 * - Offset 0x06: `addi a0, a0, 1` (`0x00150513`), straddling Bank 0 (`0x0513`) & Bank 1 (`0x0015`)
 * - Offset 0x0a: `ret` (`0x00008067`)
 */
extern uint32_t target_bank_check_en_fault(uint32_t val);
__asm__(
    ".section .subtest1_text, \"ax\", @progbits\n"
    ".balign 64\n"
    ".global target_bank_check_en_fault\n"
    ".type target_bank_check_en_fault, @function\n"
    "target_bank_check_en_fault:\n"
    ".half 0x0001\n"      // Offset 0x00: c.nop
    ".half 0x0001\n"      // Offset 0x02: c.nop
    ".half 0xa009\n"      // Offset 0x04: c.j +2 -> jumps to Offset 0x06 (addr[2:1] == 2'b11)
    ".word 0x00150513\n"  // Offset 0x06: addi a0, a0, 1 (upper half 0x0015 in Bank 1)
    ".word 0x00008067\n"  // Offset 0x0a: ret
    ".rept 13\n"
    ".word 0x00000013\n"
    ".endr\n"
    ".size target_bank_check_en_fault, .-target_bank_check_en_fault\n"
    ".previous\n"
);

/**
 * Sub-test 2 cross-bank target function placed at `0x8000b400` (`.subtest2_text`):
 * - Offset 0x00..0x02: `c.nop` (`0x0001`)
 * - Offset 0x04: `c.j +2` (`0xa009`) -> redirects fetch PC to Offset 0x06 (`addr[2:1] == 2'b11`)
 * - Offset 0x06: `addi a0, a0, 1` (`0x00150513`), straddling Bank 0 `[63:48]` (`0x0513`)
 *   and Bank 1 `[15:0]` (`0x0015`)
 * - Offset 0x0a: `ret` (`0x00008067`)
 */
extern uint32_t target_straddle_rden_fault(uint32_t val);
__asm__(
    ".section .subtest2_text, \"ax\", @progbits\n"
    ".balign 64\n"
    ".global target_straddle_rden_fault\n"
    ".type target_straddle_rden_fault, @function\n"
    "target_straddle_rden_fault:\n"
    ".half 0x0001\n"      // Offset 0x00: c.nop
    ".half 0x0001\n"      // Offset 0x02: c.nop
    ".half 0xa009\n"      // Offset 0x04: c.j +2 -> jumps to Offset 0x06 (addr[2:1] == 2'b11)
    ".word 0x00150513\n"  // Offset 0x06: addi a0, a0, 1 (straddles Bank 0 and Bank 1)
    ".word 0x00008067\n"  // Offset 0x0a: ret
    ".rept 13\n"
    ".word 0x00000013\n"
    ".endr\n"
    ".size target_straddle_rden_fault, .-target_straddle_rden_fault\n"
    ".previous\n"
);

/**
 * Sub-test 2 Bank-1 stale-data primer placed at `0x8000bc00` (`.subtest2_stale`):
 * - Reads 3 distinct Bank-1 rows (`0x8000bc08`, `0x8000bc18`, `0x8000bc28`, whose
 *   upper halfword at `[15:0]` is `0x0005` from `addi a0, a0, 0` = `0x00050513`),
 *   overflowing the 2-entry read-bypass buffer (`ICACHE_NUM_BYPASS = 2`) and jumping
 *   directly to `target_straddle_rden_fault + 6` at `0x8000b406`.
 * - Because `(0x8000bc00 ^ 0x8000b400) >> 6 == 0x0020`, when `RV_ICACHE_ADDR_XOR=1`,
 *   reading stale Bank 1 from `0x8000bc28` during `0x8000b406` produces `0x0005 ^ 0x0020 = 0x0025`
 *   (`addi a0, a0, 2`) with a 1-bit Address-XOR error (`0x0020`) in Bank 1.
 */
extern uint32_t prime_and_jump_straddle(uint32_t val);
__asm__(
    ".section .subtest2_stale, \"ax\", @progbits\n"
    ".balign 64\n"
    ".global prime_and_jump_straddle\n"
    ".type prime_and_jump_straddle, @function\n"
    "prime_and_jump_straddle:\n"
    // Sub-line 0 (0x8000bc00..0x8000bc0f): Bank 1 at 0x8000bc08 has [15:0] = 0x0005
    ".half 0x0001\n"      // Offset 0x00: c.nop
    ".half 0x0001\n"      // Offset 0x02: c.nop
    ".half 0x0001\n"      // Offset 0x04: c.nop
    ".word 0x00050513\n"  // Offset 0x06: addi a0, a0, 0 (Bank 1 0x8000bc08 [15:0] = 0x0005)
    ".half 0x0001\n"      // Offset 0x0a: c.nop
    ".half 0x0001\n"      // Offset 0x0c: c.nop
    ".half 0x0001\n"      // Offset 0x0e: c.nop
    // Sub-line 1 (0x8000bc10..0x8000bc1f): Bank 1 at 0x8000bc18 has [15:0] = 0x0005
    ".half 0x0001\n"      // Offset 0x10: c.nop
    ".half 0x0001\n"      // Offset 0x12: c.nop
    ".half 0x0001\n"      // Offset 0x14: c.nop
    ".word 0x00050513\n"  // Offset 0x16: addi a0, a0, 0 (Bank 1 0x8000bc18 [15:0] = 0x0005)
    ".half 0x0001\n"      // Offset 0x1a: c.nop
    ".half 0x0001\n"      // Offset 0x1c: c.nop
    ".half 0x0001\n"      // Offset 0x1e: c.nop
    // Sub-line 2 (0x8000bc20..0x8000bc2f): Bank 1 at 0x8000bc28 has [15:0] = 0x0005
    // Accessing a 3rd distinct Bank-1 row overflows the 2-entry read-bypass buffer
    // (`ICACHE_NUM_BYPASS = 2`), guaranteeing a real Bank-1 SRAM read before jumping to 0x8000b406.
    ".half 0x0001\n"      // Offset 0x20: c.nop
    ".half 0x0001\n"      // Offset 0x22: c.nop
    ".half 0x0001\n"      // Offset 0x24: c.nop
    ".word 0x00050513\n"  // Offset 0x26: addi a0, a0, 0 (Bank 1 0x8000bc28 [15:0] = 0x0005)
    "j (target_straddle_rden_fault + 6)\n"  // Offset 0x2a: jump directly to 0x8000b406
    ".half 0x0001\n"      // Offset 0x2e: c.nop
    // Sub-line 3 (0x8000bc30..0x8000bc3f): Bank 1 at 0x8000bc38 also has [15:0] = 0x0005
    ".half 0x0001\n"      // Offset 0x30: c.nop
    ".half 0x0001\n"      // Offset 0x32: c.nop
    ".half 0x0001\n"      // Offset 0x34: c.nop
    ".word 0x00050513\n"  // Offset 0x36: addi a0, a0, 0 (Bank 1 0x8000bc38 [15:0] = 0x0005)
    ".half 0x0001\n"      // Offset 0x3a: c.nop
    ".half 0x0001\n"      // Offset 0x3c: c.nop
    ".half 0x0001\n"      // Offset 0x3e: c.nop
    ".size prime_and_jump_straddle, .-prime_and_jump_straddle\n"
    ".previous\n"
);

/**
 * Sub-test 3 & Sub-test 4 single-cacheline target placed at `0x8000d000` (`.subtest3_text`):
 * - `target_rot_fault` at Offset 0x00 (`0x8000d000`, Bank 0):
 *     - Offset 0x00 (`addr[2:1] == 2'b00`): `addi a0, a0, 1` (`0x00150513`)
 *     - Offset 0x04 (`addr[2:1] == 2'b10`): `ret` (`0x00008067`)
 * - `target_bank_swap_fault` at Offset 0x1c (`0x8000d01c`, Bank 1 row 1):
 *     - Steps across 3 distinct Bank-1 rows (`0x18`, `0x28`, `0x38`) inside the
 *       SAME 64-byte cache line (`0x8000d000..0x8000d03f`), overflowing the 2-entry
 *       `rd_data_hold_ff` bypass buffer so Bank-1 SRAM output `wb_dout_pre_up[way][1]`
 *       holds `{j ..., ret}` encoded with valid ECC/Parity AND `0x8000d000`'s exact
 *       Address-XOR mask right before jumping to `target_rot_fault` (`0x8000d000`).
 */
extern uint32_t target_rot_fault(uint32_t val);
extern uint32_t target_bank_swap_fault(uint32_t val);
__asm__(
    ".section .subtest3_text, \"ax\", @progbits\n"
    ".balign 64\n"
    ".global target_rot_fault\n"
    ".type target_rot_fault, @function\n"
    "target_rot_fault:\n"
    // Sub-line 0, Bank 0 (0x00..0x07):
    ".word 0x00150513\n"        // Offset 0x00: addi a0, a0, 1
    ".word 0x00008067\n"        // Offset 0x04: ret
    // Sub-line 0, Bank 1 (0x08..0x0f):
    ".word 0x00008067\n"        // Offset 0x08: ret
    ".word 0x00000013\n"        // Offset 0x0c: nop
    // Sub-line 1, Bank 0 (0x10..0x17):
    ".word 0x00000013\n"        // Offset 0x10: nop
    ".word 0x00000013\n"        // Offset 0x14: nop
    // Sub-line 1, Bank 1 (0x18..0x1f): [31:0] = ret, [63:32] = jal x0, +16 (Offset 0x2c)
    ".word 0x00008067\n"        // Offset 0x18: ret
    ".global target_bank_swap_fault\n"
    ".type target_bank_swap_fault, @function\n"
    "target_bank_swap_fault:\n"
    ".word 0x0100006f\n"        // Offset 0x1c: j +0x10 -> Offset 0x2c
    // Sub-line 2, Bank 0 (0x20..0x27):
    ".word 0x00000013\n"        // Offset 0x20: nop
    ".word 0x00000013\n"        // Offset 0x24: nop
    // Sub-line 2, Bank 1 (0x28..0x2f): [31:0] = ret, [63:32] = jal x0, +16 (Offset 0x3c)
    ".word 0x00008067\n"        // Offset 0x28: ret
    ".word 0x0100006f\n"        // Offset 0x2c: j +0x10 -> Offset 0x3c
    // Sub-line 3, Bank 0 (0x30..0x37):
    ".word 0x00000013\n"        // Offset 0x30: nop
    ".word 0x00000013\n"        // Offset 0x34: nop
    // Sub-line 3, Bank 1 (0x38..0x3f): [31:0] = ret, [63:32] = jal x0, -60 (Offset 0x00)
    ".word 0x00008067\n"        // Offset 0x38: ret
    ".word 0xfc5ff06f\n"        // Offset 0x3c: j -0x3c -> target_rot_fault (Offset 0x00)
    ".if (.-target_rot_fault) != 64\n"
    ".err\n"
    ".endif\n"
    ".size target_rot_fault, .-target_rot_fault\n"
    ".previous\n"
);

/**
 * Helper that writes `cmd` to `mailbox`, drains the store buffer with `fence`,
 * and immediately invokes `fn(0)` from within a single warm 64-byte cache line.
 */
__attribute__((noinline, aligned(64)))
uint32_t call_with_mailbox_u32(uint32_t (*fn)(uint32_t), uint32_t cmd) {
    if (cmd != 0U) {
        *mailbox = cmd;
        __asm__ volatile ("fence" ::: "memory");
    }
    return fn(0U);
}

int main(void) {
    uint32_t failures = 0U;

    printf("=== Starting EL2_IC_DATA Outside-DCLS Boundary Test ===\n");
    write_csr(MICECT_CSR_ADDR, 0UL);

    // Warm up `call_with_mailbox_u32` and all target cache lines
    uint32_t warm1 = call_with_mailbox_u32(target_bank_check_en_fault, 0U);
    uint32_t warm2 = call_with_mailbox_u32(prime_and_jump_straddle, 0U);
    uint32_t warm3 = call_with_mailbox_u32(target_rot_fault, 0U);
    uint32_t warm4 = call_with_mailbox_u32(target_bank_swap_fault, 0U);
    if ((warm1 != 1U) || (warm2 != 1U) || (warm3 != 1U) || (warm4 != 1U)) {
        printf("ERROR: Warmup failed (warm1=%u, warm2=%u, warm3=%u, warm4=%u)\n",
               (unsigned int)warm1, (unsigned int)warm2,
               (unsigned int)warm3, (unsigned int)warm4);
        *mailbox = CMD_TEST_FAILED;
        while (true) {
        }
    }

    // =========================================================================
    // Sub-test 1: `ic_b_rden_ff` forced to 2'b00 in `EL2_IC_DATA` (outside DCLS)
    // during a 1-bit upper-bank data flip on `ic_rd_data` at `0x8000b006`.
    // =========================================================================
    printf("\n--- Sub-test 1: EL2_IC_DATA.ic_b_rden_ff = 2'b00 with 1-bit Data Fault ---\n");
    (void)call_with_mailbox_u32(target_bank_check_en_fault, 0U);
    unsigned long micect_pre1 = read_csr(MICECT_CSR_ADDR);
    uint32_t cmd1 = (MODE_BANK_CHECK_EN_FAULT << 8) | CMD_INJECT_IC_DCLS_BOUNDARY;
    uint32_t res1 = call_with_mailbox_u32(target_bank_check_en_fault, cmd1);
    unsigned long micect_post1 = read_csr(MICECT_CSR_ADDR);
    unsigned long delta1 = micect_post1 - micect_pre1;

    printf("Sub-test 1: res=%u (expected 1), micect_delta=%u (expected >=1)\n",
           (unsigned int)res1, (unsigned int)delta1);
    if ((res1 != 1U) || (delta1 == 0UL)) {
        printf("[FAIL] Sub-test 1: Fault on EL2_IC_DATA check-enable flops (outside DCLS) "
               "disabled core ECC/Parity check and executed corrupted instruction!\n");
        failures++;
    } else {
        printf("[PASS] Sub-test 1: Core detected data fault despite EL2_IC_DATA.ic_b_rden_ff fault.\n");
    }

    // =========================================================================
    // Sub-test 2: Single-bit fault `ic_b_rden[1] = 1'b0` in `EL2_IC_DATA`
    // (outside DCLS) during a cross-bank straddling fetch at `0x8000b406`.
    // =========================================================================
    printf("\n--- Sub-test 2: EL2_IC_DATA.ic_b_rden[1] = 1'b0 on Cross-Bank Fetch ---\n");
    (void)call_with_mailbox_u32(prime_and_jump_straddle, 0U);
    unsigned long micect_pre2 = read_csr(MICECT_CSR_ADDR);
    uint32_t cmd2 = (MODE_BANK1_RDEN_FAULT << 8) | CMD_INJECT_IC_DCLS_BOUNDARY;
    uint32_t res2 = call_with_mailbox_u32(prime_and_jump_straddle, cmd2);
    unsigned long micect_post2 = read_csr(MICECT_CSR_ADDR);
    unsigned long delta2 = micect_post2 - micect_pre2;

#ifdef RV_ICACHE_ADDR_XOR
    printf("Sub-test 2: res=%u (expected 1), micect_delta=%u (expected >=1)\n",
           (unsigned int)res2, (unsigned int)delta2);
    if ((res2 != 1U) || (delta2 == 0UL)) {
        printf("[FAIL] Sub-test 2: Single-bit fault on EL2_IC_DATA.ic_b_rden[1]=0 suppressed "
               "Bank-1 SRAM read AND disabled bank check, executing stale/XOR-corrupted "
               "instruction (res=%u) without ECC/Parity/Address-XOR/DCLS detection!\n",
               (unsigned int)res2);
        failures++;
    } else {
        printf("[PASS] Sub-test 2: Core detected cross-bank ic_b_rden[1] fault.\n");
    }
#else
    printf("Sub-test 2 [ICACHE_ADDR_XOR=0 negative check]: res=%u (expected 0), micect_delta=%u (expected 0)\n",
           (unsigned int)res2, (unsigned int)delta2);
    if ((res2 != 0U) || (delta2 != 0UL)) {
        printf("[FAIL] Sub-test 2: Unexpected result with ICACHE_ADDR_XOR=0 (res=%u, micect_delta=%u)\n",
               (unsigned int)res2, (unsigned int)delta2);
        failures++;
    } else {
        printf("[PASS] Sub-test 2: Verified stale cross-line Bank-1 codeword slips undetected when ICACHE_ADDR_XOR=0.\n");
    }
#endif

    // =========================================================================
    // Sub-test 3: Fault on `ic_rw_addr_ff[2:1]` (`2'b10`) in `EL2_IC_DATA`
    // (outside DCLS) during an aligned fetch hit at `0x8000d000`.
    // =========================================================================
    printf("\n--- Sub-test 3: EL2_IC_DATA.ic_rw_addr_ff[2:1] Rotator Offset Fault ---\n");
    (void)call_with_mailbox_u32(target_rot_fault, 0U);
    unsigned long micect_pre3 = read_csr(MICECT_CSR_ADDR);
    uint32_t cmd3 = (MODE_ADDR_LO_ROT_FAULT << 8) | CMD_INJECT_IC_DCLS_BOUNDARY;
    uint32_t res3 = call_with_mailbox_u32(target_rot_fault, cmd3);
    unsigned long micect_post3 = read_csr(MICECT_CSR_ADDR);
    unsigned long delta3 = micect_post3 - micect_pre3;

    printf("Sub-test 3: res=%u (expected 1), micect_delta=%u\n",
           (unsigned int)res3, (unsigned int)delta3);
    if (res3 != 1U) {
        printf("[FAIL] Sub-test 3: Fault on EL2_IC_DATA.ic_rw_addr_ff[2:1] rotated 64-bit bank "
               "post-ECC/Parity check, skipping instruction undetected!\n");
        failures++;
    } else {
        printf("[PASS] Sub-test 3: Core rotator unaffected by EL2_IC_DATA.ic_rw_addr_ff[2:1] fault.\n");
    }

    // =========================================================================
    // Sub-test 4: Fault on `ic_rw_addr_ff[3]` (`1'b1`) in `EL2_IC_DATA`
    // (outside DCLS) swapping physical Bank 0 / Bank 1 on `0x8000d000`.
    // =========================================================================
    printf("\n--- Sub-test 4: EL2_IC_DATA.ic_rw_addr_ff[3] Physical Bank-Select Fault ---\n");
    (void)call_with_mailbox_u32(target_bank_swap_fault, 0U);
    unsigned long micect_pre4 = read_csr(MICECT_CSR_ADDR);
    uint32_t cmd4 = (MODE_BANK_SEL_SWAP_FAULT << 8) | CMD_INJECT_IC_DCLS_BOUNDARY;
    uint32_t res4 = call_with_mailbox_u32(target_bank_swap_fault, cmd4);
    unsigned long micect_post4 = read_csr(MICECT_CSR_ADDR);
    unsigned long delta4 = micect_post4 - micect_pre4;

    printf("Sub-test 4: res=%u (expected 1), micect_delta=%u\n",
           (unsigned int)res4, (unsigned int)delta4);
    if (res4 != 1U) {
        printf("[FAIL] Sub-test 4: Fault on EL2_IC_DATA.ic_rw_addr_ff[3] swapped same-line "
               "Bank 1 onto Bank 0 undetected across ECC/Parity/Address-XOR/DCLS!\n");
        failures++;
    } else {
        printf("[PASS] Sub-test 4: Core bank select unaffected by EL2_IC_DATA.ic_rw_addr_ff[3] fault.\n");
    }

    // =========================================================================
    // Final Summary
    // =========================================================================
    printf("\n=== Summary: %u / 4 sub-tests failed ===\n", (unsigned int)failures);
    if (failures != 0U) {
        *mailbox = CMD_TEST_FAILED;
        while (true) {
        }
    }

    *mailbox = CMD_TEST_PASSED;
    while (true) {
    }
    return 0;
}
