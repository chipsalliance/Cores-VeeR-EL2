/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * dcls_discrepancy_latency.c
 *
 * Scenario 15 (Discrepancy Latency - Negative + Propagation Test):
 * Induce register mismatch across all 31 GPRs (x1..x31) and all 13 Monitored TLU CSRs
 * on both Main Core and Shadow Core with lockstep_regfile_enable=0:
 *   1. Cases 0..87 (62 GPR + 26 CSR):
 *      - Phase 1 (Latency Check): Inject register mismatch and perform 50 internal
 *        read + ALU + GPR writeback iterations into live scratch GPRs (rd != x0)
 *        without driving any core output port. Verify NO immediate DCLS error occurs.
 *        Note: For mstatus_rf, mtval_rf, mie_rf, and mip_rf, tb_top.sv forces the
 *        internal *_rf CSR read-mux / regfile-monitor wires (consistent with
 *        dcls_regfile_read isolation) rather than control/trace-driving flops.
 *      - Phase 2 (Output Propagation): Propagate the corrupted register value to
 *        a monitored core output port (DCCM store -> dccm_wr_data_lo) and verify
 *        that the DCLS output comparator detects the discrepancy and triggers a
 *        valid DCLS trap (verified via mcause and PIC MEIP[2]).
 *   2. Cases 88..89 (mtval_ff storage flop on Main & Shadow Core):
 *      - Verify that a bit flip in the actual mtval_ff storage flop (which drives
 *        trace_rv_i_tval_ip unconditionally) has zero discrepancy latency and
 *        immediately triggers a valid DCLS output-comparator trap without any
 *        software store.
 */

#include "dcls_discrepancy_latency.h"
#include <stdio.h>
#include <defines.h>

#define TOTAL_GPR_TESTS       62U
#define TOTAL_CSR_TESTS       26U
#define TOTAL_LATENCY_CASES   (TOTAL_GPR_TESTS + TOTAL_CSR_TESTS)
#define TOTAL_IMMEDIATE_CASES 2U
#define TOTAL_TEST_CASES      (TOTAL_LATENCY_CASES + TOTAL_IMMEDIATE_CASES)

volatile uint32_t boot_count                 __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t latency_verified_count     __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t propagation_verified_count __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t error_count                __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t propagate_phase            __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t trap_pending               __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t propagate_scratch          __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t g_inj_val                  __attribute__((section(".dccm.persistent"))) = 0;

volatile uint32_t *threshold    = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIPT_OFFSET);
volatile uint32_t *gateway      = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIGWCTRL_OFFSET);
volatile uint32_t *clr_gateway  = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIGWCLR_OFFSET);
volatile uint32_t *priority     = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIPL_OFFSET);
volatile uint32_t *enable       = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIE_OFFSET);
volatile uint32_t *meip         = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIP_OFFSET);

static void print_str(const char *s) {
    while (*s) {
        tohost = (uint32_t)(uint8_t)(*s++);
    }
}

static const char * const gpr_names[32] = {
    "zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2",
    "s0/fp", "s1", "a0", "a1", "a2", "a3", "a4", "a5",
    "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7",
    "s8", "s9", "s10", "s11", "t3", "t4", "t5", "t6"
};

void trap_handler(void) {
    uint32_t mstatus          = (uint32_t)read_csr(mstatus);
    uint32_t mcause           = (uint32_t)read_csr(mcause);
    uint32_t mepc             = (uint32_t)read_csr(mepc);
    uint32_t dcls_irq_pending = ((*meip >> 2) & 1U);
    uint32_t valid_mcause     = (mcause == MCAUSE_MEI || mcause == MCAUSE_FIR_NON_DCCM);

    WRITE_MBOX(CMD_INJ_CLEAR);
    WRITE_MBOX(CLEAR_NMI_INT);

    if (propagate_phase == 0U) {
        printf("Error: [LATENCY] Unexpected immediate trap before output propagation! "
               "mstatus=0x%08X, mcause=0x%08X, mepc=0x%08X, meip2=%u\n",
               (unsigned int)mstatus, (unsigned int)mcause,
               (unsigned int)mepc, (unsigned int)dcls_irq_pending);
        error_count++;
    } else if (!valid_mcause || !dcls_irq_pending) {
        printf("Error: [PROPAGATION] Unexpected trap cause or missing DCLS IRQ! "
               "mstatus=0x%08X, mcause=0x%08X, mepc=0x%08X, meip2=%u\n",
               (unsigned int)mstatus, (unsigned int)mcause,
               (unsigned int)mepc, (unsigned int)dcls_irq_pending);
        error_count++;
    } else {
        propagation_verified_count++;
        printf("trap (output propagation verified, count=%u)! "
               "mstatus=0x%08X, mcause=0x%08X, mepc=0x%08X\n",
               (unsigned int)propagation_verified_count,
               (unsigned int)mstatus, (unsigned int)mcause, (unsigned int)mepc);
    }

    trap_pending = 0U;
    WRITE_MBOX(CMD_RST);
    while (1);
}

/*
 * Phase 1 (GPR Latency Check):
 * Save xN, inject fault on xN, initialize xN with bit 0 = 0, then execute 50
 * internal read + ALU + GPR writeback iterations into live scratch GPR s3 (rd != x0)
 * without driving any core output port (2*xN + 1 preserves divergence at every bit).
 * Clear injection, scrub s3, and restore xN.
 */
#define READ_GPR_ASM(n, s0, s1, s2, s3) \
    asm volatile( \
        "mv   " #s0 ", x" #n "\n\t" \
        "la   " #s1 ", g_inj_val\n\t" \
        "lw   " #s1 ", 0(" #s1 ")\n\t" \
        "li   " #s2 ", 0xd0580000\n\t" \
        "sw   " #s1 ", 0(" #s2 ")\n\t" \
        "fence\n\t" \
        ".rept 6\n\t" \
        "nop\n\t" \
        ".endr\n\t" \
        "li   x" #n ", 0x12345670\n\t" \
        ".rept 4\n\t" \
        "nop\n\t" \
        ".endr\n\t" \
        "li   " #s3 ", 0\n\t" \
        ".rept 50\n\t" \
        "mv   " #s3 ", x" #n "\n\t" \
        "addi " #s3 ", " #s3 ", 1\n\t" \
        "add  " #s3 ", " #s3 ", x" #n "\n\t" \
        ".endr\n\t" \
        "li   " #s1 ", 0x95\n\t" \
        "sb   " #s1 ", 0(" #s2 ")\n\t" \
        "fence\n\t" \
        ".rept 6\n\t" \
        "nop\n\t" \
        ".endr\n\t" \
        "li   " #s3 ", 0\n\t" \
        "mv   x" #n ", " #s0 "\n\t" \
        ::: #s0, #s1, #s2, #s3, "memory" \
    )

#define CASE_GPR(n) \
    case n: \
        READ_GPR_ASM(n, t0, t1, t2, t3); \
        break;

#define CASE_GPR_ALT(n) \
    case n: \
        READ_GPR_ASM(n, t4, t5, t6, a7); \
        break;

static void __attribute__((noinline)) verify_gpr_latency(uint32_t reg, uint32_t err_id, uint32_t cmd) {
    g_inj_val = ((err_id) << 8) | (cmd);
    switch (reg) {
        CASE_GPR(1);
        CASE_GPR(2);
        CASE_GPR(3);
        CASE_GPR(4);
        CASE_GPR_ALT(5);
        CASE_GPR_ALT(6);
        CASE_GPR_ALT(7);
        CASE_GPR(8);
        CASE_GPR(9);
        CASE_GPR(10);
        CASE_GPR(11);
        CASE_GPR(12);
        CASE_GPR(13);
        CASE_GPR(14);
        CASE_GPR(15);
        CASE_GPR(16);
        CASE_GPR(17);
        CASE_GPR(18);
        CASE_GPR(19);
        CASE_GPR(20);
        CASE_GPR(21);
        CASE_GPR(22);
        CASE_GPR(23);
        CASE_GPR(24);
        CASE_GPR(25);
        CASE_GPR(26);
        CASE_GPR(27);
        CASE_GPR_ALT(28);
        CASE_GPR(29);
        CASE_GPR(30);
        CASE_GPR(31);
        default: break;
    }
}

/*
 * Phase 2 (GPR Output Propagation):
 * Inject fault on xN, initialize xN with bit 0 = 0, wait for writeback so xN is
 * read from gprff.dout, store xN to DCCM (propagate_scratch -> dccm_wr_data_lo),
 * immediately restore xN (so sp/ra remain valid before fence/trap entry), and wait
 * for the DCLS output comparator to trigger a trap.
 */
#define PROP_GPR_ASM(n, s0, s1, s2) \
    asm volatile( \
        "mv   " #s0 ", x" #n "\n\t" \
        "la   " #s1 ", g_inj_val\n\t" \
        "lw   " #s1 ", 0(" #s1 ")\n\t" \
        "li   " #s2 ", 0xd0580000\n\t" \
        "sw   " #s1 ", 0(" #s2 ")\n\t" \
        "fence\n\t" \
        ".rept 6\n\t" \
        "nop\n\t" \
        ".endr\n\t" \
        "li   x" #n ", 0x12345670\n\t" \
        ".rept 4\n\t" \
        "nop\n\t" \
        ".endr\n\t" \
        "la   " #s1 ", propagate_scratch\n\t" \
        "sw   x" #n ", 0(" #s1 ")\n\t" \
        "mv   x" #n ", " #s0 "\n\t" \
        "fence\n\t" \
        ".rept 50\n\t" \
        "nop\n\t" \
        ".endr\n\t" \
        "li   " #s1 ", 0x95\n\t" \
        "sb   " #s1 ", 0(" #s2 ")\n\t" \
        "fence\n\t" \
        ".rept 20\n\t" \
        "nop\n\t" \
        ".endr\n\t" \
        ::: #s0, #s1, #s2, "memory" \
    )

#define CASE_PROP_GPR(n) \
    case n: \
        PROP_GPR_ASM(n, t0, t1, t2); \
        break;

#define CASE_PROP_GPR_ALT(n) \
    case n: \
        PROP_GPR_ASM(n, t3, t4, t5); \
        break;

static void __attribute__((noinline)) propagate_gpr_to_output(uint32_t reg, uint32_t err_id, uint32_t cmd) {
    g_inj_val = ((err_id) << 8) | (cmd);
    switch (reg) {
        CASE_PROP_GPR(1);
        CASE_PROP_GPR(2);
        CASE_PROP_GPR(3);
        CASE_PROP_GPR(4);
        CASE_PROP_GPR_ALT(5);
        CASE_PROP_GPR_ALT(6);
        CASE_PROP_GPR_ALT(7);
        CASE_PROP_GPR(8);
        CASE_PROP_GPR(9);
        CASE_PROP_GPR(10);
        CASE_PROP_GPR(11);
        CASE_PROP_GPR(12);
        CASE_PROP_GPR(13);
        CASE_PROP_GPR(14);
        CASE_PROP_GPR(15);
        CASE_PROP_GPR(16);
        CASE_PROP_GPR(17);
        CASE_PROP_GPR(18);
        CASE_PROP_GPR(19);
        CASE_PROP_GPR(20);
        CASE_PROP_GPR(21);
        CASE_PROP_GPR(22);
        CASE_PROP_GPR(23);
        CASE_PROP_GPR(24);
        CASE_PROP_GPR(25);
        CASE_PROP_GPR(26);
        CASE_PROP_GPR(27);
        CASE_PROP_GPR(28);
        CASE_PROP_GPR(29);
        CASE_PROP_GPR(30);
        CASE_PROP_GPR(31);
        default: break;
    }
}

enum csr_kind_e {
    CSR_KIND_MSCRATCH = 0,
    CSR_KIND_MSTATUS,
    CSR_KIND_MTVEC,
    CSR_KIND_MTVAL,
    CSR_KIND_MCYCLE,
    CSR_KIND_MRAC,
    CSR_KIND_MCYCLEH,
    CSR_KIND_MEPC,
    CSR_KIND_MIE,
    CSR_KIND_MCAUSE,
    CSR_KIND_MIP,
    CSR_KIND_MINSTRET,
    CSR_KIND_MINSTRETH
};

/*
 * Reset CSRs whose injected bits must start at 0 so forcing 1'b1 always produces
 * a deterministic 1-bit divergence between Main Core and Shadow Core.
 */
static void prepare_csr_for_injection(uint32_t csr_kind) {
    switch (csr_kind) {
        case CSR_KIND_MSCRATCH:  write_csr(mscratch, 0);  break;
        case CSR_KIND_MTVAL:     write_csr(mtval, 0);     break;
        case CSR_KIND_MCYCLE:    write_csr(mcycle, 0);    break;
        case CSR_KIND_MCYCLEH:   write_csr(mcycleh, 0);   break;
        case CSR_KIND_MEPC:      write_csr(mepc, 0);      break;
        case CSR_KIND_MCAUSE:    write_csr(mcause, 0);    break;
        case CSR_KIND_MINSTRET:  write_csr(minstret, 0);  break;
        case CSR_KIND_MINSTRETH: write_csr(minstreth, 0); break;
        default: break;
    }
}

/*
 * Phase 1 (CSR Latency Check):
 * Inject fault on CSR, then read CSR into live GPR t0 and execute internal ALU +
 * GPR writeback (t1 = 2*t0 + 1, which preserves divergence at every injected bit
 * position k <= 30) across 50 iterations without driving any core output port.
 * Clear injection and scrub t0/t1 inside the same asm block.
 */
#define VERIFY_CSR_ASM(csr) \
    asm volatile( \
        "la   t1, g_inj_val\n\t" \
        "lw   t1, 0(t1)\n\t" \
        "li   t2, 0xd0580000\n\t" \
        "sw   t1, 0(t2)\n\t" \
        "fence\n\t" \
        ".rept 6\n\t" \
        "nop\n\t" \
        ".endr\n\t" \
        "li   t0, 0\n\t" \
        "li   t1, 0\n\t" \
        ".rept 50\n\t" \
        "csrr t0, " #csr "\n\t" \
        "addi t1, t0, 1\n\t" \
        "add  t1, t1, t0\n\t" \
        ".endr\n\t" \
        "li   t1, 0x95\n\t" \
        "sb   t1, 0(t2)\n\t" \
        "fence\n\t" \
        ".rept 6\n\t" \
        "nop\n\t" \
        ".endr\n\t" \
        "li   t0, 0\n\t" \
        "li   t1, 0\n\t" \
        ::: "t0", "t1", "t2", "memory" \
    )

static void __attribute__((noinline)) verify_csr_latency(uint32_t csr_kind, uint16_t err_id, uint8_t cmd) {
    g_inj_val = ((uint32_t)err_id << 8) | (uint32_t)cmd;
    prepare_csr_for_injection(csr_kind);
    switch (csr_kind) {
        case CSR_KIND_MSCRATCH:  VERIFY_CSR_ASM(mscratch);  break;
        case CSR_KIND_MSTATUS:   VERIFY_CSR_ASM(mstatus);   break;
        case CSR_KIND_MTVEC:     VERIFY_CSR_ASM(mtvec);     break;
        case CSR_KIND_MTVAL:     VERIFY_CSR_ASM(mtval);     break;
        case CSR_KIND_MCYCLE:    VERIFY_CSR_ASM(mcycle);    break;
        case CSR_KIND_MRAC:      VERIFY_CSR_ASM(0x7c0);     break;
        case CSR_KIND_MCYCLEH:   VERIFY_CSR_ASM(mcycleh);   break;
        case CSR_KIND_MEPC:      VERIFY_CSR_ASM(mepc);      break;
        case CSR_KIND_MIE:       VERIFY_CSR_ASM(mie);       break;
        case CSR_KIND_MCAUSE:    VERIFY_CSR_ASM(mcause);    break;
        case CSR_KIND_MIP:       VERIFY_CSR_ASM(mip);       break;
        case CSR_KIND_MINSTRET:  VERIFY_CSR_ASM(minstret);  break;
        case CSR_KIND_MINSTRETH: VERIFY_CSR_ASM(minstreth); break;
        default: break;
    }
}

/*
 * Phase 2 (CSR Output Propagation):
 * Inject fault on CSR, read CSR into t0, store t0 to DCCM (propagate_scratch),
 * wait for DCLS output-comparator trap, and clear injection if the trap did not fire.
 */
#define PROP_CSR_ASM(csr) \
    asm volatile( \
        "la   t1, g_inj_val\n\t" \
        "lw   t1, 0(t1)\n\t" \
        "li   t2, 0xd0580000\n\t" \
        "sw   t1, 0(t2)\n\t" \
        "fence\n\t" \
        ".rept 6\n\t" \
        "nop\n\t" \
        ".endr\n\t" \
        "csrr t0, " #csr "\n\t" \
        "la   t1, propagate_scratch\n\t" \
        "sw   t0, 0(t1)\n\t" \
        "fence\n\t" \
        ".rept 50\n\t" \
        "nop\n\t" \
        ".endr\n\t" \
        "li   t1, 0x95\n\t" \
        "sb   t1, 0(t2)\n\t" \
        "fence\n\t" \
        ".rept 20\n\t" \
        "nop\n\t" \
        ".endr\n\t" \
        "li   t0, 0\n\t" \
        ::: "t0", "t1", "t2", "memory" \
    )

static void __attribute__((noinline)) propagate_csr_to_output(uint32_t csr_kind, uint16_t err_id, uint8_t cmd) {
    g_inj_val = ((uint32_t)err_id << 8) | (uint32_t)cmd;
    prepare_csr_for_injection(csr_kind);
    switch (csr_kind) {
        case CSR_KIND_MSCRATCH:  PROP_CSR_ASM(mscratch);  break;
        case CSR_KIND_MSTATUS:   PROP_CSR_ASM(mstatus);   break;
        case CSR_KIND_MTVEC:     PROP_CSR_ASM(mtvec);     break;
        case CSR_KIND_MTVAL:     PROP_CSR_ASM(mtval);     break;
        case CSR_KIND_MCYCLE:    PROP_CSR_ASM(mcycle);    break;
        case CSR_KIND_MRAC:      PROP_CSR_ASM(0x7c0);     break;
        case CSR_KIND_MCYCLEH:   PROP_CSR_ASM(mcycleh);   break;
        case CSR_KIND_MEPC:      PROP_CSR_ASM(mepc);      break;
        case CSR_KIND_MIE:       PROP_CSR_ASM(mie);       break;
        case CSR_KIND_MCAUSE:    PROP_CSR_ASM(mcause);    break;
        case CSR_KIND_MIP:       PROP_CSR_ASM(mip);       break;
        case CSR_KIND_MINSTRET:  PROP_CSR_ASM(minstret);  break;
        case CSR_KIND_MINSTRETH: PROP_CSR_ASM(minstreth); break;
        default: break;
    }
}

/*
 * Direct-output CSR check (mtval_ff.dout[0] -> trace_rv_i_tval_ip[0]):
 * Inject fault directly on the mtval_ff storage flop without any software store
 * and verify immediate DCLS output-comparator detection.
 */
static void __attribute__((noinline)) verify_mtval_ff_immediate_propagation(uint16_t err_id, uint8_t cmd) {
    g_inj_val = ((uint32_t)err_id << 8) | (uint32_t)cmd;
    write_csr(mtval, 0);
    asm volatile(
        "la   t1, g_inj_val\n\t"
        "lw   t1, 0(t1)\n\t"
        "li   t2, 0xd0580000\n\t"
        "sw   t1, 0(t2)\n\t"
        "fence\n\t"
        ".rept 50\n\t"
        "nop\n\t"
        ".endr\n\t"
        "li   t1, 0x95\n\t"
        "sb   t1, 0(t2)\n\t"
        "fence\n\t"
        ".rept 20\n\t"
        "nop\n\t"
        ".endr\n\t"
        ::: "t1", "t2", "memory"
    );
}

int main(void) {
    uint32_t old_boot_count = boot_count;
    boot_count++;

    if (old_boot_count == 0U) {
        printf("[Boot 0] Initial reset...\n");
        WRITE_MBOX(CMD_RST);
        while (1);
    }

    if (trap_pending != 0U) {
        printf("Error: Stray reset detected during Boot %u without entering trap_handler()!\n",
               (unsigned int)(old_boot_count - 1U));
        error_count++;
        trap_pending = 0U;
    }

    if (old_boot_count > 0U) {
        *threshold = 1;
        gateway[2] = (1U << 1) | 0U;
        clr_gateway[2] = 0;
        priority[2] = 7;
        enable[2] = 1;
    }

    uint32_t test_case = old_boot_count - 1U;
    propagate_phase = 0U;
    printf("[Boot %u] Test case %u\n",
           (unsigned int)old_boot_count, (unsigned int)test_case);

    // ---------------------------------------------------------------------
    // Test cases 0 to 61: GPRs x1 to x31 (Main Core: 0-30, Shadow Core: 31-61)
    // ---------------------------------------------------------------------
    if (test_case < TOTAL_GPR_TESTS) {
        uint32_t is_shadow = (test_case > 30U);
        uint32_t reg       = is_shadow ? (test_case - 30U) : (test_case + 1U);
        uint32_t err_id    = is_shadow ? (221U + test_case - 31U) : (221U + test_case);
        uint32_t cmd       = is_shadow ? CMD_INJ_LOCKSTEP : CMD_INJ_VEER;
        const char *core   = is_shadow ? "Shadow Core" : "Main Core";

        // Phase 1: Verify discrepancy latency (no immediate error on internal read/ALU/writeback)
        verify_gpr_latency(reg, err_id, cmd);
        latency_verified_count++;
        printf("[LATENCY OK] x%u (", (unsigned int)reg);
        print_str(gpr_names[reg]);
        printf(") ");
        print_str(core);
        printf(": no immediate error on internal read/writeback (count=%u)\n",
               (unsigned int)latency_verified_count);

        // Phase 2: Propagate corrupted register to DCCM write output port
        propagate_phase = 1U;
        trap_pending    = 1U;
        propagate_gpr_to_output(reg, err_id, cmd);

        printf("Error: [PROPAGATION] reg x%u (", (unsigned int)reg);
        print_str(gpr_names[reg]);
        printf(") ");
        print_str(core);
        printf(" did not trigger DCLS trap after output propagation!\n");
        error_count++;
        trap_pending = 0U;
        WRITE_MBOX(CMD_RST);
        while (1);
    }
    // ---------------------------------------------------------------------
    // Test cases 62 to 87: All 13 Monitored TLU CSRs on both Main & Shadow Core
    // ---------------------------------------------------------------------
    else if (test_case < TOTAL_LATENCY_CASES) {
        static const struct {
            const char *name;
            uint8_t csr_kind;
            uint16_t err_id;
            uint8_t cmd;
            const char *core;
        } csr_tests[TOTAL_CSR_TESTS] = {
            // Main Core (13 TLU CSRs: cases 62..74)
            {"mscratch",  CSR_KIND_MSCRATCH,  252, CMD_INJ_VEER,     "Main Core"},   // 62
            {"mstatus",   CSR_KIND_MSTATUS,   253, CMD_INJ_VEER,     "Main Core"},   // 63
            {"mtvec",     CSR_KIND_MTVEC,     254, CMD_INJ_VEER,     "Main Core"},   // 64
            {"mtval",     CSR_KIND_MTVAL,     255, CMD_INJ_VEER,     "Main Core"},   // 65
            {"mcycle",    CSR_KIND_MCYCLE,    195, CMD_INJ_VEER,     "Main Core"},   // 66
            {"mrac",      CSR_KIND_MRAC,      196, CMD_INJ_VEER,     "Main Core"},   // 67
            {"mcycleh",   CSR_KIND_MCYCLEH,   197, CMD_INJ_VEER,     "Main Core"},   // 68
            {"mepc",      CSR_KIND_MEPC,      207, CMD_INJ_VEER,     "Main Core"},   // 69
            {"mie",       CSR_KIND_MIE,       208, CMD_INJ_VEER,     "Main Core"},   // 70
            {"mcause",    CSR_KIND_MCAUSE,    209, CMD_INJ_VEER,     "Main Core"},   // 71
            {"mip",       CSR_KIND_MIP,       210, CMD_INJ_VEER,     "Main Core"},   // 72
            {"minstret",  CSR_KIND_MINSTRET,  211, CMD_INJ_VEER,     "Main Core"},   // 73
            {"minstreth", CSR_KIND_MINSTRETH, 212, CMD_INJ_VEER,     "Main Core"},   // 74
            // Shadow Core (13 TLU CSRs: cases 75..87)
            {"mscratch",  CSR_KIND_MSCRATCH,  207, CMD_INJ_LOCKSTEP, "Shadow Core"}, // 75
            {"mstatus",   CSR_KIND_MSTATUS,   208, CMD_INJ_LOCKSTEP, "Shadow Core"}, // 76
            {"mtvec",     CSR_KIND_MTVEC,     209, CMD_INJ_LOCKSTEP, "Shadow Core"}, // 77
            {"mtval",     CSR_KIND_MTVAL,     210, CMD_INJ_LOCKSTEP, "Shadow Core"}, // 78
            {"mcycle",    CSR_KIND_MCYCLE,    211, CMD_INJ_LOCKSTEP, "Shadow Core"}, // 79
            {"mrac",      CSR_KIND_MRAC,      212, CMD_INJ_LOCKSTEP, "Shadow Core"}, // 80
            {"mcycleh",   CSR_KIND_MCYCLEH,   213, CMD_INJ_LOCKSTEP, "Shadow Core"}, // 81
            {"mepc",      CSR_KIND_MEPC,      252, CMD_INJ_LOCKSTEP, "Shadow Core"}, // 82
            {"mie",       CSR_KIND_MIE,       253, CMD_INJ_LOCKSTEP, "Shadow Core"}, // 83
            {"mcause",    CSR_KIND_MCAUSE,    254, CMD_INJ_LOCKSTEP, "Shadow Core"}, // 84
            {"mip",       CSR_KIND_MIP,       255, CMD_INJ_LOCKSTEP, "Shadow Core"}, // 85
            {"minstret",  CSR_KIND_MINSTRET,  195, CMD_INJ_LOCKSTEP, "Shadow Core"}, // 86
            {"minstreth", CSR_KIND_MINSTRETH, 196, CMD_INJ_LOCKSTEP, "Shadow Core"}  // 87
        };
        uint32_t idx = test_case - TOTAL_GPR_TESTS;

        // Phase 1: Verify discrepancy latency (no immediate error on internal CSR read/writeback)
        verify_csr_latency(csr_tests[idx].csr_kind, csr_tests[idx].err_id, csr_tests[idx].cmd);
        latency_verified_count++;
        printf("[LATENCY OK] CSR ");
        print_str(csr_tests[idx].name);
        tohost = (uint32_t)' ';
        print_str(csr_tests[idx].core);
        printf(": no immediate error on internal read/writeback (count=%u)\n",
               (unsigned int)latency_verified_count);

        // Phase 2: Propagate corrupted CSR value to DCCM write output port
        propagate_phase = 1U;
        trap_pending    = 1U;
        propagate_csr_to_output(csr_tests[idx].csr_kind, csr_tests[idx].err_id, csr_tests[idx].cmd);

        printf("Error: [PROPAGATION] CSR ");
        print_str(csr_tests[idx].name);
        tohost = (uint32_t)' ';
        print_str(csr_tests[idx].core);
        printf(" did not trigger DCLS trap after output propagation!\n");
        error_count++;
        trap_pending = 0U;
        WRITE_MBOX(CMD_RST);
        while (1);
    }
    // ---------------------------------------------------------------------
    // Test cases 88 to 89: Direct-output mtval_ff storage flop (Main & Shadow)
    // ---------------------------------------------------------------------
    else if (test_case < TOTAL_TEST_CASES) {
        uint32_t is_shadow = (test_case == (TOTAL_LATENCY_CASES + 1U));
        uint16_t err_id    = is_shadow ? 214U : 213U;
        uint8_t cmd        = is_shadow ? CMD_INJ_LOCKSTEP : CMD_INJ_VEER;
        const char *core   = is_shadow ? "Shadow Core" : "Main Core";

        // mtval_ff drives trace_rv_i_tval_ip unconditionally, so corruption must
        // propagate immediately to outputs_corrupted with zero latency.
        propagate_phase = 1U;
        trap_pending    = 1U;
        verify_mtval_ff_immediate_propagation(err_id, cmd);

        printf("Error: [DIRECT OUTPUT] CSR mtval_ff ");
        print_str(core);
        printf(" did not trigger immediate DCLS trap via trace_rv_i_tval_ip!\n");
        error_count++;
        trap_pending = 0U;
        WRITE_MBOX(CMD_RST);
        while (1);
    }
    // ---------------------------------------------------------------------
    // Test completion / summary
    // ---------------------------------------------------------------------
    else {
        if (error_count > 0U ||
            latency_verified_count != TOTAL_LATENCY_CASES ||
            propagation_verified_count != TOTAL_TEST_CASES) {
            printf("Test FAILED with %u errors (latency=%u/%u, propagation=%u/%u)!\n",
                   (unsigned int)error_count,
                   (unsigned int)latency_verified_count, (unsigned int)TOTAL_LATENCY_CASES,
                   (unsigned int)propagation_verified_count, (unsigned int)TOTAL_TEST_CASES);
            SEND_TEST_STATUS(TEST_FAILED);
            while (1) { asm volatile("wfi"); }
        } else {
            printf("All %u discrepancy latency + %u direct-output propagation tests completed with 0 errors!\n",
                   (unsigned int)TOTAL_LATENCY_CASES, (unsigned int)TOTAL_IMMEDIATE_CASES);
            SEND_TEST_STATUS(TEST_PASSED);
            while (1) { asm volatile("wfi"); }
        }
    }

    while (1);
}
