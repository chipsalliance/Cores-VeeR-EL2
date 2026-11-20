/*
 * SPDX-License-Identifier: Apache-2.0
 *
 * dcls_discrepancy_latency.c
 *
 * Scenario (Discrepancy Latency - Negative + Propagation Test):
 * Induce register mismatch across all 31 GPRs (x1..x31) and 13 Monitored TLU CSRs
 * on both Main Core and Shadow Core with lockstep_regfile_enable=0:
 *   1. Phase 1 (Latency Check): Inject register mismatch and execute 50 internal
 *      register reads (mv x0, xN / csrr x0, csr) without touching core outputs.
 *      Verify NO immediate DCLS corruption error occurs.
 *   2. Phase 2 (Output Propagation): Propagate the corrupted register value to
 *      a monitored core output port (DCCM store -> dccm_wr_data_lo) and verify
 *      that the DCLS output comparator detects the discrepancy and triggers a trap.
 */

#include "dcls_discrepancy_latency.h"
#include <stdio.h>
#include <defines.h>

volatile uint32_t boot_count __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t latency_verified_count __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t error_count __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t propagate_phase __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t propagate_scratch __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t g_inj_val __attribute__((section(".dccm.persistent"))) = 0;

volatile uint32_t *threshold    = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIPT_OFFSET);
volatile uint32_t *gateway      = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIGWCTRL_OFFSET);
volatile uint32_t *clr_gateway  = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIGWCLR_OFFSET);
volatile uint32_t *priority     = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIPL_OFFSET);
volatile uint32_t *enable       = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIE_OFFSET);

static void print_str(const char *s) {
    while (*s) {
        tohost = *s++;
    }
}

static const char * const gpr_names[32] = {
    "zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2",
    "s0/fp", "s1", "a0", "a1", "a2", "a3", "a4", "a5",
    "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7",
    "s8", "s9", "s10", "s11", "t3", "t4", "t5", "t6"
};

void trap_handler(void) {
    uint32_t mstatus = read_csr(mstatus);
    uint32_t mcause  = read_csr(mcause);
    uint32_t mepc    = read_csr(mepc);

    tohost = CLEAR_NMI_INT;
    tohost = CMD_INJ_CLEAR;
    if (propagate_phase == 0) {
        printf("Error: [LATENCY] Unexpected immediate trap before output propagation! mstatus=0x%08X, mcause=0x%08X, mepc=0x%08X\n",
               mstatus, mcause, mepc);
        error_count++;
    } else {
        printf("trap (output propagation verified)! mstatus=0x%08X, mcause=0x%08X, mepc=0x%08X\n",
               mstatus, mcause, mepc);
    }
    tohost = CMD_RST;
    while (1);
}

#define READ_GPR_ASM(n, s0, s1, s2) \
    asm volatile( \
        "mv   " #s0 ", x" #n "\n\t" \
        "la   " #s1 ", g_inj_val\n\t" \
        "lw   " #s1 ", 0(" #s1 ")\n\t" \
        "li   " #s2 ", 0xd0580000\n\t" \
        "sw   " #s1 ", 0(" #s2 ")\n\t" \
        "li   x" #n ", 0x12345670\n\t" \
        ".rept 50\n\t" \
        "mv   x0, x" #n "\n\t" \
        ".endr\n\t" \
        "li   " #s1 ", 0x95\n\t" \
        "sw   " #s1 ", 0(" #s2 ")\n\t" \
        ".rept 6\n\t" \
        "nop\n\t" \
        ".endr\n\t" \
        "mv   x" #n ", " #s0 "\n\t" \
        ::: #s0, #s1, #s2, "memory" \
    )

#define CASE_GPR(n) \
    case n: \
        READ_GPR_ASM(n, t0, t1, t2); \
        break;

#define CASE_GPR_ALT(n) \
    case n: \
        READ_GPR_ASM(n, t3, t4, t5); \
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
        CASE_GPR(28);
        CASE_GPR(29);
        CASE_GPR(30);
        CASE_GPR(31);
        default: break;
    }
}

#define PROP_GPR_ASM(n, s0, s1, s2) \
    asm volatile( \
        "mv   " #s0 ", x" #n "\n\t" \
        "la   " #s1 ", g_inj_val\n\t" \
        "lw   " #s1 ", 0(" #s1 ")\n\t" \
        "li   " #s2 ", 0xd0580000\n\t" \
        "sw   " #s1 ", 0(" #s2 ")\n\t" \
        ".rept 6\n\t" \
        "nop\n\t" \
        ".endr\n\t" \
        "li   x" #n ", 0x12345670\n\t" \
        "la   " #s1 ", propagate_scratch\n\t" \
        "sw   x" #n ", 0(" #s1 ")\n\t" \
        "mv   x" #n ", " #s0 "\n\t" \
        ".rept 50\n\t" \
        "nop\n\t" \
        ".endr\n\t" \
        "li   " #s1 ", 0x95\n\t" \
        "sw   " #s1 ", 0(" #s2 ")\n\t" \
        ".rept 6\n\t" \
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

static void __attribute__((noinline)) verify_csr_latency(uint32_t test_case, uint16_t err_id, uint8_t cmd) {
    switch (test_case) {
        case 62: INJECT_ERR(err_id, cmd); asm volatile(".rept 50\n\t csrr x0, mscratch \n\t .endr"); tohost = CMD_INJ_CLEAR; break;
        case 63: INJECT_ERR(err_id, cmd); asm volatile(".rept 50\n\t csrr x0, mstatus  \n\t .endr"); tohost = CMD_INJ_CLEAR; break;
        case 64: INJECT_ERR(err_id, cmd); asm volatile(".rept 50\n\t csrr x0, mtvec    \n\t .endr"); tohost = CMD_INJ_CLEAR; break;
        case 65: INJECT_ERR(err_id, cmd); asm volatile(".rept 50\n\t csrr x0, mtval    \n\t .endr"); tohost = CMD_INJ_CLEAR; break;
        case 66: INJECT_ERR(err_id, cmd); asm volatile(".rept 50\n\t csrr x0, mcycle   \n\t .endr"); tohost = CMD_INJ_CLEAR; break;
        case 67: INJECT_ERR(err_id, cmd); asm volatile(".rept 50\n\t csrr x0, 0x7c0    \n\t .endr"); tohost = CMD_INJ_CLEAR; break;
        case 68: INJECT_ERR(err_id, cmd); asm volatile(".rept 50\n\t csrr x0, mepc     \n\t .endr"); tohost = CMD_INJ_CLEAR; break;
        case 69: INJECT_ERR(err_id, cmd); asm volatile(".rept 50\n\t csrr x0, mie      \n\t .endr"); tohost = CMD_INJ_CLEAR; break;
        case 70: INJECT_ERR(err_id, cmd); asm volatile(".rept 50\n\t csrr x0, mcause   \n\t .endr"); tohost = CMD_INJ_CLEAR; break;
        case 71: INJECT_ERR(err_id, cmd); asm volatile(".rept 50\n\t csrr x0, mip      \n\t .endr"); tohost = CMD_INJ_CLEAR; break;
        case 72: INJECT_ERR(err_id, cmd); asm volatile(".rept 50\n\t csrr x0, minstret \n\t .endr"); tohost = CMD_INJ_CLEAR; break;
        case 73: INJECT_ERR(err_id, cmd); asm volatile(".rept 50\n\t csrr x0, mcycleh  \n\t .endr"); tohost = CMD_INJ_CLEAR; break;
        case 74: INJECT_ERR(err_id, cmd); asm volatile(".rept 50\n\t csrr x0, minstreth\n\t .endr"); tohost = CMD_INJ_CLEAR; break;
        default: break;
    }
    asm volatile(".rept 6\n\t nop\n\t .endr");
}

#define PROP_CSR(csr) \
    do { \
        INJECT_ERR(err_id, cmd); \
        asm volatile( \
            ".rept 6\n\t" \
            "nop\n\t" \
            ".endr\n\t" \
            "csrr t0, " #csr "\n\t" \
            "la   t1, propagate_scratch\n\t" \
            "sw   t0, 0(t1)\n\t" \
            ".rept 50\n\t" \
            "nop\n\t" \
            ".endr\n\t" \
            ::: "t0", "t1", "memory" \
        ); \
        tohost = CMD_INJ_CLEAR; \
    } while (0)

static void __attribute__((noinline)) propagate_csr_to_output(uint32_t test_case, uint16_t err_id, uint8_t cmd) {
    switch (test_case) {
        case 62: PROP_CSR(mscratch);  break;
        case 63: PROP_CSR(mstatus);   break;
        case 64: PROP_CSR(mtvec);     break;
        case 65: PROP_CSR(mtval);     break;
        case 66: PROP_CSR(mcycle);    break;
        case 67: PROP_CSR(0x7c0);     break;
        case 68: PROP_CSR(mepc);      break;
        case 69: PROP_CSR(mie);       break;
        case 70: PROP_CSR(mcause);    break;
        case 71: PROP_CSR(mip);       break;
        case 72: PROP_CSR(minstret);  break;
        case 73: PROP_CSR(mcycleh);   break;
        case 74: PROP_CSR(minstreth); break;
        default: break;
    }
}

int main(void) {
    uint32_t old_boot_count = boot_count;
    boot_count++;

    if (old_boot_count == 0) {
        printf("[Boot 0] Initial reset...\n");
        tohost = CMD_RST;
        while (1);
    }

    if (old_boot_count > 0) {
        *threshold = 1;
        gateway[2] = (1 << 1) | 0;
        clr_gateway[2] = 0;
        priority[2] = 7;
        enable[2] = 1;
    }

    uint32_t test_case = old_boot_count - 1;
    propagate_phase = 0;
    printf("[Boot %d] Test case %d\n", old_boot_count, test_case);

    // ---------------------------------------------------------------------
    // Test cases 0 to 61: GPRs x1 to x31 (Main Core: 0-30, Shadow Core: 31-61)
    // ---------------------------------------------------------------------
    if (test_case <= 61) {
        uint32_t is_shadow = (test_case > 30);
        uint32_t reg       = is_shadow ? (test_case - 30) : (test_case + 1);
        uint32_t err_id    = is_shadow ? (221 + test_case - 31) : (221 + test_case);
        uint32_t cmd       = is_shadow ? CMD_INJ_LOCKSTEP : CMD_INJ_VEER;
        const char *core   = is_shadow ? "Shadow Core" : "Main Core";

        // Phase 1: Verify discrepancy latency (no immediate error on internal reads)
        verify_gpr_latency(reg, err_id, cmd);
        latency_verified_count++;
        printf("[LATENCY OK] x%d (", reg);
        print_str(gpr_names[reg]);
        printf(") ");
        print_str(core);
        printf(": no immediate error on internal reads (count=%d)\n", latency_verified_count);

        // Phase 2: Propagate corrupted register to DCCM write output port
        propagate_phase = 1;
        propagate_gpr_to_output(reg, err_id, cmd);

        printf("Error: [PROPAGATION] reg x%d (", reg);
        print_str(gpr_names[reg]);
        printf(") ");
        print_str(core);
        printf(" did not trigger DCLS trap after output propagation!\n");
        error_count++;
        tohost = CMD_RST;
        while (1);
    }
    // ---------------------------------------------------------------------
    // Test cases 62 to 74: CSRs (Main and Shadow Core)
    // ---------------------------------------------------------------------
    else if (test_case <= 74) {
        static const struct {
            const char *name;
            uint16_t err_id;
            uint8_t cmd;
            const char *core;
        } csr_tests[] = {
            {"mscratch",  252, CMD_INJ_VEER,     "Main Core"},   // 62
            {"mstatus",   253, CMD_INJ_VEER,     "Main Core"},   // 63
            {"mtvec",     254, CMD_INJ_VEER,     "Main Core"},   // 64
            {"mtval",     255, CMD_INJ_VEER,     "Main Core"},   // 65
            {"mcycle",    195, CMD_INJ_VEER,     "Main Core"},   // 66
            {"mrac",      196, CMD_INJ_VEER,     "Main Core"},   // 67
            {"mepc",      252, CMD_INJ_LOCKSTEP, "Shadow Core"}, // 68
            {"mie",       253, CMD_INJ_LOCKSTEP, "Shadow Core"}, // 69
            {"mcause",    254, CMD_INJ_LOCKSTEP, "Shadow Core"}, // 70
            {"mip",       255, CMD_INJ_LOCKSTEP, "Shadow Core"}, // 71
            {"minstret",  195, CMD_INJ_LOCKSTEP, "Shadow Core"}, // 72
            {"mcycleh",   197, CMD_INJ_VEER,     "Main Core"},   // 73
            {"minstreth", 196, CMD_INJ_LOCKSTEP, "Shadow Core"}  // 74
        };
        int idx = test_case - 62;

        // Phase 1: Verify discrepancy latency (no immediate error on internal CSR reads)
        verify_csr_latency(test_case, csr_tests[idx].err_id, csr_tests[idx].cmd);
        latency_verified_count++;
        printf("[LATENCY OK] CSR ");
        print_str(csr_tests[idx].name);
        tohost = ' ';
        print_str(csr_tests[idx].core);
        printf(": no immediate error on internal reads (count=%d)\n", latency_verified_count);

        // Phase 2: Propagate corrupted CSR value to DCCM write output port
        propagate_phase = 1;
        propagate_csr_to_output(test_case, csr_tests[idx].err_id, csr_tests[idx].cmd);

        printf("Error: [PROPAGATION] CSR ");
        print_str(csr_tests[idx].name);
        tohost = ' ';
        print_str(csr_tests[idx].core);
        printf(" did not trigger DCLS trap after output propagation!\n");
        error_count++;
        tohost = CMD_RST;
        while (1);
    }
    // ---------------------------------------------------------------------
    // Test completion / summary
    // ---------------------------------------------------------------------
    else if (test_case >= 75) {
        if (error_count > 0 || latency_verified_count != 75) {
            printf("Test FAILED with %d errors (latency_verified_count=%d/75)!\n",
                   error_count, latency_verified_count);
            SEND_TEST_STATUS(TEST_FAILED);
            while(1) { asm volatile("wfi"); }
        } else {
            printf("All 75 discrepancy latency & output propagation tests completed with 0 errors!\n");
            SEND_TEST_STATUS(TEST_PASSED);
            while(1) { asm volatile("wfi"); }
        }
    }

    while(1);
}
