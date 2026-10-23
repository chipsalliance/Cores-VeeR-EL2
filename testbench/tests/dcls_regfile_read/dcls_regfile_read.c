#include "dcls_regfile_read.h"
#include <stdio.h>

/*
 * Dynamic DCLS GPR Monitoring Configuration:
 * - When RV_LOCKSTEP_REGFILE_READ_ENABLE == 1: ALL 31 GPRs are monitored on read
 *   (62 GPR cases + 13 CSR cases = 75 DCLS traps, 0 non-monitored cases).
 * - When RV_LOCKSTEP_REGFILE_READ_ENABLE == 0: Only ra, sp, fp, and a0..a7 are monitored
 *   (22 GPR cases + 13 CSR cases = 35 DCLS traps, 40 non-monitored cases).
 */
#if defined(RV_LOCKSTEP_REGFILE_READ_ENABLE) && (RV_LOCKSTEP_REGFILE_READ_ENABLE == 1)
  #define IS_GPR_MONITORED(r)     (1)
  #define EXPECTED_DCLS_TRAPS     75U
  #define EXPECTED_NON_MONITORED  0U
#else
  #define IS_GPR_MONITORED(r) ( \
      (r) == 1  || (r) == 2  || (r) == 8  || \
      ((r) >= 10 && (r) <= 17) \
  )
  #define EXPECTED_DCLS_TRAPS     35U
  #define EXPECTED_NON_MONITORED  40U
#endif

volatile uint32_t boot_count          __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t dcls_trap_count     __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t non_monitored_count __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t error_count         __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t expected_trap       __attribute__((section(".dccm.persistent"))) = 0;

volatile uint32_t *threshold    = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIPT_OFFSET);
volatile uint32_t *gateway      = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIGWCTRL_OFFSET);
volatile uint32_t *clr_gateway  = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIGWCLR_OFFSET);
volatile uint32_t *priority     = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIPL_OFFSET);
volatile uint32_t *enable       = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIE_OFFSET);
volatile uint32_t *meip         = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIP_OFFSET);

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
    printf("trap! mstatus=0x%08X, mcause=0x%08X, mepc=0x%08X\n", mstatus, mcause, mepc);

    uint32_t dcls_irq_pending  = ((*meip >> 2) & 1U);
    uint32_t valid_dcls_mcause = (mcause == MCAUSE_MEI || mcause == MCAUSE_NMI_FIR_NON_DCCM);

    if (!expected_trap || !valid_dcls_mcause || !dcls_irq_pending) {
        printf("Error: Unexpected trap (expected_trap=%d, mcause=0x%08X, dcls_irq=%d)!\n",
               expected_trap, mcause, dcls_irq_pending);
        error_count++;
    } else {
        dcls_trap_count++;
    }
    expected_trap = 0;

    tohost = CMD_RST;
    while (1);
}

/* Assumes n != 5 (t0); only called for ABI-monitored GPRs {x1, x2, x8, x10..x17}. */
#define TOGGLE_GPR(n) \
    asm volatile( \
        "mv t0, x" #n "\n\t" \
        "li x" #n ", 0xAAAAAAAA\n\t" \
        "add x0, x" #n ", x" #n "\n\t" \
        ".rept 5\n\t nop\n\t .endr\n\t" \
        "li x" #n ", 0x55555555\n\t" \
        "add x0, x" #n ", x" #n "\n\t" \
        ".rept 5\n\t nop\n\t .endr\n\t" \
        "li x" #n ", 0x00000000\n\t" \
        "add x0, x" #n ", x" #n "\n\t" \
        ".rept 5\n\t nop\n\t .endr\n\t" \
        "mv x" #n ", t0\n\t" \
        ::: "t0" \
    )

/*
 * Assumes n is disjoint from t0 (x5), t1 (x6), t2 (x7) -- holds for all
 * ABI-monitored GPRs {x1, x2, x8, x10..x17}. Preserves xN in t0 prior to fault
 * injection and issues both injection and CMD_INJ_CLEAR through t1/t2 before
 * synchronizing and restoring xN so a non-trapping regression returns cleanly.
 */
#define CASE_MON_GPR(n) \
    case n: { \
        uint32_t inj_word = ((err_id) << 8) | (cmd); \
        TOGGLE_GPR(n); \
        asm volatile( \
            "mv t0, x" #n "\n\t" \
            "mv t1, %[inj]\n\t" \
            "li t2, " CSR_STR(MBOX_ADDR) "\n\t" \
            "sw t1, 0(t2)\n\t" \
            "li x" #n ", 0x12345670\n\t" \
            ".rept 50\n\t" \
            "mv x0, x" #n "\n\t" \
            ".endr\n\t" \
            "li t1, " CSR_STR(CMD_INJ_CLEAR) "\n\t" \
            "sw t1, 0(t2)\n\t" \
            "fence\n\t" \
            ".rept 20\n\t" \
            "nop\n\t" \
            ".endr\n\t" \
            "mv x" #n ", t0\n\t" \
            : \
            : [inj] "r"(inj_word) \
            : "t0", "t1", "t2", "memory" \
        ); \
        break; \
    }

#define CASE_GPR(n) \
    case n: { \
        register uint32_t saved_val; \
        asm volatile("mv %0, x" #n : "=r"(saved_val)); \
        INJECT_ERR(err_id, cmd); \
        asm volatile( \
            "li x" #n ", 0x12345670\n\t" \
            ".rept 50\n\t" \
            "mv x0, x" #n "\n\t" \
            ".endr" \
        ); \
        tohost = CMD_INJ_CLEAR; \
        asm volatile("mv x" #n ", %0" :: "r"(saved_val)); \
        break; \
    }

static void __attribute__((noinline)) trigger_gpr_read(uint32_t reg, uint32_t err_id, uint32_t cmd) {
    switch (reg) {
        CASE_MON_GPR(1);
        CASE_MON_GPR(2);
        CASE_GPR(3);
        CASE_GPR(4);
        CASE_GPR(5);
        CASE_GPR(6);
        CASE_GPR(7);
        CASE_MON_GPR(8);
        CASE_GPR(9);
        CASE_MON_GPR(10);
        CASE_MON_GPR(11);
        CASE_MON_GPR(12);
        CASE_MON_GPR(13);
        CASE_MON_GPR(14);
        CASE_MON_GPR(15);
        CASE_MON_GPR(16);
        CASE_MON_GPR(17);
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

/*
 * Mask global interrupts (mstatus.MIE) across CSR bit-toggle sequences so
 * transient writes to mtvec/mie/etc. cannot vector a stray interrupt to an
 * invalid handler address.
 */
#define TOGGLE_CSR(csr) \
    asm volatile( \
        "csrci mstatus, 0x8\n\t" \
        "li t0, 0xAAAAAAAA\n\t" \
        "li t1, 0x55555555\n\t" \
        "csrr t2, " CSR_STR(csr) "\n\t" \
        "csrw " CSR_STR(csr) ", x0\n\t" \
        "csrw " CSR_STR(csr) ", t0\n\t" \
        "csrw " CSR_STR(csr) ", t1\n\t" \
        "csrw " CSR_STR(csr) ", x0\n\t" \
        "csrw " CSR_STR(csr) ", t2\n\t" \
        ".rept 10\n\t" \
        "nop\n\t" \
        ".endr\n\t" \
        "csrsi mstatus, 0x8\n\t" \
        ::: "t0", "t1", "t2" \
    )

/*
 * When toggling mstatus itself, writing 0xAAAAAAAA temporarily sets MIE (bit 3).
 * Save and zero mie around the mstatus toggle sequence so no maskable interrupt
 * source is enabled during that window, then restore mie and mstatus.MIE.
 */
#define TOGGLE_MSTATUS() \
    asm volatile( \
        "csrci mstatus, 0x8\n\t" \
        "csrrw t3, mie, x0\n\t" \
        "li t0, 0xAAAAAAAA\n\t" \
        "li t1, 0x55555555\n\t" \
        "csrr t2, mstatus\n\t" \
        "csrw mstatus, x0\n\t" \
        "csrw mstatus, t0\n\t" \
        "csrw mstatus, t1\n\t" \
        "csrw mstatus, x0\n\t" \
        "csrw mstatus, t2\n\t" \
        ".rept 10\n\t" \
        "nop\n\t" \
        ".endr\n\t" \
        "csrw mie, t3\n\t" \
        "csrsi mstatus, 0x8\n\t" \
        ::: "t0", "t1", "t2", "t3" \
    )

/*
 * Toggle all 32 bits (0 -> 0xAAAAAAAA -> 0x55555555 -> 0) of a free-running
 * counter CSR (mcycle / minstret) with interrupts masked, and leave it cleared
 * at 0 so bit 16 (0x10000, corresponding to dout[8] of the 24-bit [31:8] slice
 * mcyclel_bff / minstretl_bff) is guaranteed to remain 0 when tb_top.sv forces
 * dout[8] = 1'b1 during the subsequent 50 CSR reads.
 */
#define TOGGLE_COUNTER_CSR(csr) \
    asm volatile( \
        "csrci mstatus, 0x8\n\t" \
        "li t0, 0xAAAAAAAA\n\t" \
        "li t1, 0x55555555\n\t" \
        "csrw " CSR_STR(csr) ", x0\n\t" \
        "csrw " CSR_STR(csr) ", t0\n\t" \
        "csrw " CSR_STR(csr) ", t1\n\t" \
        "csrw " CSR_STR(csr) ", x0\n\t" \
        ".rept 10\n\t" \
        "nop\n\t" \
        ".endr\n\t" \
        "csrsi mstatus, 0x8\n\t" \
        ::: "t0", "t1" \
    )

/*
 * Toggle implemented bits of mip (0x344) with global interrupts masked
 * (assumes pt.TIMER_LEGAL_EN != 0 for internal timer CSRs MITB0/MITB1):
 * - CMD_SET_SOFT_INT (0x84)  -> asserts soft_int  (toggles mip.MSIP, bit 3)
 * - CMD_SET_TIMER_INT (0x85) -> asserts timer_int (toggles mip.MTIP, bit 7)
 * - CSR_MDCCMECT (0x7f2) = 1 -> triggers DCCM correctable error interrupt (toggles mip.MCEIP, bit 30)
 * - CSR_MITB0 (0x7d3) = 0    -> internal timer 0 match (toggles mip.MITIP0, bit 29)
 * - CSR_MITB1 (0x7d6) = 0    -> internal timer 1 match (toggles mip.MITIP1, bit 28)
 * - Clears bits [30:28] via CSR writes and issues a defensive
 *   CMD_CLR_SOFT_TIMER_INT (0x82 with mailbox_data[10:9] = 2'b11, in addition
 *   to tb_top.sv auto-clearing the 1-cycle soft_int/timer_int pulses) before
 *   re-enabling mstatus.MIE so mip_rf[7] is guaranteed 0 prior to INJECT_ERR.
 */
#define TOGGLE_MIP() \
    do { \
        asm volatile("csrci mstatus, 0x8"); \
        tohost = CMD_SET_SOFT_INT; \
        tohost = CMD_SET_TIMER_INT; \
        asm volatile( \
            "fence\n\t" \
            "li t0, 1\n\t" \
            "li t1, -1\n\t" \
            "csrw " CSR_STR(CSR_MDCCMECT) ", t0\n\t" \
            "csrw " CSR_STR(CSR_MITB0) ", x0\n\t" \
            "csrw " CSR_STR(CSR_MITB1) ", x0\n\t" \
            ".rept 6\n\t" \
            "nop\n\t" \
            ".endr\n\t" \
            "csrw " CSR_STR(CSR_MDCCMECT) ", x0\n\t" \
            "csrw " CSR_STR(CSR_MITB0) ", t1\n\t" \
            "csrw " CSR_STR(CSR_MITB1) ", t1\n\t" \
            ::: "t0", "t1" \
        ); \
        tohost = CMD_CLR_SOFT_TIMER_INT; \
        asm volatile( \
            "fence\n\t" \
            ".rept 10\n\t" \
            "nop\n\t" \
            ".endr\n\t" \
            "csrsi mstatus, 0x8\n\t" \
        ); \
    } while (0)

static void __attribute__((noinline)) trigger_csr_read(uint32_t test_case, uint16_t err_id, uint8_t cmd) {
    switch (test_case) {
        case 62: TOGGLE_CSR(mscratch);         INJECT_ERR(err_id, cmd); asm volatile(".rept 50\n\t csrr x0, mscratch \n\t .endr"); tohost = CMD_INJ_CLEAR; break;
        case 63: TOGGLE_MSTATUS();             INJECT_ERR(err_id, cmd); asm volatile(".rept 50\n\t csrr x0, mstatus  \n\t .endr"); tohost = CMD_INJ_CLEAR; break;
        case 64: TOGGLE_CSR(mtvec);            INJECT_ERR(err_id, cmd); asm volatile(".rept 50\n\t csrr x0, mtvec    \n\t .endr"); tohost = CMD_INJ_CLEAR; break;
        case 65: TOGGLE_CSR(mtval);            INJECT_ERR(err_id, cmd); asm volatile(".rept 50\n\t csrr x0, mtval    \n\t .endr"); tohost = CMD_INJ_CLEAR; break;
        case 66: TOGGLE_COUNTER_CSR(mcycle);   INJECT_ERR(err_id, cmd); asm volatile(".rept 50\n\t csrr x0, mcycle   \n\t .endr"); tohost = CMD_INJ_CLEAR; break;
        case 67: TOGGLE_CSR(CSR_MRAC);         INJECT_ERR(err_id, cmd); asm volatile(".rept 50\n\t csrr x0, " CSR_STR(CSR_MRAC) " \n\t .endr"); tohost = CMD_INJ_CLEAR; break;
        case 68: TOGGLE_CSR(mepc);             INJECT_ERR(err_id, cmd); asm volatile(".rept 50\n\t csrr x0, mepc     \n\t .endr"); tohost = CMD_INJ_CLEAR; break;
        case 69: TOGGLE_CSR(mie);              INJECT_ERR(err_id, cmd); asm volatile(".rept 50\n\t csrr x0, mie      \n\t .endr"); tohost = CMD_INJ_CLEAR; break;
        case 70: TOGGLE_CSR(mcause);           INJECT_ERR(err_id, cmd); asm volatile(".rept 50\n\t csrr x0, mcause   \n\t .endr"); tohost = CMD_INJ_CLEAR; break;
        case 71: TOGGLE_MIP();                 INJECT_ERR(err_id, cmd); asm volatile(".rept 50\n\t csrr x0, mip      \n\t .endr"); tohost = CMD_INJ_CLEAR; break;
        case 72: TOGGLE_COUNTER_CSR(minstret); INJECT_ERR(err_id, cmd); asm volatile(".rept 50\n\t csrr x0, minstret \n\t .endr"); tohost = CMD_INJ_CLEAR; break;
        case 73: TOGGLE_CSR(mcycleh);          INJECT_ERR(err_id, cmd); asm volatile(".rept 50\n\t csrr x0, mcycleh  \n\t .endr"); tohost = CMD_INJ_CLEAR; break;
        case 74: TOGGLE_CSR(minstreth);        INJECT_ERR(err_id, cmd); asm volatile(".rept 50\n\t csrr x0, minstreth\n\t .endr"); tohost = CMD_INJ_CLEAR; break;
        default: break;
    }
    asm volatile("fence\n\t .rept 20\n\t nop\n\t .endr");
}

int main(void) {
    uint32_t old_boot_count = boot_count;
    boot_count++;

    if (old_boot_count == 0) {
        printf("[Boot 0] Initial reset...\n");
        tohost = CMD_RST;
        while (1);
    }

    /* Note: mtvec, mie.MEIE (0x800), and mstatus.MIE (0x8) are configured in crt0.s before main(). */
    if (old_boot_count > 0) {
        *threshold = 1;
        gateway[2] = (1 << 1) | 0;
        clr_gateway[2] = 0;
        priority[2] = 7;
        enable[2] = 1;
    }

    uint32_t test_case = old_boot_count - 1;
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

        expected_trap = IS_GPR_MONITORED(reg) ? 1U : 0U;
        trigger_gpr_read(reg, err_id, cmd);
        expected_trap = 0U;

        if (IS_GPR_MONITORED(reg)) {
            printf("Error: [MONITORED] reg x%d (", reg);
            print_str(gpr_names[reg]);
            printf(") ");
            print_str(core);
            printf(" did not trigger DCLS trap!\n");
            error_count++;
        } else {
            non_monitored_count++;
            printf("[NON-MONITORED] x%d (", reg);
            print_str(gpr_names[reg]);
            printf(") ");
            print_str(core);
            printf(" verified: no corruption (count=%d)\n", non_monitored_count);
        }

        tohost = CMD_RST;
        while (1);
    }
    // ---------------------------------------------------------------------
    // Test cases 62 to 74: CSRs (Main and Shadow Core)
    // ---------------------------------------------------------------------
    else if (test_case < TOTAL_TEST_CASES) {
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
        expected_trap = 1U;
        trigger_csr_read(test_case, csr_tests[idx].err_id, csr_tests[idx].cmd);
        expected_trap = 0U;
        printf("Error: [MONITORED] CSR ");
        print_str(csr_tests[idx].name);
        tohost = ' ';
        print_str(csr_tests[idx].core);
        printf(" did not trigger DCLS trap!\n");
        error_count++;
        tohost = CMD_RST;
        while (1);
    }
    // ---------------------------------------------------------------------
    // Test completion / summary
    // ---------------------------------------------------------------------
    else if (test_case >= TOTAL_TEST_CASES) {
        if (dcls_trap_count != EXPECTED_DCLS_TRAPS ||
            non_monitored_count != EXPECTED_NON_MONITORED) {
            printf("Error: Count mismatch! dcls_trap_count=%d (expected %d), non_monitored_count=%d (expected %d)\n",
                   dcls_trap_count, EXPECTED_DCLS_TRAPS,
                   non_monitored_count, EXPECTED_NON_MONITORED);
            error_count++;
        }

        if (error_count > 0) {
            printf("Test FAILED with %d total errors across %d test cases!\n", error_count, TOTAL_TEST_CASES);
            printf("Total DCLS traps verified: %d, non-monitored registers verified: %d\n",
                   dcls_trap_count, non_monitored_count);
            SEND_TEST_STATUS(TEST_FAILED);
            while(1) { asm volatile("wfi"); }
        } else {
            printf("All %d register tests completed successfully with 0 errors!\n", TOTAL_TEST_CASES);
            printf("Total DCLS traps verified: %d\n", dcls_trap_count);
            printf("Total non-monitored registers verified (no false corruption detected): %d\n", non_monitored_count);
            SEND_TEST_STATUS(TEST_PASSED);
            while(1) { asm volatile("wfi"); }
        }
    }

    while(1);
}
