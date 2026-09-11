#include "dcls_regfile_read.h"
#include <stdio.h>
#include <defines.h>

/*
 * Dynamic DCLS GPR Monitoring Configuration:
 * - When RV_LOCKSTEP_REGFILE_READ_ENABLE == 1: ALL 31 GPRs are monitored on read.
 * - When RV_LOCKSTEP_REGFILE_READ_ENABLE == 0: Only ra, sp, fp, and a0..a7 are monitored (11 GPRs).
 */
#if defined(RV_LOCKSTEP_REGFILE_READ_ENABLE) && (RV_LOCKSTEP_REGFILE_READ_ENABLE == 1)
  #define IS_GPR_MONITORED(r) (1)
#else
  #define IS_GPR_MONITORED(r) (       (r) == 1  || (r) == 2  || (r) == 8  ||       ((r) >= 10 && (r) <= 17)   )
#endif

volatile uint32_t boot_count __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t non_monitored_count __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t error_count __attribute__((section(".dccm.persistent"))) = 0;

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
    printf("trap! mstatus=0x%08X, mcause=0x%08X, mepc=0x%08X\n", mstatus, mcause, mepc);
    tohost = CMD_RST;
    while (1);
}

#define CASE_GPR(n)     case n: {         register uint32_t saved_val;         asm volatile("mv %0, x" #n : "=r"(saved_val));         INJECT_ERR(err_id, cmd);         asm volatile(             "li x" #n ", 0x12345670\n\t"             ".rept 50\n\t"             "mv x0, x" #n "\n\t"             ".endr"         );         tohost = CMD_INJ_CLEAR;         asm volatile("mv x" #n ", %0" :: "r"(saved_val));         break;     }

static void __attribute__((noinline)) trigger_gpr_read(uint32_t reg, uint32_t err_id, uint32_t cmd) {
    switch (reg) {
        case 1:
            INJECT_ERR(err_id, cmd);
            asm volatile("li x1, 0x12345670\n\t.rept 50\n\t mv x0, x1\n\t.endr");
            tohost = CMD_INJ_CLEAR;
            break;
        case 2:
            INJECT_ERR(err_id, cmd);
            asm volatile("li x2, 0x12345670\n\t.rept 50\n\t mv x0, x2\n\t.endr");
            tohost = CMD_INJ_CLEAR;
            break;
        CASE_GPR(3);
        CASE_GPR(4);
        CASE_GPR(5);
        CASE_GPR(6);
        CASE_GPR(7);
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

static void __attribute__((noinline)) trigger_csr_read(uint32_t test_case, uint16_t err_id, uint8_t cmd) {
    switch (test_case) {
        case 62: INJECT_ERR(err_id, cmd); asm volatile(".rept 50\n\t csrr x0, mscratch\n\t .endr"); tohost = CMD_INJ_CLEAR; break;
        case 63: INJECT_ERR(err_id, cmd); asm volatile(".rept 50\n\t csrr x0, mstatus \n\t .endr"); tohost = CMD_INJ_CLEAR; break;
        case 64: INJECT_ERR(err_id, cmd); asm volatile(".rept 50\n\t csrr x0, mtvec   \n\t .endr"); tohost = CMD_INJ_CLEAR; break;
        case 65: INJECT_ERR(err_id, cmd); asm volatile(".rept 50\n\t csrr x0, mtval   \n\t .endr"); tohost = CMD_INJ_CLEAR; break;
        case 66: INJECT_ERR(err_id, cmd); asm volatile(".rept 50\n\t csrr x0, mcycle  \n\t .endr"); tohost = CMD_INJ_CLEAR; break;
        case 67: INJECT_ERR(err_id, cmd); asm volatile(".rept 50\n\t csrr x0, 0x7c0   \n\t .endr"); tohost = CMD_INJ_CLEAR; break;
        case 68: INJECT_ERR(err_id, cmd); asm volatile(".rept 50\n\t csrr x0, mepc    \n\t .endr"); tohost = CMD_INJ_CLEAR; break;
        case 69: INJECT_ERR(err_id, cmd); asm volatile(".rept 50\n\t csrr x0, mie     \n\t .endr"); tohost = CMD_INJ_CLEAR; break;
        case 70: INJECT_ERR(err_id, cmd); asm volatile(".rept 50\n\t csrr x0, mcause  \n\t .endr"); tohost = CMD_INJ_CLEAR; break;
        case 71: INJECT_ERR(err_id, cmd); asm volatile(".rept 50\n\t csrr x0, mip     \n\t .endr"); tohost = CMD_INJ_CLEAR; break;
        case 72: INJECT_ERR(err_id, cmd); asm volatile(".rept 50\n\t csrr x0, minstret\n\t .endr"); tohost = CMD_INJ_CLEAR; break;
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

        asm volatile(
            "li t0, 0x800\n\t"
            "csrs mie, t0\n\t"
            "li t0, 0x8\n\t"
            "csrs mstatus, t0\n\t"
            ::: "t0"
        );
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

        trigger_gpr_read(reg, err_id, cmd);

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
    // Test cases 62 to 72: CSRs (Main and Shadow Core)
    // ---------------------------------------------------------------------
    else if (test_case <= 72) {
        static const struct {
            const char *name;
            uint16_t err_id;
            uint8_t cmd;
            const char *core;
        } csr_tests[] = {
            {"mscratch", 252, CMD_INJ_VEER,     "Main Core"},   // 62
            {"mstatus",  253, CMD_INJ_VEER,     "Main Core"},   // 63
            {"mtvec",    254, CMD_INJ_VEER,     "Main Core"},   // 64
            {"mtval",    255, CMD_INJ_VEER,     "Main Core"},   // 65
            {"mcycle",   195, CMD_INJ_VEER,     "Main Core"},   // 66
            {"mrac",     196, CMD_INJ_VEER,     "Main Core"},   // 67
            {"mepc",     252, CMD_INJ_LOCKSTEP, "Shadow Core"}, // 68
            {"mie",      253, CMD_INJ_LOCKSTEP, "Shadow Core"}, // 69
            {"mcause",   254, CMD_INJ_LOCKSTEP, "Shadow Core"}, // 70
            {"mip",      255, CMD_INJ_LOCKSTEP, "Shadow Core"}, // 71
            {"minstret", 195, CMD_INJ_LOCKSTEP, "Shadow Core"}  // 72
        };
        int idx = test_case - 62;
        trigger_csr_read(test_case, csr_tests[idx].err_id, csr_tests[idx].cmd);
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
    else if (test_case >= 73) {
        if (error_count > 0) {
            printf("Test FAILED with %d total errors across 73 test cases!\n", error_count);
            printf("Total non-monitored registers verified: %d\n", non_monitored_count);
            SEND_TEST_STATUS(TEST_FAILED);
            while(1) { asm volatile("wfi"); }
        } else {
            printf("All 73 register tests completed successfully with 0 errors!\n");
            printf("Total non-monitored registers verified (no false corruption detected): %d\n", non_monitored_count);
            SEND_TEST_STATUS(TEST_PASSED);
            while(1) { asm volatile("wfi"); }
        }
    }

    while(1);
}
