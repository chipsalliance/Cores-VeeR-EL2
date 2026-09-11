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
  #define IS_GPR_MONITORED(r) ( \
      (r) == 1  || (r) == 2  || (r) == 8  || \
      ((r) >= 10 && (r) <= 17) \
  )
#endif

volatile uint32_t boot_count __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t non_monitored_count __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t error_count __attribute__((section(".dccm.persistent"))) = 0;

volatile uint32_t *threshold    = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIPT_OFFSET);
volatile uint32_t *gateway      = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIGWCTRL_OFFSET);
volatile uint32_t *clr_gateway  = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIGWCLR_OFFSET);
volatile uint32_t *priority     = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIPL_OFFSET);
volatile uint32_t *enable       = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIE_OFFSET);

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
    if (test_case == 0) { // Target x1 (ra) Main Core
        if (IS_GPR_MONITORED(1)) {
            INJECT_ERR(221, CMD_INJ_VEER);
            asm volatile("li x1, 0x12345670\n\t.rept 1000\n\t mv x0, x1\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x1 (ra) did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(221, CMD_INJ_VEER);
            asm volatile("li x1, 0x12345670\n\t.rept 1000\n\t mv x0, x1\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x1 (ra) Main Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 1) { // Target x2 (sp) Main Core
        if (IS_GPR_MONITORED(2)) {
            INJECT_ERR(222, CMD_INJ_VEER);
            asm volatile("li x2, 0x12345670\n\t.rept 1000\n\t mv x0, x2\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x2 (sp) did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(222, CMD_INJ_VEER);
            asm volatile("li x2, 0x12345670\n\t.rept 1000\n\t mv x0, x2\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x2 (sp) Main Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 2) { // Target x3 (gp) Main Core
        if (IS_GPR_MONITORED(3)) {
            INJECT_ERR(223, CMD_INJ_VEER);
            asm volatile("li x3, 0x12345670\n\t.rept 1000\n\t mv x0, x3\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x3 (gp) did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(223, CMD_INJ_VEER);
            asm volatile("li x3, 0x12345670\n\t.rept 1000\n\t mv x0, x3\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x3 (gp) Main Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 3) { // Target x4 (tp) Main Core
        if (IS_GPR_MONITORED(4)) {
            INJECT_ERR(224, CMD_INJ_VEER);
            asm volatile("li x4, 0x12345670\n\t.rept 1000\n\t mv x0, x4\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x4 (tp) did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(224, CMD_INJ_VEER);
            asm volatile("li x4, 0x12345670\n\t.rept 1000\n\t mv x0, x4\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x4 (tp) Main Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 4) { // Target x5 (t0) Main Core
        if (IS_GPR_MONITORED(5)) {
            INJECT_ERR(225, CMD_INJ_VEER);
            asm volatile("li x5, 0x12345670\n\t.rept 1000\n\t mv x0, x5\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x5 (t0) did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(225, CMD_INJ_VEER);
            asm volatile("li x5, 0x12345670\n\t.rept 1000\n\t mv x0, x5\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x5 (t0) Main Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 5) { // Target x6 (t1) Main Core
        if (IS_GPR_MONITORED(6)) {
            INJECT_ERR(226, CMD_INJ_VEER);
            asm volatile("li x6, 0x12345670\n\t.rept 1000\n\t mv x0, x6\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x6 (t1) did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(226, CMD_INJ_VEER);
            asm volatile("li x6, 0x12345670\n\t.rept 1000\n\t mv x0, x6\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x6 (t1) Main Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 6) { // Target x7 (t2) Main Core
        if (IS_GPR_MONITORED(7)) {
            INJECT_ERR(227, CMD_INJ_VEER);
            asm volatile("li x7, 0x12345670\n\t.rept 1000\n\t mv x0, x7\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x7 (t2) did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(227, CMD_INJ_VEER);
            asm volatile("li x7, 0x12345670\n\t.rept 1000\n\t mv x0, x7\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x7 (t2) Main Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 7) { // Target x8 (s0/fp) Main Core
        if (IS_GPR_MONITORED(8)) {
            INJECT_ERR(228, CMD_INJ_VEER);
            asm volatile("li x8, 0x12345670\n\t.rept 1000\n\t mv x0, x8\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x8 (s0/fp) did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(228, CMD_INJ_VEER);
            asm volatile("li x8, 0x12345670\n\t.rept 1000\n\t mv x0, x8\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x8 (s0/fp) Main Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 8) { // Target x9 (s1) Main Core
        if (IS_GPR_MONITORED(9)) {
            INJECT_ERR(229, CMD_INJ_VEER);
            asm volatile("li x9, 0x12345670\n\t.rept 1000\n\t mv x0, x9\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x9 (s1) did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(229, CMD_INJ_VEER);
            asm volatile("li x9, 0x12345670\n\t.rept 1000\n\t mv x0, x9\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x9 (s1) Main Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 9) { // Target x10 (a0) Main Core
        if (IS_GPR_MONITORED(10)) {
            INJECT_ERR(230, CMD_INJ_VEER);
            asm volatile("li x10, 0x12345670\n\t.rept 1000\n\t mv x0, x10\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x10 (a0) did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(230, CMD_INJ_VEER);
            asm volatile("li x10, 0x12345670\n\t.rept 1000\n\t mv x0, x10\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x10 (a0) Main Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 10) { // Target x11 (a1) Main Core
        if (IS_GPR_MONITORED(11)) {
            INJECT_ERR(231, CMD_INJ_VEER);
            asm volatile("li x11, 0x12345670\n\t.rept 1000\n\t mv x0, x11\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x11 (a1) did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(231, CMD_INJ_VEER);
            asm volatile("li x11, 0x12345670\n\t.rept 1000\n\t mv x0, x11\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x11 (a1) Main Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 11) { // Target x12 (a2) Main Core
        if (IS_GPR_MONITORED(12)) {
            INJECT_ERR(232, CMD_INJ_VEER);
            asm volatile("li x12, 0x12345670\n\t.rept 1000\n\t mv x0, x12\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x12 (a2) did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(232, CMD_INJ_VEER);
            asm volatile("li x12, 0x12345670\n\t.rept 1000\n\t mv x0, x12\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x12 (a2) Main Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 12) { // Target x13 (a3) Main Core
        if (IS_GPR_MONITORED(13)) {
            INJECT_ERR(233, CMD_INJ_VEER);
            asm volatile("li x13, 0x12345670\n\t.rept 1000\n\t mv x0, x13\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x13 (a3) did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(233, CMD_INJ_VEER);
            asm volatile("li x13, 0x12345670\n\t.rept 1000\n\t mv x0, x13\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x13 (a3) Main Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 13) { // Target x14 (a4) Main Core
        if (IS_GPR_MONITORED(14)) {
            INJECT_ERR(234, CMD_INJ_VEER);
            asm volatile("li x14, 0x12345670\n\t.rept 1000\n\t mv x0, x14\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x14 (a4) did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(234, CMD_INJ_VEER);
            asm volatile("li x14, 0x12345670\n\t.rept 1000\n\t mv x0, x14\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x14 (a4) Main Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 14) { // Target x15 (a5) Main Core
        if (IS_GPR_MONITORED(15)) {
            INJECT_ERR(235, CMD_INJ_VEER);
            asm volatile("li x15, 0x12345670\n\t.rept 1000\n\t mv x0, x15\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x15 (a5) did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(235, CMD_INJ_VEER);
            asm volatile("li x15, 0x12345670\n\t.rept 1000\n\t mv x0, x15\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x15 (a5) Main Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 15) { // Target x16 (a6) Main Core
        if (IS_GPR_MONITORED(16)) {
            INJECT_ERR(236, CMD_INJ_VEER);
            asm volatile("li x16, 0x12345670\n\t.rept 1000\n\t mv x0, x16\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x16 (a6) did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(236, CMD_INJ_VEER);
            asm volatile("li x16, 0x12345670\n\t.rept 1000\n\t mv x0, x16\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x16 (a6) Main Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 16) { // Target x17 (a7) Main Core
        if (IS_GPR_MONITORED(17)) {
            INJECT_ERR(237, CMD_INJ_VEER);
            asm volatile("li x17, 0x12345670\n\t.rept 1000\n\t mv x0, x17\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x17 (a7) did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(237, CMD_INJ_VEER);
            asm volatile("li x17, 0x12345670\n\t.rept 1000\n\t mv x0, x17\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x17 (a7) Main Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 17) { // Target x18 (s2) Main Core
        if (IS_GPR_MONITORED(18)) {
            INJECT_ERR(238, CMD_INJ_VEER);
            asm volatile("li x18, 0x12345670\n\t.rept 1000\n\t mv x0, x18\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x18 (s2) did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(238, CMD_INJ_VEER);
            asm volatile("li x18, 0x12345670\n\t.rept 1000\n\t mv x0, x18\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x18 (s2) Main Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 18) { // Target x19 (s3) Main Core
        if (IS_GPR_MONITORED(19)) {
            INJECT_ERR(239, CMD_INJ_VEER);
            asm volatile("li x19, 0x12345670\n\t.rept 1000\n\t mv x0, x19\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x19 (s3) did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(239, CMD_INJ_VEER);
            asm volatile("li x19, 0x12345670\n\t.rept 1000\n\t mv x0, x19\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x19 (s3) Main Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 19) { // Target x20 (s4) Main Core
        if (IS_GPR_MONITORED(20)) {
            INJECT_ERR(240, CMD_INJ_VEER);
            asm volatile("li x20, 0x12345670\n\t.rept 1000\n\t mv x0, x20\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x20 (s4) did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(240, CMD_INJ_VEER);
            asm volatile("li x20, 0x12345670\n\t.rept 1000\n\t mv x0, x20\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x20 (s4) Main Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 20) { // Target x21 (s5) Main Core
        if (IS_GPR_MONITORED(21)) {
            INJECT_ERR(241, CMD_INJ_VEER);
            asm volatile("li x21, 0x12345670\n\t.rept 1000\n\t mv x0, x21\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x21 (s5) did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(241, CMD_INJ_VEER);
            asm volatile("li x21, 0x12345670\n\t.rept 1000\n\t mv x0, x21\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x21 (s5) Main Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 21) { // Target x22 (s6) Main Core
        if (IS_GPR_MONITORED(22)) {
            INJECT_ERR(242, CMD_INJ_VEER);
            asm volatile("li x22, 0x12345670\n\t.rept 1000\n\t mv x0, x22\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x22 (s6) did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(242, CMD_INJ_VEER);
            asm volatile("li x22, 0x12345670\n\t.rept 1000\n\t mv x0, x22\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x22 (s6) Main Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 22) { // Target x23 (s7) Main Core
        if (IS_GPR_MONITORED(23)) {
            INJECT_ERR(243, CMD_INJ_VEER);
            asm volatile("li x23, 0x12345670\n\t.rept 1000\n\t mv x0, x23\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x23 (s7) did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(243, CMD_INJ_VEER);
            asm volatile("li x23, 0x12345670\n\t.rept 1000\n\t mv x0, x23\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x23 (s7) Main Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 23) { // Target x24 (s8) Main Core
        if (IS_GPR_MONITORED(24)) {
            INJECT_ERR(244, CMD_INJ_VEER);
            asm volatile("li x24, 0x12345670\n\t.rept 1000\n\t mv x0, x24\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x24 (s8) did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(244, CMD_INJ_VEER);
            asm volatile("li x24, 0x12345670\n\t.rept 1000\n\t mv x0, x24\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x24 (s8) Main Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 24) { // Target x25 (s9) Main Core
        if (IS_GPR_MONITORED(25)) {
            INJECT_ERR(245, CMD_INJ_VEER);
            asm volatile("li x25, 0x12345670\n\t.rept 1000\n\t mv x0, x25\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x25 (s9) did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(245, CMD_INJ_VEER);
            asm volatile("li x25, 0x12345670\n\t.rept 1000\n\t mv x0, x25\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x25 (s9) Main Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 25) { // Target x26 (s10) Main Core
        if (IS_GPR_MONITORED(26)) {
            INJECT_ERR(246, CMD_INJ_VEER);
            asm volatile("li x26, 0x12345670\n\t.rept 1000\n\t mv x0, x26\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x26 (s10) did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(246, CMD_INJ_VEER);
            asm volatile("li x26, 0x12345670\n\t.rept 1000\n\t mv x0, x26\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x26 (s10) Main Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 26) { // Target x27 (s11) Main Core
        if (IS_GPR_MONITORED(27)) {
            INJECT_ERR(247, CMD_INJ_VEER);
            asm volatile("li x27, 0x12345670\n\t.rept 1000\n\t mv x0, x27\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x27 (s11) did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(247, CMD_INJ_VEER);
            asm volatile("li x27, 0x12345670\n\t.rept 1000\n\t mv x0, x27\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x27 (s11) Main Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 27) { // Target x28 (t3) Main Core
        if (IS_GPR_MONITORED(28)) {
            INJECT_ERR(248, CMD_INJ_VEER);
            asm volatile("li x28, 0x12345670\n\t.rept 1000\n\t mv x0, x28\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x28 (t3) did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(248, CMD_INJ_VEER);
            asm volatile("li x28, 0x12345670\n\t.rept 1000\n\t mv x0, x28\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x28 (t3) Main Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 28) { // Target x29 (t4) Main Core
        if (IS_GPR_MONITORED(29)) {
            INJECT_ERR(249, CMD_INJ_VEER);
            asm volatile("li x29, 0x12345670\n\t.rept 1000\n\t mv x0, x29\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x29 (t4) did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(249, CMD_INJ_VEER);
            asm volatile("li x29, 0x12345670\n\t.rept 1000\n\t mv x0, x29\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x29 (t4) Main Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 29) { // Target x30 (t5) Main Core
        if (IS_GPR_MONITORED(30)) {
            INJECT_ERR(250, CMD_INJ_VEER);
            asm volatile("li x30, 0x12345670\n\t.rept 1000\n\t mv x0, x30\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x30 (t5) did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(250, CMD_INJ_VEER);
            asm volatile("li x30, 0x12345670\n\t.rept 1000\n\t mv x0, x30\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x30 (t5) Main Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 30) { // Target x31 (t6) Main Core
        if (IS_GPR_MONITORED(31)) {
            INJECT_ERR(251, CMD_INJ_VEER);
            asm volatile("li x31, 0x12345670\n\t.rept 1000\n\t mv x0, x31\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x31 (t6) did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(251, CMD_INJ_VEER);
            asm volatile("li x31, 0x12345670\n\t.rept 1000\n\t mv x0, x31\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x31 (t6) Main Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 31) { // Target x1 (ra) Shadow Core
        if (IS_GPR_MONITORED(1)) {
            INJECT_ERR(221, CMD_INJ_LOCKSTEP);
            asm volatile("li x1, 0x12345670\n\t.rept 1000\n\t mv x0, x1\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x1 (ra) Shadow Core did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(221, CMD_INJ_LOCKSTEP);
            asm volatile("li x1, 0x12345670\n\t.rept 1000\n\t mv x0, x1\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x1 (ra) Shadow Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 32) { // Target x2 (sp) Shadow Core
        if (IS_GPR_MONITORED(2)) {
            INJECT_ERR(222, CMD_INJ_LOCKSTEP);
            asm volatile("li x2, 0x12345670\n\t.rept 1000\n\t mv x0, x2\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x2 (sp) Shadow Core did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(222, CMD_INJ_LOCKSTEP);
            asm volatile("li x2, 0x12345670\n\t.rept 1000\n\t mv x0, x2\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x2 (sp) Shadow Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 33) { // Target x3 (gp) Shadow Core
        if (IS_GPR_MONITORED(3)) {
            INJECT_ERR(223, CMD_INJ_LOCKSTEP);
            asm volatile("li x3, 0x12345670\n\t.rept 1000\n\t mv x0, x3\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x3 (gp) Shadow Core did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(223, CMD_INJ_LOCKSTEP);
            asm volatile("li x3, 0x12345670\n\t.rept 1000\n\t mv x0, x3\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x3 (gp) Shadow Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 34) { // Target x4 (tp) Shadow Core
        if (IS_GPR_MONITORED(4)) {
            INJECT_ERR(224, CMD_INJ_LOCKSTEP);
            asm volatile("li x4, 0x12345670\n\t.rept 1000\n\t mv x0, x4\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x4 (tp) Shadow Core did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(224, CMD_INJ_LOCKSTEP);
            asm volatile("li x4, 0x12345670\n\t.rept 1000\n\t mv x0, x4\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x4 (tp) Shadow Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 35) { // Target x5 (t0) Shadow Core
        if (IS_GPR_MONITORED(5)) {
            INJECT_ERR(225, CMD_INJ_LOCKSTEP);
            asm volatile("li x5, 0x12345670\n\t.rept 1000\n\t mv x0, x5\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x5 (t0) Shadow Core did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(225, CMD_INJ_LOCKSTEP);
            asm volatile("li x5, 0x12345670\n\t.rept 1000\n\t mv x0, x5\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x5 (t0) Shadow Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 36) { // Target x6 (t1) Shadow Core
        if (IS_GPR_MONITORED(6)) {
            INJECT_ERR(226, CMD_INJ_LOCKSTEP);
            asm volatile("li x6, 0x12345670\n\t.rept 1000\n\t mv x0, x6\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x6 (t1) Shadow Core did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(226, CMD_INJ_LOCKSTEP);
            asm volatile("li x6, 0x12345670\n\t.rept 1000\n\t mv x0, x6\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x6 (t1) Shadow Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 37) { // Target x7 (t2) Shadow Core
        if (IS_GPR_MONITORED(7)) {
            INJECT_ERR(227, CMD_INJ_LOCKSTEP);
            asm volatile("li x7, 0x12345670\n\t.rept 1000\n\t mv x0, x7\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x7 (t2) Shadow Core did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(227, CMD_INJ_LOCKSTEP);
            asm volatile("li x7, 0x12345670\n\t.rept 1000\n\t mv x0, x7\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x7 (t2) Shadow Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 38) { // Target x8 (s0/fp) Shadow Core
        if (IS_GPR_MONITORED(8)) {
            INJECT_ERR(228, CMD_INJ_LOCKSTEP);
            asm volatile("li x8, 0x12345670\n\t.rept 1000\n\t mv x0, x8\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x8 (s0/fp) Shadow Core did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(228, CMD_INJ_LOCKSTEP);
            asm volatile("li x8, 0x12345670\n\t.rept 1000\n\t mv x0, x8\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x8 (s0/fp) Shadow Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 39) { // Target x9 (s1) Shadow Core
        if (IS_GPR_MONITORED(9)) {
            INJECT_ERR(229, CMD_INJ_LOCKSTEP);
            asm volatile("li x9, 0x12345670\n\t.rept 1000\n\t mv x0, x9\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x9 (s1) Shadow Core did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(229, CMD_INJ_LOCKSTEP);
            asm volatile("li x9, 0x12345670\n\t.rept 1000\n\t mv x0, x9\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x9 (s1) Shadow Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 40) { // Target x10 (a0) Shadow Core
        if (IS_GPR_MONITORED(10)) {
            INJECT_ERR(230, CMD_INJ_LOCKSTEP);
            asm volatile("li x10, 0x12345670\n\t.rept 1000\n\t mv x0, x10\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x10 (a0) Shadow Core did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(230, CMD_INJ_LOCKSTEP);
            asm volatile("li x10, 0x12345670\n\t.rept 1000\n\t mv x0, x10\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x10 (a0) Shadow Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 41) { // Target x11 (a1) Shadow Core
        if (IS_GPR_MONITORED(11)) {
            INJECT_ERR(231, CMD_INJ_LOCKSTEP);
            asm volatile("li x11, 0x12345670\n\t.rept 1000\n\t mv x0, x11\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x11 (a1) Shadow Core did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(231, CMD_INJ_LOCKSTEP);
            asm volatile("li x11, 0x12345670\n\t.rept 1000\n\t mv x0, x11\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x11 (a1) Shadow Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 42) { // Target x12 (a2) Shadow Core
        if (IS_GPR_MONITORED(12)) {
            INJECT_ERR(232, CMD_INJ_LOCKSTEP);
            asm volatile("li x12, 0x12345670\n\t.rept 1000\n\t mv x0, x12\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x12 (a2) Shadow Core did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(232, CMD_INJ_LOCKSTEP);
            asm volatile("li x12, 0x12345670\n\t.rept 1000\n\t mv x0, x12\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x12 (a2) Shadow Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 43) { // Target x13 (a3) Shadow Core
        if (IS_GPR_MONITORED(13)) {
            INJECT_ERR(233, CMD_INJ_LOCKSTEP);
            asm volatile("li x13, 0x12345670\n\t.rept 1000\n\t mv x0, x13\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x13 (a3) Shadow Core did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(233, CMD_INJ_LOCKSTEP);
            asm volatile("li x13, 0x12345670\n\t.rept 1000\n\t mv x0, x13\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x13 (a3) Shadow Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 44) { // Target x14 (a4) Shadow Core
        if (IS_GPR_MONITORED(14)) {
            INJECT_ERR(234, CMD_INJ_LOCKSTEP);
            asm volatile("li x14, 0x12345670\n\t.rept 1000\n\t mv x0, x14\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x14 (a4) Shadow Core did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(234, CMD_INJ_LOCKSTEP);
            asm volatile("li x14, 0x12345670\n\t.rept 1000\n\t mv x0, x14\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x14 (a4) Shadow Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 45) { // Target x15 (a5) Shadow Core
        if (IS_GPR_MONITORED(15)) {
            INJECT_ERR(235, CMD_INJ_LOCKSTEP);
            asm volatile("li x15, 0x12345670\n\t.rept 1000\n\t mv x0, x15\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x15 (a5) Shadow Core did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(235, CMD_INJ_LOCKSTEP);
            asm volatile("li x15, 0x12345670\n\t.rept 1000\n\t mv x0, x15\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x15 (a5) Shadow Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 46) { // Target x16 (a6) Shadow Core
        if (IS_GPR_MONITORED(16)) {
            INJECT_ERR(236, CMD_INJ_LOCKSTEP);
            asm volatile("li x16, 0x12345670\n\t.rept 1000\n\t mv x0, x16\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x16 (a6) Shadow Core did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(236, CMD_INJ_LOCKSTEP);
            asm volatile("li x16, 0x12345670\n\t.rept 1000\n\t mv x0, x16\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x16 (a6) Shadow Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 47) { // Target x17 (a7) Shadow Core
        if (IS_GPR_MONITORED(17)) {
            INJECT_ERR(237, CMD_INJ_LOCKSTEP);
            asm volatile("li x17, 0x12345670\n\t.rept 1000\n\t mv x0, x17\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x17 (a7) Shadow Core did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(237, CMD_INJ_LOCKSTEP);
            asm volatile("li x17, 0x12345670\n\t.rept 1000\n\t mv x0, x17\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x17 (a7) Shadow Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 48) { // Target x18 (s2) Shadow Core
        if (IS_GPR_MONITORED(18)) {
            INJECT_ERR(238, CMD_INJ_LOCKSTEP);
            asm volatile("li x18, 0x12345670\n\t.rept 1000\n\t mv x0, x18\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x18 (s2) Shadow Core did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(238, CMD_INJ_LOCKSTEP);
            asm volatile("li x18, 0x12345670\n\t.rept 1000\n\t mv x0, x18\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x18 (s2) Shadow Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 49) { // Target x19 (s3) Shadow Core
        if (IS_GPR_MONITORED(19)) {
            INJECT_ERR(239, CMD_INJ_LOCKSTEP);
            asm volatile("li x19, 0x12345670\n\t.rept 1000\n\t mv x0, x19\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x19 (s3) Shadow Core did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(239, CMD_INJ_LOCKSTEP);
            asm volatile("li x19, 0x12345670\n\t.rept 1000\n\t mv x0, x19\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x19 (s3) Shadow Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 50) { // Target x20 (s4) Shadow Core
        if (IS_GPR_MONITORED(20)) {
            INJECT_ERR(240, CMD_INJ_LOCKSTEP);
            asm volatile("li x20, 0x12345670\n\t.rept 1000\n\t mv x0, x20\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x20 (s4) Shadow Core did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(240, CMD_INJ_LOCKSTEP);
            asm volatile("li x20, 0x12345670\n\t.rept 1000\n\t mv x0, x20\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x20 (s4) Shadow Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 51) { // Target x21 (s5) Shadow Core
        if (IS_GPR_MONITORED(21)) {
            INJECT_ERR(241, CMD_INJ_LOCKSTEP);
            asm volatile("li x21, 0x12345670\n\t.rept 1000\n\t mv x0, x21\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x21 (s5) Shadow Core did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(241, CMD_INJ_LOCKSTEP);
            asm volatile("li x21, 0x12345670\n\t.rept 1000\n\t mv x0, x21\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x21 (s5) Shadow Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 52) { // Target x22 (s6) Shadow Core
        if (IS_GPR_MONITORED(22)) {
            INJECT_ERR(242, CMD_INJ_LOCKSTEP);
            asm volatile("li x22, 0x12345670\n\t.rept 1000\n\t mv x0, x22\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x22 (s6) Shadow Core did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(242, CMD_INJ_LOCKSTEP);
            asm volatile("li x22, 0x12345670\n\t.rept 1000\n\t mv x0, x22\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x22 (s6) Shadow Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 53) { // Target x23 (s7) Shadow Core
        if (IS_GPR_MONITORED(23)) {
            INJECT_ERR(243, CMD_INJ_LOCKSTEP);
            asm volatile("li x23, 0x12345670\n\t.rept 1000\n\t mv x0, x23\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x23 (s7) Shadow Core did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(243, CMD_INJ_LOCKSTEP);
            asm volatile("li x23, 0x12345670\n\t.rept 1000\n\t mv x0, x23\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x23 (s7) Shadow Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 54) { // Target x24 (s8) Shadow Core
        if (IS_GPR_MONITORED(24)) {
            INJECT_ERR(244, CMD_INJ_LOCKSTEP);
            asm volatile("li x24, 0x12345670\n\t.rept 1000\n\t mv x0, x24\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x24 (s8) Shadow Core did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(244, CMD_INJ_LOCKSTEP);
            asm volatile("li x24, 0x12345670\n\t.rept 1000\n\t mv x0, x24\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x24 (s8) Shadow Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 55) { // Target x25 (s9) Shadow Core
        if (IS_GPR_MONITORED(25)) {
            INJECT_ERR(245, CMD_INJ_LOCKSTEP);
            asm volatile("li x25, 0x12345670\n\t.rept 1000\n\t mv x0, x25\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x25 (s9) Shadow Core did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(245, CMD_INJ_LOCKSTEP);
            asm volatile("li x25, 0x12345670\n\t.rept 1000\n\t mv x0, x25\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x25 (s9) Shadow Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 56) { // Target x26 (s10) Shadow Core
        if (IS_GPR_MONITORED(26)) {
            INJECT_ERR(246, CMD_INJ_LOCKSTEP);
            asm volatile("li x26, 0x12345670\n\t.rept 1000\n\t mv x0, x26\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x26 (s10) Shadow Core did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(246, CMD_INJ_LOCKSTEP);
            asm volatile("li x26, 0x12345670\n\t.rept 1000\n\t mv x0, x26\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x26 (s10) Shadow Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 57) { // Target x27 (s11) Shadow Core
        if (IS_GPR_MONITORED(27)) {
            INJECT_ERR(247, CMD_INJ_LOCKSTEP);
            asm volatile("li x27, 0x12345670\n\t.rept 1000\n\t mv x0, x27\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x27 (s11) Shadow Core did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(247, CMD_INJ_LOCKSTEP);
            asm volatile("li x27, 0x12345670\n\t.rept 1000\n\t mv x0, x27\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x27 (s11) Shadow Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 58) { // Target x28 (t3) Shadow Core
        if (IS_GPR_MONITORED(28)) {
            INJECT_ERR(248, CMD_INJ_LOCKSTEP);
            asm volatile("li x28, 0x12345670\n\t.rept 1000\n\t mv x0, x28\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x28 (t3) Shadow Core did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(248, CMD_INJ_LOCKSTEP);
            asm volatile("li x28, 0x12345670\n\t.rept 1000\n\t mv x0, x28\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x28 (t3) Shadow Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 59) { // Target x29 (t4) Shadow Core
        if (IS_GPR_MONITORED(29)) {
            INJECT_ERR(249, CMD_INJ_LOCKSTEP);
            asm volatile("li x29, 0x12345670\n\t.rept 1000\n\t mv x0, x29\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x29 (t4) Shadow Core did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(249, CMD_INJ_LOCKSTEP);
            asm volatile("li x29, 0x12345670\n\t.rept 1000\n\t mv x0, x29\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x29 (t4) Shadow Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 60) { // Target x30 (t5) Shadow Core
        if (IS_GPR_MONITORED(30)) {
            INJECT_ERR(250, CMD_INJ_LOCKSTEP);
            asm volatile("li x30, 0x12345670\n\t.rept 1000\n\t mv x0, x30\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x30 (t5) Shadow Core did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(250, CMD_INJ_LOCKSTEP);
            asm volatile("li x30, 0x12345670\n\t.rept 1000\n\t mv x0, x30\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x30 (t5) Shadow Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 61) { // Target x31 (t6) Shadow Core
        if (IS_GPR_MONITORED(31)) {
            INJECT_ERR(251, CMD_INJ_LOCKSTEP);
            asm volatile("li x31, 0x12345670\n\t.rept 1000\n\t mv x0, x31\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            printf("Error: [MONITORED] reg x31 (t6) Shadow Core did not trigger DCLS trap!\n");
            error_count++;
            tohost = CMD_RST;
            while (1);
        } else {
            INJECT_ERR(251, CMD_INJ_LOCKSTEP);
            asm volatile("li x31, 0x12345670\n\t.rept 1000\n\t mv x0, x31\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            non_monitored_count++;
            printf("[NON-MONITORED] x31 (t6) Shadow Core verified: no corruption (count=%d)\n", non_monitored_count);
            tohost = CMD_RST;
            while (1);
        }
    } else
    if (test_case == 62) { // Target mscratch Main Core
        INJECT_ERR(252, CMD_INJ_VEER);
        asm volatile(".rept 1000\n\t csrr x0, mscratch\n\t .endr");
        tohost = CMD_INJ_CLEAR;
        printf("Error: [MONITORED] CSR mscratch did not trigger DCLS trap!\n");
        error_count++;
        tohost = CMD_RST;
        while (1);
    } else
    if (test_case == 63) { // Target mstatus Main Core
        INJECT_ERR(253, CMD_INJ_VEER);
        asm volatile(".rept 1000\n\t csrr x0, mstatus\n\t .endr");
        tohost = CMD_INJ_CLEAR;
        printf("Error: [MONITORED] CSR mstatus did not trigger DCLS trap!\n");
        error_count++;
        tohost = CMD_RST;
        while (1);
    } else
    if (test_case == 64) { // Target mtvec Main Core
        INJECT_ERR(254, CMD_INJ_VEER);
        asm volatile(".rept 1000\n\t csrr x0, mtvec\n\t .endr");
        tohost = CMD_INJ_CLEAR;
        printf("Error: [MONITORED] CSR mtvec did not trigger DCLS trap!\n");
        error_count++;
        tohost = CMD_RST;
        while (1);
    } else
    if (test_case == 65) { // Target mtval Main Core
        INJECT_ERR(255, CMD_INJ_VEER);
        asm volatile(".rept 1000\n\t csrr x0, mtval\n\t .endr");
        tohost = CMD_INJ_CLEAR;
        printf("Error: [MONITORED] CSR mtval did not trigger DCLS trap!\n");
        error_count++;
        tohost = CMD_RST;
        while (1);
    } else
    if (test_case == 66) { // Target mcycle Main Core
        INJECT_ERR(195, CMD_INJ_VEER);
        asm volatile(".rept 1000\n\t csrr x0, mcycle\n\t .endr");
        tohost = CMD_INJ_CLEAR;
        printf("Error: [MONITORED] CSR mcycle did not trigger DCLS trap!\n");
        error_count++;
        tohost = CMD_RST;
        while (1);
    } else
    if (test_case == 67) { // Target mrac Main Core
        INJECT_ERR(196, CMD_INJ_VEER);
        asm volatile(".rept 1000\n\t csrr x0, 0x7c0\n\t .endr");
        tohost = CMD_INJ_CLEAR;
        printf("Error: [MONITORED] CSR mrac did not trigger DCLS trap!\n");
        error_count++;
        tohost = CMD_RST;
        while (1);
    } else
    if (test_case == 68) { // Target mepc Shadow Core
        INJECT_ERR(252, CMD_INJ_LOCKSTEP);
        asm volatile(".rept 1000\n\t csrr x0, mepc\n\t .endr");
        tohost = CMD_INJ_CLEAR;
        printf("Error: [MONITORED] CSR mepc Shadow Core did not trigger DCLS trap!\n");
        error_count++;
        tohost = CMD_RST;
        while (1);
    } else
    if (test_case == 69) { // Target mie Shadow Core
        INJECT_ERR(253, CMD_INJ_LOCKSTEP);
        asm volatile(".rept 1000\n\t csrr x0, mie\n\t .endr");
        tohost = CMD_INJ_CLEAR;
        printf("Error: [MONITORED] CSR mie Shadow Core did not trigger DCLS trap!\n");
        error_count++;
        tohost = CMD_RST;
        while (1);
    } else
    if (test_case == 70) { // Target mcause Shadow Core
        INJECT_ERR(254, CMD_INJ_LOCKSTEP);
        asm volatile(".rept 1000\n\t csrr x0, mcause\n\t .endr");
        tohost = CMD_INJ_CLEAR;
        printf("Error: [MONITORED] CSR mcause Shadow Core did not trigger DCLS trap!\n");
        error_count++;
        tohost = CMD_RST;
        while (1);
    } else
    if (test_case == 71) { // Target mip Shadow Core
        INJECT_ERR(255, CMD_INJ_LOCKSTEP);
        asm volatile(".rept 1000\n\t csrr x0, mip\n\t .endr");
        tohost = CMD_INJ_CLEAR;
        printf("Error: [MONITORED] CSR mip Shadow Core did not trigger DCLS trap!\n");
        error_count++;
        tohost = CMD_RST;
        while (1);
    } else
    if (test_case == 72) { // Target minstret Shadow Core
        INJECT_ERR(195, CMD_INJ_LOCKSTEP);
        asm volatile(".rept 1000\n\t csrr x0, minstret\n\t .endr");
        tohost = CMD_INJ_CLEAR;
        printf("Error: [MONITORED] CSR minstret Shadow Core did not trigger DCLS trap!\n");
        error_count++;
        tohost = CMD_RST;
        while (1);
    } else
    if (test_case >= 73) {
        if (error_count > 0) {
            printf("Test FAILED with %d total errors across 73 test cases!\n", error_count);
            printf("Total non-monitored registers verified: %d\n", non_monitored_count);
            SEND_TEST_STATUS(TEST_FAILED);
            while(1) { asm volatile("wfi"); }
        } else {
            printf("All 73 register tests completed successfully with 0 errors!\n");
            printf("Total false corruption No. of non-monitored registers verified : %d\n", non_monitored_count);
            SEND_TEST_STATUS(TEST_PASSED);
            while(1) { asm volatile("wfi"); }
        }
    } else {
        tohost = CMD_INJ_CLEAR;
        printf("Error: Test case %d timed out without trap\n", test_case);
        error_count++;
        tohost = CMD_RST;
        while(1);
    }

    while(1);
}
