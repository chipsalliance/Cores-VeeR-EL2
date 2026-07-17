/*
 * dcls_monitored_regs.c
 *
 * Verifies the Dual-Core Lock-Step (DCLS) corruption detection specifically
 * for the tracked Monitored Registers (GPRs and CSRs) on both the Main and
 * Shadow cores as outlined in Section 5.1.2.
 *
 * Rewritten to use the reset-loop style (similar to dcls.c) using boot_count.
 *
 * Author: navadiya
 */

#include "dcls_monitored_regs.h"
#include <stdio.h>
#include <defines.h>
#define CMD_RST              0x96
#define CLEAR_FAULT_CMD      0x95

volatile uint32_t boot_count __attribute__((section(".dccm.persistent"))) = 0;

volatile uint32_t *threshold    = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIPT_OFFSET);
volatile uint32_t *gateway      = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIGWCTRL_OFFSET);
volatile uint32_t *clr_gateway  = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIGWCLR_OFFSET);
volatile uint32_t *priority     = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIPL_OFFSET);
volatile uint32_t *enable       = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIE_OFFSET);

#define read_csr(csr) ({ \
    unsigned long res; \
    asm volatile ("csrr %0, " #csr : "=r"(res)); \
    res; \
})

#define write_csr(csr, val) { \
    unsigned long __unshielded_val = (val); \
    unsigned long __shielded_val = __unshielded_val; \
    asm volatile ("" : "+r"(__shielded_val)); \
    asm volatile ("csrw " #csr ", %0" : : "r"(__shielded_val)); \
}

#define read_mcycle() ({ \
    uint32_t _mcycle; \
    asm volatile ("csrr %0, mcycle" : "=r"(_mcycle)); \
    _mcycle; \
})

/**
 * Trap handler. Clears the fault and resets the CPU to run the next test.
 * Relies on the assembly wrapper in crt0.s.
 */
void trap_handler(void) {
    // Clear the fault injection source in the testbench.
    tohost = CMD_INJ_CLEAR;
    asm volatile(".rept 10\n\t nop\n\t .endr");
    
    // Trigger hardware reset via mailbox
    tohost = CMD_RST;
    
    while (1); // Wait for reset
}

int main(void) {
    uint32_t old_boot_count = boot_count;
    boot_count++;

    if (old_boot_count == 0) {
        printf("[%u cycles] Boot 0: Initial reset to clear debug mode latch...\n", read_mcycle());
        tohost = CMD_RST;
        while (1);
    }

    if (old_boot_count > 0) {
        // Configure PIC for DCLS interrupts (extintsrc_req[2])
        *threshold = 1;
        gateway[2] = (1 << 1) | 0;
        clr_gateway[2] = 0;
        priority[2] = 7;
        enable[2] = 1;
    }

    uint32_t readback_val;
    uint32_t saved_reg;
    uint32_t test_val;

    uint32_t test_case = old_boot_count - 1;
    printf("[%u cycles] Boot %d: Starting monitored register test case %d...\n", read_mcycle(), old_boot_count, test_case);

    switch (test_case) {
        // ---------------------------------------------------------------------
        // 1. Monitored GPR Corruption - MAIN CORE
        // ---------------------------------------------------------------------
        case 0: // Target x10 (a0)
            printf("[%u cycles] Injecting fault into MAIN CORE GPR x10 (a0)\n", read_mcycle());
            asm volatile("mv %0, a0" : "=r"(saved_reg));
            asm volatile("li a0, 0x11111111");
            INJECT_ERR(100, CMD_INJ_VEER);
            asm volatile(".rept 100\n\t mv x0, a0\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            asm volatile("mv %0, a0" : "=r" (readback_val));
            asm volatile("mv a0, %0" :: "r"(saved_reg));
            break;
            
        case 1: // Target x1 (ra)
            printf("[%u cycles] Injecting fault into MAIN CORE GPR x1 (ra)\n", read_mcycle());
            asm volatile("mv %0, ra" : "=r"(saved_reg));
            asm volatile("li ra, 0x12345678");
            INJECT_ERR(101, CMD_INJ_VEER);
            asm volatile(".rept 100\n\t mv x0, ra\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            asm volatile("mv %0, ra" : "=r" (readback_val));
            asm volatile("mv ra, %0" :: "r"(saved_reg));
            break;

        case 2: // Target x12 (a2)
            printf("[%u cycles] Injecting fault into MAIN CORE GPR x12 (a2)\n", read_mcycle());
            asm volatile("mv %0, a2" : "=r"(saved_reg));
            asm volatile("li a2, 0x22222222");
            INJECT_ERR(102, CMD_INJ_VEER);
            asm volatile(".rept 100\n\t mv x0, a2\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            asm volatile("mv %0, a2" : "=r" (readback_val));
            asm volatile("mv a2, %0" :: "r"(saved_reg));
            break;

        case 3: // Target x14 (a4)
            printf("[%u cycles] Injecting fault into MAIN CORE GPR x14 (a4)\n", read_mcycle());
            asm volatile("mv %0, a4" : "=r"(saved_reg));
            asm volatile("li a4, 0x44444444");
            INJECT_ERR(103, CMD_INJ_VEER);
            asm volatile(".rept 100\n\t mv x0, a4\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            asm volatile("mv %0, a4" : "=r" (readback_val));
            asm volatile("mv a4, %0" :: "r"(saved_reg));
            break;

        case 4: // Target x16 (a6)
            printf("[%u cycles] Injecting fault into MAIN CORE GPR x16 (a6)\n", read_mcycle());
            asm volatile("mv %0, a6" : "=r"(saved_reg));
            asm volatile("li a6, 0x66666666");
            INJECT_ERR(104, CMD_INJ_VEER);
            asm volatile(".rept 100\n\t mv x0, a6\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            asm volatile("mv %0, a6" : "=r" (readback_val));
            asm volatile("mv a6, %0" :: "r"(saved_reg));
            break;

        // ---------------------------------------------------------------------
        // 2. Monitored GPR Corruption - SHADOW CORE
        // ---------------------------------------------------------------------
        case 5: // Target x11 (a1)
            printf("[%u cycles] Injecting fault into SHADOW CORE GPR x11 (a1)\n", read_mcycle());
            asm volatile("mv %0, a1" : "=r"(saved_reg));
            asm volatile("li a1, 0x22222222");
            INJECT_ERR(105, CMD_INJ_LOCKSTEP);
            asm volatile(".rept 100\n\t mv x0, a1\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            asm volatile("mv %0, a1" : "=r" (readback_val));
            asm volatile("mv a1, %0" :: "r"(saved_reg));
            break;

        case 6: // Target x13 (a3)
            printf("[%u cycles] Injecting fault into SHADOW CORE GPR x13 (a3)\n", read_mcycle());
            asm volatile("mv %0, a3" : "=r"(saved_reg));
            asm volatile("li a3, 0x33333333");
            INJECT_ERR(106, CMD_INJ_LOCKSTEP);
            asm volatile(".rept 100\n\t mv x0, a3\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            asm volatile("mv %0, a3" : "=r" (readback_val));
            asm volatile("mv a3, %0" :: "r"(saved_reg));
            break;

        case 7: // Target x15 (a5)
            printf("[%u cycles] Injecting fault into SHADOW CORE GPR x15 (a5)\n", read_mcycle());
            asm volatile("mv %0, a5" : "=r"(saved_reg));
            asm volatile("li a5, 0x55555555");
            INJECT_ERR(107, CMD_INJ_LOCKSTEP);
            asm volatile(".rept 100\n\t mv x0, a5\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            asm volatile("mv %0, a5" : "=r" (readback_val));
            asm volatile("mv a5, %0" :: "r"(saved_reg));
            break;

        case 8: // Target x17 (a7)
            printf("[%u cycles] Injecting fault into SHADOW CORE GPR x17 (a7)\n", read_mcycle());
            asm volatile("mv %0, a7" : "=r"(saved_reg));
            asm volatile("li a7, 0x77777777");
            INJECT_ERR(108, CMD_INJ_LOCKSTEP);
            asm volatile(".rept 100\n\t mv x0, a7\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            asm volatile("mv %0, a7" : "=r" (readback_val));
            asm volatile("mv a7, %0" :: "r"(saved_reg));
            break;

        // ---------------------------------------------------------------------
        // 3. Monitored CSR Corruption - MAIN CORE
        // ---------------------------------------------------------------------
        case 9: // Target mscratch (0x340)
            printf("[%u cycles] Injecting fault into MAIN CORE CSR mscratch (0x340)\n", read_mcycle());
            test_val = 0xAAAAAAAA;
            asm volatile("csrw mscratch, %0" :: "r"(test_val));
            INJECT_ERR(109, CMD_INJ_VEER);
            asm volatile(".rept 100\n\t csrr x0, mscratch\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            asm volatile("csrr %0, mscratch" : "=r"(readback_val));
            break;

        case 10: // Target mstatus (0x300)
            printf("[%u cycles] Injecting fault into MAIN CORE CSR mstatus (0x300)\n", read_mcycle());
            INJECT_ERR(110, CMD_INJ_VEER);
            asm volatile(".rept 100\n\t csrr x0, mstatus\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            asm volatile("csrr %0, mstatus" : "=r"(readback_val));
            break;

        case 11: // Target mtvec (0x305)
            printf("[%u cycles] Injecting fault into MAIN CORE CSR mtvec (0x305)\n", read_mcycle());
            INJECT_ERR(111, CMD_INJ_VEER);
            asm volatile(".rept 100\n\t csrr x0, mtvec\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            asm volatile("csrr %0, mtvec" : "=r"(readback_val));
            break;

        case 12: // Target mtval (0x343)
            printf("[%u cycles] Injecting fault into MAIN CORE CSR mtval (0x343)\n", read_mcycle());
            INJECT_ERR(112, CMD_INJ_VEER);
            asm volatile(".rept 100\n\t csrr x0, mtval\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            asm volatile("csrr %0, mtval" : "=r"(readback_val));
            break;

        case 13: // Target mcycle (0xB00)
            printf("[%u cycles] Injecting fault into MAIN CORE CSR mcycle (0xB00)\n", read_mcycle());
            INJECT_ERR(113, CMD_INJ_VEER);
            asm volatile(".rept 100\n\t csrr x0, mcycle\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            asm volatile("csrr %0, mcycle" : "=r"(readback_val));
            break;

        case 14: // Target mrac (0x7C0)
            printf("[%u cycles] Injecting fault into MAIN CORE CSR mrac (0x7C0)\n", read_mcycle());
            INJECT_ERR(114, CMD_INJ_VEER);
            asm volatile(".rept 100\n\t csrr x0, 0x7c0\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            asm volatile("csrr %0, 0x7c0" : "=r"(readback_val));
            break;

        // ---------------------------------------------------------------------
        // 4. Monitored CSR Corruption - SHADOW CORE
        // ---------------------------------------------------------------------
        case 15: // Target mepc (0x341)
            printf("[%u cycles] Injecting fault into SHADOW CORE CSR mepc (0x341)\n", read_mcycle());
            test_val = 0x55555555;
            asm volatile("csrw mepc, %0" :: "r"(test_val));
            INJECT_ERR(115, CMD_INJ_LOCKSTEP);
            asm volatile(".rept 100\n\t csrr x0, mepc\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            asm volatile("csrr %0, mepc" : "=r"(readback_val));
            break;

        case 16: // Target mie (0x304)
            printf("[%u cycles] Injecting fault into SHADOW CORE CSR mie (0x304)\n", read_mcycle());
            INJECT_ERR(116, CMD_INJ_LOCKSTEP);
            asm volatile(".rept 100\n\t csrr x0, mie\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            asm volatile("csrr %0, mie" : "=r"(readback_val));
            break;

        case 17: // Target mcause (0x342)
            printf("[%u cycles] Injecting fault into SHADOW CORE CSR mcause (0x342)\n", read_mcycle());
            INJECT_ERR(117, CMD_INJ_LOCKSTEP);
            asm volatile(".rept 100\n\t csrr x0, mcause\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            asm volatile("csrr %0, mcause" : "=r"(readback_val));
            break;

        case 18: // Target mip (0x344)
            printf("[%u cycles] Injecting fault into SHADOW CORE CSR mip (0x344)\n", read_mcycle());
            INJECT_ERR(118, CMD_INJ_LOCKSTEP);
            asm volatile(".rept 100\n\t csrr x0, mip\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            asm volatile("csrr %0, mip" : "=r"(readback_val));
            break;

        case 19: // Target minstret (0xB02)
            printf("[%u cycles] Injecting fault into SHADOW CORE CSR minstret (0xB02)\n", read_mcycle());
            INJECT_ERR(119, CMD_INJ_LOCKSTEP);
            asm volatile(".rept 100\n\t csrr x0, minstret\n\t .endr");
            tohost = CMD_INJ_CLEAR;
            asm volatile("csrr %0, minstret" : "=r"(readback_val));
            break;

        default:
            // All tests passed!
            printf("All monitored registers tests passed!\n");
            SEND_TEST_STATUS(TEST_PASSED);
            while(1) { asm volatile("wfi"); }
    }

    // If we reach here, the test did not trigger a trap (failure)
    printf("Test failed: No trap triggered for boot_count=%d\n", old_boot_count);
    SEND_TEST_STATUS(TEST_FAILED);
    return 0;
}
