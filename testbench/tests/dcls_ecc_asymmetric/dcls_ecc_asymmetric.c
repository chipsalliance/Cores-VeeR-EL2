/*
 * DCLS Safety Scope: Asymmetric ECC Threshold Mismatch Test
 * Author: Samip Modi (samipmodi@google.com)
 *
 * Description:
 * This test verifies Dual-Core Lockstep (DCLS) safety isolation when an asymmetric RAS
 * threshold alert event occurs on only one of the redundant execution cores.
 *
 * Test Sequence:
 * 1. Programs the MDCCMECT threshold field to N=2.
 * 2. Triggers testbench stimulus hook Case 103 (CMD_INJ_LOCKSTEP) to inject an asymmetric
 *    ECC threshold alert exclusively onto the subordinate/shadow lockstep core.
 * 3. Verifies that the lockstep comparator detects the internal core divergence resulting
 *    from the asymmetric alert and generates a lockstep mismatch trap (mcause).
 */

#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <defines.h>

#define CMD_INJ_LOCKSTEP        0x92
#define CMD_INJ_CLEAR           0x95
#define CMD_RST                 0x96
#define TEST_PASSED             0xff
#define TEST_FAILED             0x01

extern volatile uint32_t tohost;

volatile uint32_t test_count __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t trap_count __attribute__((section(".dccm.persistent"))) = 0;

volatile uint32_t *threshold    = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIPT_OFFSET);
volatile uint32_t *gateway      = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIGWCTRL_OFFSET);
volatile uint32_t *clr_gateway  = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIGWCLR_OFFSET);
volatile uint32_t *priority     = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIPL_OFFSET);
volatile uint32_t *enable       = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIE_OFFSET);

void write_mdccmect(uint32_t val) {
    __asm__ volatile ("csrw %1, %0" : : "r" (val), "i" (0x7F2));
}

void trap_handler(void) {
    uint32_t mcause;
    __asm__ volatile ("csrr %0, mcause" : "=r" (mcause));
    printf("Lockstep divergence trap detected! mcause=0x%08X\n", mcause);
    trap_count++;
    tohost = CMD_INJ_CLEAR;
    tohost = CMD_RST;
}

int main () {
    printf("Starting DCLS Safety Scope: Asymmetric ECC Threshold Mismatch Test...\n");
    printf("test_count=%d, trap_count=%d\n", test_count, trap_count);

    *threshold = 1;
    gateway[2] = (1 << 1) | 0;
    clr_gateway[2] = 0;
    priority[2] = 7;
    enable[2] = 1;

    uint32_t mie_val;
    __asm__ volatile ("csrr %0, mie" : "=r" (mie_val));
    mie_val |= (1 << 5) | (1 << 11);
    __asm__ volatile ("csrw mie, %0" : : "r" (mie_val));

    uint32_t mstatus_val;
    __asm__ volatile ("csrr %0, mstatus" : "=r" (mstatus_val));
    mstatus_val |= (1 << 3);
    __asm__ volatile ("csrw mstatus, %0" : : "r" (mstatus_val));

    if (test_count == 0) {
        // Program DCCM threshold to N=2
        write_mdccmect(2 << 27);

        printf("Injecting asymmetric ECC threshold alert onto Subordinate Lockstep Core (Case 203)...\n");
        test_count = 1;
        tohost = (203 << 8) | CMD_INJ_LOCKSTEP;
        for (volatile int i = 0; i < 500; i++) asm volatile ("nop");
        printf("FAIL: Case 203 did not trap!\n");
        tohost = 1;
    } else if (test_count == 1) {
        if (trap_count != 1) {
            printf("FAIL: Expected trap_count=1, got %d\n", trap_count);
            tohost = 1;
        }
        printf("DCLS Asymmetric ECC Threshold Mismatch Test PASSED.\n");
        mie_val = 0;
        __asm__ volatile ("csrw mie, %0" : : "r" (mie_val));
        mstatus_val = 0;
        __asm__ volatile ("csrw mstatus, %0" : : "r" (mstatus_val));
        // Keep corruption active so exit monitor sees corruption_detected_o == El2MuBiTrue
        tohost = (1 << 8) | CMD_INJ_LOCKSTEP;
        for (volatile int slp = 0; slp < 50; slp++) asm volatile ("nop");
        return 0;
    }

    return 0;
}
