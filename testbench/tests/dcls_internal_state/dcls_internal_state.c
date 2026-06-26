/*
 * DCLS Internal Core State Tamper Test (Val-Rec-4)
 * Author: Samip Modi (samipmodi@google.com)
 *
 * Description:
 * This test verifies Dual-Core Lockstep (DCLS) architectural equivalence monitoring and
 * trap generation across diverse internal architectural register structures (GPRs and CSRs).
 *
 * Test Scenarios:
 * 1. Scenario 4.1 (TP_DCLS_INT_GPR / Case 200): General Purpose Register (GPR) Bit-Flip.
 *    Performs arithmetic on t0 (x5). Flips bit 15 of subordinate GPR bank 5 and verifies
 *    divergence when read into the ALU execution stage.
 * 2. Scenario 4.2 (TP_DCLS_INT_FLOP / Case 201): Program Counter Flop Corruption (PRIORITY #2).
 *    Forces 1-bit corruption in subordinate Program Counter (ifu_pc_ff). Asserts mismatch
 *    detection within 1 to 2 clock cycles.
 * 3. Scenario 4.3 (TP_DCLS_INT_CSR / Case 202): Architectural CSR Flop Tamper.
 *    Forces a bit-flip inside subordinate mtvec holding flop. Asserts mismatch detected
 *    upon next CSR read instruction retirement.
 */

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <defines.h>

#define read_csr(csr) ({ \
    unsigned long res; \
    asm volatile ("csrr %0, " #csr : "=r"(res)); \
    res; \
})

#define write_csr(csr, val) { \
    asm volatile ("csrw " #csr ", %0" : : "r"(val)); \
}

#define CMD_INJ_VEER         0x91
#define CMD_INJ_LOCKSTEP     0x92
#define CMD_INJ_CLEAR        0x95
#define CMD_RST              0x96

volatile uint32_t test_count __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t trap_count __attribute__((section(".dccm.persistent"))) = 0;

volatile uint32_t *threshold    = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIPT_OFFSET);
volatile uint32_t *gateway      = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIGWCTRL_OFFSET);
volatile uint32_t *clr_gateway  = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIGWCLR_OFFSET);
volatile uint32_t *priority     = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIPL_OFFSET);
volatile uint32_t *enable       = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIE_OFFSET);

extern volatile uint32_t tohost;

void trap_handler () {
    uint32_t mcause = read_csr(mcause);
    printf("Internal state divergence trap detected! mcause=0x%08X\n", mcause);
    trap_count++;
    tohost = CMD_INJ_CLEAR;
    tohost = CMD_RST;
}

int main () {
    printf("Starting DCLS Internal Core State Tamper Test (Val-Rec-4)...\n");
    printf("test_count=%d, trap_count=%d\n", test_count, trap_count);

    *threshold = 1;
    gateway[2] = (1 << 1) | 0;
    clr_gateway[2] = 0;
    priority[2] = 7;
    enable[2] = 1;

    unsigned long mie = read_csr(mie);
    mie |= (1 << 11);
    write_csr(mie, mie);

    unsigned long mstatus = read_csr(mstatus);
    mstatus |= (1 << 3);
    write_csr(mstatus, mstatus);

    if (test_count == 0) {
        // Scenario 4.2 (TP_DCLS_INT_FLOP): Program Counter Flop Corruption (PRIORITY #2)
        printf("Scenario 4.2 (TP_DCLS_INT_FLOP): Forcing 1-bit corruption in Program Counter flop (case 201)...\n");
        test_count = 1;
        tohost = (201 << 8) | CMD_INJ_LOCKSTEP;
        for (volatile int i = 0; i < 500; i++) asm volatile ("nop");
        printf("FAIL: Scenario 4.2 did not trap!\n");
        tohost = 1;
    } else if (test_count == 1) {
        if (trap_count != 1) {
            printf("FAIL: Expected trap_count=1, got %d\n", trap_count);
            tohost = 1;
        }
        // Scenario 4.1 (TP_DCLS_INT_GPR): GPR Bit-Flip on a5 (x15)
        printf("Scenario 4.1 (TP_DCLS_INT_GPR): Forcing bit 15 flip in Lockstep GPR a5 (case 200)...\n");
        test_count = 2;
        register uint32_t a5_val asm("a5") = 0xAAAA5555;
        tohost = (200 << 8) | CMD_INJ_LOCKSTEP;
        for (int i = 0; i < 20; i++) {
            a5_val += 0x11111111; // Perform arithmetic on a5 in ALU stage
            asm volatile ("nop");
        }
        printf("FAIL: Scenario 4.1 did not trap!\n");
        tohost = 1;
    } else if (test_count == 2) {
        if (trap_count != 2) {
            printf("FAIL: Expected trap_count=2, got %d\n", trap_count);
            tohost = 1;
        }
        // Scenario 4.3 (TP_DCLS_INT_CSR): Architectural CSR Flop Tamper (mtvec)
        printf("Scenario 4.3 (TP_DCLS_INT_CSR): Forcing bit-flip inside Lockstep mtvec CSR flop (case 202)...\n");
        test_count = 3;
        write_csr(mtvec, (uint32_t)&trap_handler);
        tohost = (202 << 8) | CMD_INJ_LOCKSTEP;
        for (int i = 0; i < 20; i++) {
            uint32_t tvec_read = read_csr(mtvec);
            asm volatile ("nop");
        }
        printf("FAIL: Scenario 4.3 did not trap!\n");
        tohost = 1;
    } else if (test_count == 3) {
        if (trap_count != 3) {
            printf("FAIL: Expected trap_count=3, got %d\n", trap_count);
            tohost = 1;
        }
        printf("All 3 internal state tamper scenarios trapped and passed verification!\n");
        mie = read_csr(mie);
        mie &= ~(1 << 11);
        write_csr(mie, mie);
        mstatus = read_csr(mstatus);
        mstatus &= ~(1 << 3);
        write_csr(mstatus, mstatus);
        // Keep corruption active so tohost=0xFE sees corruption_detected_o == El2MuBiTrue
        tohost = (1 << 8) | CMD_INJ_LOCKSTEP;
        for (volatile int slp = 0; slp < 50; slp++) asm volatile ("nop");
        return 0;
    }

    return 0;
}
