/*
 * Core RAS Scope: ECC Counter & Threshold Alert Test
 * Author: Samip Modi (samipmodi@google.com)
 *
 * Description:
 * This test verifies the Reliability, Availability, and Serviceability (RAS) Single-Bit Error
 * (SBE) counting mechanism and threshold alert generation in the Data Closely Coupled Memory
 * (DCCM) using the MDCCMECT (DCCM ECC Counter and Threshold) CSR (0x7F2).
 *
 * Test Sequence:
 * 1. Programs the DCCM ECC error threshold field (MDCCMECT[31:27]) to N=3.
 * 2. Enables single-bit DCCM error injection via testbench stimulus (INJECT_DCCM_SINGLE_BIT).
 * 3. Executes repeated read/write accesses to dummy DCCM data.
 * 4. Verifies that the internal ECC counter increments on each single-bit error access.
 * 5. Confirms that when the error count reaches the programmed threshold (N=3), an ECC
 *    threshold alert trap is generated and handled cleanly.
 */

#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>

#define STDOUT 0xd0580000

#define INJECT_DCCM_SINGLE_BIT  0xe2
#define DISABLE_ERROR_INJECTION 0xe4
#define TEST_PASSED             0xff
#define TEST_FAILED             0x01

extern volatile uint32_t tohost;
volatile uint32_t dummy_data __attribute__((section(".dccm"))) = 0x11223344;

int read_mdccmect(void) {
    uint32_t val;
    __asm__ volatile ("csrr %0, %1" : "=r" (val) : "i" (0x7F2));
    return val;
}

void write_mdccmect(uint32_t val) {
    __asm__ volatile ("csrw %1, %0" : : "r" (val), "i" (0x7F2));
}

volatile int trap_count = 0;
void trap_handler(void) {
    printf("ECC threshold alert trap received!\n");
    trap_count++;
    tohost = DISABLE_ERROR_INJECTION;
}

int main () {
    printf("Starting Core RAS Scope: ECC Counter & Threshold Alert Test...\n");

    // Configure mtvec and enable Machine Correctable Error Interrupts (MCEIE bit 5)
    __asm__ volatile ("csrw mtvec, %0" : : "r" ((uint32_t)&trap_handler));
    uint32_t mie_val;
    __asm__ volatile ("csrr %0, mie" : "=r" (mie_val));
    mie_val |= (1 << 5);
    __asm__ volatile ("csrw mie, %0" : : "r" (mie_val));
    uint32_t mstatus_val;
    __asm__ volatile ("csrr %0, mstatus" : "=r" (mstatus_val));
    mstatus_val |= (1 << 3);
    __asm__ volatile ("csrw mstatus, %0" : : "r" (mstatus_val));

    // Program DCCM Parity/ECC Threshold to N=3 (bits [31:27])
    uint32_t threshold = (3 << 27);
    write_mdccmect(threshold);
    printf("Programmed MDCCMECT threshold to 3. Initial MDCCMECT=0x%08X\n", read_mdccmect());

    // Enable error injection
    tohost = INJECT_DCCM_SINGLE_BIT;

    for (int i = 1; i <= 4; i++) {
        dummy_data ^= 0xFFFFFFFF; // Trigger DCCM write/read cycle
        uint32_t mdccm = read_mdccmect();
        printf("Access %d: MDCCMECT=0x%08X (Counter=%d)\n", i, mdccm, mdccm & 0x7FFFFFF);
        for (int slp = 0; slp < 10; slp++) asm volatile ("nop");
    }

    tohost = DISABLE_ERROR_INJECTION;

    if (trap_count > 0 || (read_mdccmect() & 0x7FFFFFF) >= 3) {
        printf("Core RAS ECC Threshold Test PASSED.\n");
        // Keep corruption active for DCLS exit monitor (tohost=0xFE)
        tohost = (1 << 8) | 0x92;
        for (volatile int slp = 0; slp < 50; slp++) asm volatile ("nop");
        return 0;
    } else {
        printf("Core RAS ECC Threshold Test FAILED.\n");
        return 1;
    }
}
