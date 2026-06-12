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
#define CMD_DBG_SEQ          0x97
#define CMD_FAIL             0x99

// We use a persistent variable to track the test phase across resets.
volatile uint32_t test_phase __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t has_been_reset __attribute__((section(".dccm.persistent"))) = 0;

extern uint32_t tohost;
volatile uint32_t *threshold    = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIPT_OFFSET);
volatile uint32_t *gateway      = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIGWCTRL_OFFSET);
volatile uint32_t *clr_gateway  = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIGWCLR_OFFSET);
volatile uint32_t *priority     = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIPL_OFFSET);
volatile uint32_t *enable       = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIE_OFFSET);

void trap_handler () {
    uint32_t mstatus = read_csr(mstatus);
    uint32_t mcause  = read_csr(mcause);
    uint32_t mepc    = read_csr(mepc);

    printf("Trap! test_phase=%d, mstatus=0x%08X, mcause=0x%08X, mepc=0x%08X\n", test_phase, mstatus, mcause, mepc);

    // Clear injection immediately to avoid continuous trapping if we don't reset immediately
    tohost = CMD_INJ_CLEAR;

    if (test_phase == 0) {
        printf("Phase 0 trap: DCLS caught injected error (Expected).\n");
        test_phase = 1;
        printf("Resetting for Phase 1...\n");
        tohost = CMD_RST;
    } else if (test_phase == 1) {
        printf("Phase 1 trap: DCLS caught injected error in Debug Mode (UNEXPECTED!).\n");
        tohost = CMD_FAIL;
    } else if (test_phase == 2) {
        printf("Phase 2 trap: DCLS caught injected error after reset (Expected).\n");
        printf("Test PASSED.\n");
        tohost = 0xFE; // Success exit code
    } else {
        printf("Unexpected trap in phase %d.\n", test_phase);
        tohost = CMD_FAIL;
    }
    
    // We should not reach here if reset or exit happened, but just in case:
    while(1);
}

void delay(int cycles) {
    for (volatile int i = 0; i < cycles; i++) {
        __asm__ volatile ("nop");
    }
}

int main () {
    printf("Booting main... (has_been_reset=%d)\n", has_been_reset);
    if (has_been_reset == 0) {
        printf("Triggering initial reset...\n");
        has_been_reset = 1;
        tohost = CMD_RST;
        delay(10);
        printf("Warning: Reset did not happen immediately.\n");
    }

    printf("DCLS Debug Mode Test - Start (Phase %d)\n", test_phase);

    // Enable interrupts (needed for trap handler to be called on DCLS error)
    // DCLS error is mapped to external interrupt 2 in tb_top.sv
    unsigned long mie;
    unsigned long mstatus;

    mie = read_csr(mie);
    mie &= ~(1 << 11); // Disable external interrupts while configuring
    write_csr(mie, mie);

    *threshold = 1;
    gateway[2] = (1 << 1) | 0; // Level triggered, active high?
    clr_gateway[2] = 0;
    priority[2] = 7; // High priority
    enable[2] = 1; // Enable interrupt 2

    mie = read_csr(mie);
    mie |= (1 << 11); // Enable external interrupts
    write_csr(mie, mie);

    mstatus = read_csr(mstatus);
    mstatus |= (1 << 3); // MIE bit in mstatus
    write_csr(mstatus, mstatus);

    if (test_phase == 0) {
        printf("Phase 0: Verifying DCLS is active and catches errors.\n");
        // Inject error into Lockstep core (signal ID 1 is a good candidate, used in dcls.c)
        tohost = 1 << 8 | CMD_INJ_LOCKSTEP;
        
        // Wait for trap. If no trap, we fail.
        delay(100);
        printf("Error: Phase 0 did not trap after error injection.\n");
        tohost = CMD_FAIL;
        
    } else if (test_phase == 1) {
        printf("Phase 1: Triggering Debug Mode and verifying DCLS is suppressed.\n");
        
        // Trigger Debug Mode sequence (halt then run)
        tohost = CMD_DBG_SEQ;
        
        // We should have resumed now.
        printf("Resumed from Debug Mode. Injecting error (should be suppressed).\n");
        tohost = 1 << 8 | CMD_INJ_LOCKSTEP;
        
        // Wait to see if we trap. We expect NOT to trap.
        delay(200); 
        printf("No trap occurred (Expected). DCLS is suppressed in Debug Mode.\n");
        
        // Clear injection (even though it was suppressed, clean up)
        tohost = CMD_INJ_CLEAR;
        
        test_phase = 2;
        printf("Resetting for Phase 2...\n");
        tohost = CMD_RST;
        
    } else if (test_phase == 2) {
        printf("Phase 2: Verifying DCLS is active again after reset.\n");
        // Inject error
        tohost = 1 << 8 | CMD_INJ_LOCKSTEP;
        
        // Wait for trap.
        delay(100);
        printf("Error: Phase 2 did not trap after error injection.\n");
        tohost = CMD_FAIL;
    }

    return 0;
}
