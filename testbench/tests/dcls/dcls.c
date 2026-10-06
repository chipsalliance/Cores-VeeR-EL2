#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <defines.h>

#include "dcls_common.h"

// ============================================================================

#define read_csr(csr) ({ \
    unsigned long res; \
    asm volatile ("csrr %0, " #csr : "=r"(res)); \
    res; \
})

#define write_csr(csr, val) { \
    asm volatile ("csrw " #csr ", %0" : : "r"(val)); \
}

// ============================================================================

#define CMD_INJ_VEER         0x91
#define CMD_INJ_LOCKSTEP     0x92
#define CMD_INJ_CLEAR        0x95
#define CMD_RST              0x96
#define SET_NMI_INT          0x183
#define CLEAR_NMI_INT        0x182

volatile uint32_t boot_count __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t hart_id    __attribute__((section(".dccm.persistent"))) = 0;

extern uint32_t tohost;
volatile uint32_t *threshold    = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIPT_OFFSET);
volatile uint32_t *gateway      = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIGWCTRL_OFFSET);
volatile uint32_t *clr_gateway  = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIGWCLR_OFFSET);
volatile uint32_t *priority     = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIPL_OFFSET);
volatile uint32_t *enable       = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIE_OFFSET);

// ============================================================================

void trap_handler () {
    uint32_t mstatus = read_csr(mstatus);
    uint32_t mcause  = read_csr(mcause);
    uint32_t mepc    = read_csr(mepc);

    tohost = CLEAR_NMI_INT;
    tohost = CMD_INJ_CLEAR;

    printf("trap! mstatus=0x%08X, mcause=0x%08X, mepc=0x%08X\n", mstatus, mcause, mepc);

    tohost = CMD_RST;
}

int main () {
    uint32_t old_boot_count = boot_count;

    printf("Hello VeeR\n");

    unsigned long mie;
    unsigned long mstatus;

#if (SDVT_AHB == 0)
    if (old_boot_count < (195 * 2)) {
#else
    if (old_boot_count < (93 * 2)) {
#endif
        mie = read_csr(mie);
        mie &= ~(1 << 11);
        write_csr(mie, mie);

        *threshold = 1;
        gateway[2] = (1 << 1) | 0;
        clr_gateway[2] = 0;
        priority[2] = 7;
        enable[2] = 1;

        mie = read_csr(mie);
        mie |= (1 << 11);
        write_csr(mie, mie);

        mstatus = read_csr(mstatus);
        mstatus |= (1 << 3);
        write_csr(mstatus, mstatus);
    }

#if (SDVT_AHB == 0)
    while (old_boot_count < (195 * 2)) {
#else
    while (old_boot_count < (93 * 2)) {
#endif
        old_boot_count = boot_count;
        boot_count++;

        // Skip Main Core (`VEER`) signals that break code execution in `.text`
        // or corrupt the DCCM stack; these are verified in `dcls_skipped_signals`.
        if (is_skipped_in_dcls(old_boot_count)) {
            continue;
        }

        printf("Injecting error into signal of ID %0d\n", old_boot_count);
        // Inject error
        tohost = (old_boot_count >> 1) << 8 | ((old_boot_count & 1) ? CMD_INJ_LOCKSTEP : CMD_INJ_VEER);

        for (uint32_t slp = 0; slp < 20; slp++) {
            __asm__ volatile ("nop"); // Sleep loop as "nop"
        }
        if (old_boot_count == 1) {
            tohost = CMD_RST;
        } else if (old_boot_count == 5) {
            tohost = SET_NMI_INT;
        } else if ((old_boot_count >> 1) == 5) {
            __asm__ volatile ("csrr t0, mhartid;"
                              "la t1, %0;"
                              "sw t0, 0(t1)" : : "i" ((uintptr_t)&hart_id));
        } else {
            tohost = CMD_INJ_CLEAR;
        }
        for (uint32_t slp = 0; slp < 20; slp++) {
            __asm__ volatile ("nop"); // Sleep loop as "nop"
        }
    }
    // Inject error that is known to cause error
    tohost = 1 << 8 | CMD_INJ_LOCKSTEP;
    for (uint32_t slp = 0; slp < 100; slp++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }
    return 0;
}
