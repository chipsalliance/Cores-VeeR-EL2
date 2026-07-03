#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <defines.h>

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
#define CMD_INJ_EXT          0x93
#define CMD_INJ_CTRL         0x94
#define CMD_INJ_CLEAR        0x95
#define CMD_RST              0x96
#define CMD_ENT_DBG          0xA0
#define CMD_FAIL             0x1

volatile uint32_t boot_count __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t trap_count __attribute__((section(".dccm.persistent"))) = 0;

extern volatile uint32_t tohost;
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

    tohost = CMD_INJ_CLEAR;
    tohost = RV_MUBI_FALSE << 8 | CMD_INJ_EXT;
    tohost = RV_MUBI_FALSE << 8 | CMD_INJ_CTRL;

    printf("trap! mstatus=0x%08X, mcause=0x%08X, mepc=0x%08X\n", mstatus, mcause, mepc);
    trap_count++;

    tohost = CMD_RST;
}

int main () {
    printf("Hello VeeR\n");
    boot_count++;

    unsigned long mie;
    unsigned long mstatus;

    unsigned long i;
    unsigned long tests_done;

    // Disable machine external interrupts
    mie = read_csr(mie);
    mie &= ~(1 << 11);
    write_csr(mie, mie);

    // Configure PIC for DCLS interrupts
    *threshold = 1;
    gateway[2] = (1 << 1) | 0;
    clr_gateway[2] = 0;
    priority[2] = 7;
    enable[2] = 1;

    // Enable machine external interrupts
    mie = read_csr(mie);
    mie |= (1 << 11);
    write_csr(mie, mie);

    // Enable machine interrupts
    mstatus = read_csr(mstatus);
    mstatus |= (1 << 3);
    write_csr(mstatus, mstatus);

    if (boot_count == 1) {
        printf("Inject error (should trigger a trap)\n");
        tohost = (RV_MUBI_TRUE << 8) | CMD_INJ_EXT;
    } else if (boot_count == 2) {
        if (trap_count != 1) {
            printf("ERROR: Corruption was not reported\n");
            tohost = CMD_FAIL;
        }

        printf("Execute enter/exit debug mode\n");
        tohost = 1 << 8 | CMD_ENT_DBG;

        printf("Inject error (should be ignored)\n");
        tohost = (RV_MUBI_TRUE << 8) | CMD_INJ_EXT;

        if (trap_count != 1) {
            printf("ERROR: Corruption was reported after entering debug mode\n");
            tohost = CMD_FAIL;
        }
    } else {
        printf("ERROR: This should have never been reached, reset was done too many times\n");
        tohost = CMD_FAIL;
    }
    for (uint32_t slp = 0; slp < 100; slp++) {
        __asm__ volatile ("nop");
    }
    return 0;
}
