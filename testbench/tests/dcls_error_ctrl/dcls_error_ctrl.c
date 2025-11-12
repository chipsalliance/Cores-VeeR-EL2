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

volatile uint32_t test_count __attribute__((section(".dccm.persistent"))) = 0;
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
    printf("Test_count: %d, trap_count: %d\n", test_count, trap_count);

    unsigned long mie;
    unsigned long mstatus;

    unsigned long i;
    unsigned long tests_done;

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

    // Disable error monitoring
    printf("Disable reporting!\n");
    tohost = RV_MUBI_TRUE << 8 | CMD_INJ_CTRL;

    // Check all possible inject error values
    if (test_count < ((1 << RV_MUBI_WIDTH))) {
        for (i = test_count; i < (1 << RV_MUBI_WIDTH); ++i) {
            test_count++;
            tohost = i << 8 | CMD_INJ_EXT;
        }

        if (trap_count > 0) {
            tohost = 1;
        }

        tohost = RV_MUBI_FALSE << 8 | CMD_INJ_EXT;
    }
    tests_done = ((1 << RV_MUBI_WIDTH));

    if (test_count == tests_done) {
        // Inject error that is known to cuase error
        test_count++;
        tohost = 1 << 8 | CMD_INJ_LOCKSTEP;

        if (trap_count > 0) {
            tohost = 1;
        } else {
            // Reset cores to guarantee they are in sync
            tohost = CMD_INJ_CLEAR;
            tohost = CMD_RST;
        }
    }
    tests_done += 1;

    // Re-enable error monitoring
    printf("Re-enable reporting!\n");
    tohost = RV_MUBI_FALSE << 8 | CMD_INJ_CTRL;

    // Check all possible inject error values
    if (test_count - tests_done < (1 << RV_MUBI_WIDTH)) {
        for (i = test_count - tests_done; i < (1 << RV_MUBI_WIDTH); ++i) {
            test_count++;
            for (uint32_t slp = 0; slp < 20; slp++) {
                __asm__ volatile ("nop"); // Sleep loop as "nop"
            }
            tohost = i << 8 | CMD_INJ_EXT;
        }
    }
    if (test_count - tests_done == (1 << RV_MUBI_WIDTH) && trap_count != (1 << RV_MUBI_WIDTH) - 1) {
        tohost = 1;
    } else if (test_count - tests_done == (1 << RV_MUBI_WIDTH)) {
        printf("Clearing test_count\n");
        trap_count = 0;
    }
    tests_done += (1 << RV_MUBI_WIDTH);

    // Check all possible disable error values
    if (test_count - tests_done < (1 << RV_MUBI_WIDTH)) {
        for (i = test_count - tests_done; i < (1 << RV_MUBI_WIDTH); ++i) {
            test_count++;
            tohost = i << 8 | CMD_INJ_CTRL;
        }
    }
    if (test_count - tests_done == (1 << RV_MUBI_WIDTH) && trap_count != (1 << RV_MUBI_WIDTH) - 2) {
        tohost = 1;
    } else if (test_count - tests_done == (1 << RV_MUBI_WIDTH)) {
        printf("Clearing test_count\n");
        trap_count = 0;
    }
    tests_done += (1 << RV_MUBI_WIDTH);

    mie = read_csr(mie);
    mie &= ~(1 << 11);
    write_csr(mie, mie);

    mstatus = read_csr(mstatus);
    mstatus &= ~(1 << 3);
    write_csr(mstatus, mstatus);

    // Inject error that is known to cuase error
    tohost = 1 << 8 | CMD_INJ_LOCKSTEP;
    return 0;
}
