/* SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Antmicro, Ltd. <www.antmicro.com>
 */

/*
This test verifies PMP execution protection of:
  1. Instructions that overlap multiple PMP regions of differing permissions.
  2. Compressed instructions that are located just before or just after a protected PMP region.

The tested memory fragment is visualized by the following diagram.
Note that only the last byte of the address is shown here. In reality all are based at 0x80008000

0x0             0x4              0x8              0xc                             0x14              0x18
|________________|________________|________________|________________________________|________________|
    PMP0(LRWX)       PMP1(LRWX)       PMP2(L---)                                        PMP3(L---)

       0x2              0x6              0xa              0xe              0x12   0x14      0x16    0x18
|_______|________________|________________|________________|________________|_______|________|_______|________|
  c.nop   jalr x0, x1, 0   jalr x0, x1, 0   jalr x0, x1, 0    c.nop; c.nop   c.jr ra c.jr ra  c.nop;  c.jr ra
*/

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <defines.h>

#define PMP_R     0x01
#define PMP_W     0x02
#define PMP_X     0x04
#define PMP_A     0x18
#define PMP_L     0x80
#define PMP_SHIFT 2

#define PMP_TOR   0x08
#define PMP_NA4   0x10
#define PMP_NAPOT 0x18

#define PMP0_CFG_SHIFT  0
#define PMP1_CFG_SHIFT  8
#define PMP2_CFG_SHIFT  16
#define PMP3_CFG_SHIFT  24

#define TEST_FAIL 0x1
#define TEST_SUCC 0xff
#define MAIL_RST  0x96

#define read_csr(csr) ({ \
    unsigned long res; \
    asm volatile ("csrr %0, " #csr : "=r"(res)); \
    res; \
})

#define write_csr(csr, val) { \
    asm volatile ("csrw " #csr ", %0" : : "r"(val)); \
}

extern volatile uint32_t tohost;

void __attribute__((noinline, naked, optimize("O0"), section(".text.pmp"))) pmpcode() {
    asm volatile (
        "c.nop;"          // 0x80008000
        "jalr x0, x1, 0;" // +0x2 OK!
        "jalr x0, x1, 0;" // +0x6 TRAP! ENDS IN PMP2
        "jalr x0, x1, 0;" // +0xa TRAP! STARTS IN PMP2
        "c.nop;"          // +0xe
        "c.nop;"          // +0x10
        "c.jr ra;"        // +0x12 OK! ENDS JUST BEFORE PMP3
        "c.jr ra;"        // +0x14 TRAP! ENTIRELY IN PMP3
        "c.nop;"          // +0x16
        "c.jr ra;"        // +0x18 OK! STARTS JUST AFTER PMP3
    );
}

static volatile uint32_t stage __attribute__((section(".dccm.persistent"))) = 0;
static volatile uint32_t traps __attribute__((section(".dccm.persistent"))) = 0;

void trap_handler () {
    uint32_t mstatus = read_csr(mstatus);
    uint32_t mcause  = read_csr(mcause);
    uint32_t mscause = read_csr(0x7FF);
    void*    mepc    = (void*)read_csr(mepc);
    void*    mtval   = (void*)read_csr(mtval);

    printf(
        "trap! mstatus=0x%08X, mcause=0x%08X, mscause=0x%08X, mepc=0x%08X, mtval=0x%08X\n",
        mstatus, mcause, mscause, mepc, mtval
    );

    int corr;
    switch(stage) {
        case 0: corr = mepc == pmpcode + 0x6 && mtval == pmpcode + 0x8; break;
        case 1: corr = mepc == pmpcode + 0xa && mtval == mepc; break;
        case 2: corr = mepc == pmpcode + 0x14 && mtval == mepc; break;
        default: corr = 0; break;
    }

    if (corr) {
        stage += 1;
        traps += 1;
        asm volatile (".rept 20; nop; .endr");
        tohost = MAIL_RST;
    } else {
        printf("This trap was unexpected at stage %d\n", stage);
        tohost = TEST_FAIL;
    }

    while(1);
}


#define PMP0ADDR (0x80008000 >> PMP_SHIFT)
#define PMP0CFG ((((PMP_L|PMP_R|PMP_W|PMP_X|PMP_NA4)   &0xFF) << PMP0_CFG_SHIFT))

#define PMP1ADDR (0x80008004 >> PMP_SHIFT)
#define PMP1CFG ((((PMP_L|PMP_R|PMP_W|PMP_X|PMP_NA4)   &0xFF) << PMP1_CFG_SHIFT))

#define PMP2ADDR (0x80008008 >> PMP_SHIFT)
#define PMP2CFG ((((PMP_L|                  PMP_NA4)   &0xFF) << PMP2_CFG_SHIFT))

#define PMP3ADDR (0x80008014 >> PMP_SHIFT)
#define PMP3CFG ((((PMP_L|                  PMP_NA4)   &0xFF) << PMP3_CFG_SHIFT))

int main () {
    if ((uint32_t)pmpcode != 0x80008000) {
        printf("Unexpected code location! 0x%08X\n", pmpcode);
        return -1;
    }

    write_csr(pmpaddr0, PMP0ADDR);
    write_csr(pmpcfg0, PMP0CFG);
    write_csr(pmpaddr1, PMP1ADDR);
    write_csr(pmpcfg0, PMP1CFG);
    write_csr(pmpaddr2, PMP2ADDR);
    write_csr(pmpcfg0, PMP2CFG);
    write_csr(pmpaddr3, PMP3ADDR);
    write_csr(pmpcfg0, PMP3CFG);

    switch(stage) {
        case 0:
            (pmpcode + 0x2)();  // Starts at PMP0, ends at PMP1, both are RWX -> should succeed
            (pmpcode + 0x12)(); // Compressed instruction, just before PMP3 -> should succeed
            (pmpcode + 0x18)(); // Compressed instruction, right after PMP3 -> should succeed
            (pmpcode + 0x6)();  // Starts at PMP1, ends at PMP2, PMP1 is RWX, PMP2 is protected -> should trap
            break;

        case 1: (pmpcode + 0xa)();  break; // Starts at PMP2, ends outside of any region -> should trap
        case 2: (pmpcode + 0x14)(); break; // Fully in protected PMP3 -> should trap
        case 3: {
            if (traps != 3) {
                printf("Invalid number of traps hit: %d\n", traps);
                return -1;
            }

            return 0;
        }

        default:
            printf("UNEXPECTED STAGE: %d\n", stage);
            return -1;
    }

    printf("A trap was expected at stage %d, but didn't occur\n", stage);
    return -1;
}
