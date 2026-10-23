#ifndef DCLS_REGFILE_READ_H
#define DCLS_REGFILE_READ_H

#include <stdint.h>
#include "../dcls/dcls_common.h"

#define MBOX_ADDR               0xD0580000
#define TEST_PASSED             0xFF
#define TEST_FAILED             0x01

#define CMD_CLR_IRQ             0x82
#define CMD_CLR_SOFT_TIMER_INT  ((0x6 << 8) | CMD_CLR_IRQ)
#define CMD_SET_SOFT_INT        0x84
#define CMD_SET_TIMER_INT       0x85
#define CMD_INJ_VEER            0x91
#define CMD_INJ_LOCKSTEP        0x92
#define CMD_INJ_EXT             0x93
#define CMD_INJ_CTRL            0x94
#define CMD_INJ_CLEAR           0x95
#define CMD_RST                 0x96
#define SET_NMI_INT             0x183
#define CLEAR_NMI_INT           0x182

/*
 * Expected mcause values for PIC DCLS IRQ #2 (`corruption_detected_o`):
 * - MCAUSE_MEI (0x8000000B): standard Machine External Interrupt (when
 *   FAST_INTERRUPT_REDIRECT == 0 or MEIVT points to a valid DCCM table).
 * - MCAUSE_NMI_FIR_NON_DCCM (0xF0001002): Fast Interrupt Redirect NMI on
 *   external interrupt #2 when FAST_INTERRUPT_REDIRECT == 1 and MEIVT is
 *   at its reset default (0x0, non-DCCM region).
 */
#define MCAUSE_MEI              0x8000000BU
#define MCAUSE_NMI_FIR_NON_DCCM 0xF0001002U
#define TOTAL_TEST_CASES        75U

/* VeeR EL2 custom CSR addresses */
#define CSR_MRAC                0x7c0
#define CSR_MITB0               0x7d3
#define CSR_MITB1               0x7d6
#define CSR_MDCCMECT            0x7f2

#define read_csr(csr) ({ \
    unsigned long res; \
    asm volatile ("csrr %0, " CSR_STR(csr) : "=r"(res)); \
    res; \
})

#define write_csr(csr, val) do { \
    asm volatile ("csrw " CSR_STR(csr) ", %0" : : "r"(val)); \
} while (0)

#define tohost (*(volatile uint32_t*)MBOX_ADDR)

#define INJECT_ERR(id, cmd) do { \
    tohost = ((id) << 8) | (cmd); \
} while (0)

#define SEND_TEST_STATUS(status) do { \
    *((volatile uint8_t*)MBOX_ADDR) = (status); \
} while (0)

#endif // DCLS_REGFILE_READ_H
