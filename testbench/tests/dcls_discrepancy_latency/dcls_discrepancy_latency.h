/* SPDX-License-Identifier: Apache-2.0 */

#ifndef DCLS_DISCREPANCY_LATENCY_H
#define DCLS_DISCREPANCY_LATENCY_H

#include <stdint.h>

#define MBOX_ADDR   0xD0580000UL
#define TEST_PASSED 0xFF
#define TEST_FAILED 0x01

#define CMD_INJ_VEER     0x91
#define CMD_INJ_LOCKSTEP 0x92
#define CMD_INJ_CLEAR    0x95
#define CMD_RST          0x96
#define CLEAR_NMI_INT    0x182

#define MCAUSE_MEI          0x8000000BUL
#define MCAUSE_FIR_NON_DCCM 0xF0001002UL

#define read_csr(csr) ({ \
    unsigned long res; \
    asm volatile ("csrr %0, " #csr : "=r"(res)); \
    res; \
})

#define write_csr(csr, val) do { \
    asm volatile ("csrw " #csr ", %0" : : "r"(val)); \
} while (0)

#define tohost (*(volatile uint32_t *)MBOX_ADDR)

#define WRITE_MBOX(val) do { \
    tohost = (val); \
    asm volatile ("fence" ::: "memory"); \
} while (0)

#define SEND_TEST_STATUS(status) do { \
    *((volatile uint8_t *)MBOX_ADDR) = (status); \
    asm volatile ("fence" ::: "memory"); \
} while (0)

#endif // DCLS_DISCREPANCY_LATENCY_H
