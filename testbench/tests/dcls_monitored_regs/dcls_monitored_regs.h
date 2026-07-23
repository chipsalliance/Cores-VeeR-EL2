/*
 * dcls_monitored_regs.h
 *
 * Header for VeeR-EL2 DCLS Monitored Registers Corruption Test.
 * Validates Section 5.1.2. Monitored Registers.
 *
 * Author: navadiya
 */

#ifndef DCLS_MONITORED_REGS_H
#define DCLS_MONITORED_REGS_H

#include <stdint.h>

// Mailbox & Testbench Communication
#define MBOX_ADDR 0xD0580000
#define TEST_PASSED 0xFF
#define TEST_FAILED 0x01

#define CMD_INJ_VEER     0x91
#define CMD_INJ_LOCKSTEP 0x92
#define CMD_INJ_CLEAR    0x95
#define CMD_RST          0x96

extern volatile uint32_t tohost;

// Macro to send fault injection ID command to tb_top via tohost mailbox
#define INJECT_ERR(id, cmd) do { \
    tohost = ((id) << 8) | (cmd); \
} while(0)

#define SEND_TEST_STATUS(status) do { \
    *((volatile uint8_t*)MBOX_ADDR) = (status); \
} while(0)

#endif // DCLS_MONITORED_REGS_H