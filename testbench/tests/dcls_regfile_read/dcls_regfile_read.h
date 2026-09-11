#ifndef DCLS_REGFILE_READ_H
#define DCLS_REGFILE_READ_H

#include <stdint.h>

#define MBOX_ADDR 0xD0580000
#define TEST_PASSED 0xFF
#define TEST_FAILED 0x01

#define CMD_INJ_VEER     0x91
#define CMD_INJ_LOCKSTEP 0x92
#define CMD_INJ_EXT      0x93
#define CMD_INJ_CTRL     0x94
#define CMD_INJ_CLEAR    0x95
#define CMD_RST          0x96
#define SET_NMI_INT      0x183
#define CLEAR_NMI_INT    0x182

#define read_csr(csr) ({     unsigned long res;     asm volatile ("csrr %0, " #csr : "=r"(res));     res; })

#define write_csr(csr, val) {     asm volatile ("csrw " #csr ", %0" : : "r"(val)); }

#define tohost (*(volatile uint32_t*)0xD0580000)

#define INJECT_ERR(id, cmd) do {     tohost = ((id) << 8) | (cmd); } while(0)

#define SEND_TEST_STATUS(status) do {     *((volatile uint8_t*)MBOX_ADDR) = (status); } while(0)

#endif // DCLS_REGFILE_READ_H
