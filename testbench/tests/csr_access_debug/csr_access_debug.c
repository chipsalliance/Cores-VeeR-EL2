#include <stdio.h>
#include <stdint.h>
#include <string.h>

#define _read_csr(csr) ({ \
    unsigned long res; \
    asm volatile ("csrr %0, " #csr : "=r"(res)); \
    res; \
})

#define _write_csr(csr, val) { \
    asm volatile ("csrw " #csr ", %0" : : "r"(val)); \
}

#define MAGIC 0xDEADBEEF

#define CSR_DCSR 0x7B0
#define CSR_DPC 0x7B1
#define CSR_DMST 0x7C4
#define CSR_DICAWICS 0x7C8
#define CSR_DICAD0H 0x7CC
#define CSR_DICAD0 0x7C9
#define CSR_DICAD1 0x7CA
#define CSR_DICAGO 0x7CB

void trap_handler() {
    
}
unsigned long read_csr (uint32_t addr) {

    // Define the result to be explicitly in register a0 - the return value
    // by the calling convention. Preset it to a magic value so that when
    // a CSR access fails the value stays there.
    volatile register uint32_t val asm("a0") = MAGIC;

    // Since RISC-V does not allow indirect CSR addressing there's a big
    // 'switch' to handle that.
    switch (addr) {

        case 0x7B0: val = _read_csr(0x7B0); break;
        case 0x7B1: val = _read_csr(0x7B1); break;
        case 0x7C4: val = _read_csr(0x7C4); break;
        case 0x7C8: val = _read_csr(0x7C8); break;
        case 0x7CC: val = _read_csr(0x7CC); break;
        case 0x7C9: val = _read_csr(0x7C9); break;
        case 0x7CA: val = _read_csr(0x7CA); break;
        case 0x7CB: val = _read_csr(0x7CB); break;
    }

    return val;
}

void write_csr (uint32_t addr, uint32_t val) {

    // Since RISC-V does not allow indirect CSR addressing there's a big
    // 'switch' to handle that.

    switch (addr) {
        case 0x7B0: _write_csr(0x7B0, val); return;
        case 0x7B1: _write_csr(0x7B1, val); return;
        case 0x7C4: _write_csr(0x7C4, val); return;
        case 0x7C8: _write_csr(0x7C8, val); return;
        case 0x7CC: _write_csr(0x7CC, val); return;
        case 0x7C9: _write_csr(0x7C9, val); return;
        case 0x7CA: _write_csr(0x7CA, val); return;
        case 0x7CB: _write_csr(0x7CB, val); return;
    }
}

void test_csr_read_access (uint8_t user_mode) {

    volatile unsigned long val = read_csr(CSR_DCSR);
}

void test_routine() {
    // jump here in debug mode only
    // should be called from within gdb / openocd

    volatile uint32_t dicawics_val = 0;
    volatile uint32_t dicago_val = 0;
    volatile uint32_t dicad0_val = 0;
    volatile uint32_t dicad0h_val = 0;
    volatile uint32_t dicad1_val = 0;

    //Read a Chunk of an I-cache Cache Line
    // 1. Write dicawics              array=0   way=0     index=16
    dicawics_val = (0 << 24 | 0 << 20 | 16 << 3);
    write_csr(CSR_DICAWICS, dicawics_val);
    // 2. Read dicago to trigger a read access
    dicago_val = read_csr(CSR_DICAGO);
    // 3. read dicad0, dicad0h for cache line chunk
    dicad0_val = read_csr(CSR_DICAD0);
    dicad0h_val = read_csr(CSR_DICAD0H);
    // 4. read dicad1 for parity/ECC bits
    dicad1_val = read_csr(CSR_DICAD1);

    // Write a Chunk of an I-Cache Cache Line
}

int main () {
    printf("\nHello VeeR\n");

    int debug_mode = 0;
    while (debug_mode == 0) {
        ;
    }
    test_routine();
    while (1) {
        ;
    }

    return 0;
}
