#include <stdio.h>

#define read_csr(csr) ({ \
    unsigned long res; \
    asm volatile ("csrr %0, " #csr : "=r"(res)); \
    res; \
})

#define write_csr(csr, val) { \
    asm volatile ("csrw " #csr ", %0" : : "r"(val)); \
}

int main () {

    unsigned long prv, cur;
    int res = 0;

    // Test privilete mode availablilty by writing to mstatus.MPP and reading
    // it back. The value should match.

    // M-mode
    printf("M mode:\n");
    prv  = read_csr(mstatus);
    prv &= ~(3 << 11);
    prv |=  (3 << 11); // MPP = 11
    printf(" 0x%08X\n", prv);
    write_csr(mstatus, prv);
    cur  = read_csr(mstatus);
    printf(" 0x%08X\n", cur);
    if (((prv ^ cur) & (3 << 11)) == 0) {
        printf(" ok.\n");
    } else {
        printf(" not supported.\n");
        res = -1; // error
    }

    // S-mode
    printf("S mode:\n");
    prv  = read_csr(mstatus);
    prv &= ~(3 << 11);
    prv |=  (1 << 11); // MPP = 01
    printf(" 0x%08X\n", prv);
    write_csr(mstatus, prv);
    cur  = read_csr(mstatus);
    printf(" 0x%08X\n", cur);
    if (((prv ^ cur) & (3 << 11)) == 0) {
        printf(" ok.\n");
        res = -1; // error
    } else {
        printf(" not supported.\n");
    }

    // U-mode
    printf("U mode:\n");
    prv  = read_csr(mstatus);
    prv &= ~(3 << 11); // MPP = 00
    printf(" 0x%08X\n", prv);
    write_csr(mstatus, prv);
    cur  = read_csr(mstatus);
    printf(" 0x%08X\n", cur);
    if (((prv ^ cur) & (3 << 11)) == 0) {
        printf(" ok.\n");
    } else {
        printf(" not supported.\n");
        res = -1; // error
    }

    return res;
}