#include <stdio.h>

#define read_csr(csr) ({ \
    unsigned long res; \
    asm volatile ("csrr %0, " #csr : "=r"(res)); \
    res; \
})

int main () {

    const unsigned long golden = 0x40101104;

    // Read and print misa
    unsigned long misa = read_csr(misa);
    printf("misa = 0x%08X vs. 0x%08X\n", misa, golden);

    // Check
    return (misa == golden) ? 0 : -1;
}
