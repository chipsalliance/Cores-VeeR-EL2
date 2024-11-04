#include <stdio.h>

#define read_csr(csr) ({ \
    unsigned long res; \
    asm volatile ("csrr %0, " #csr : "=r"(res)); \
    res; \
})

int main () {
    // bit [20] is set to 0 to skip checking U mode, to make this test work both with U mode and without U mode.
    const unsigned long check_mask = ~(1 << 20);

    const unsigned long golden = 0x40101104 & check_mask;

    // Read and print misa
    unsigned long misa = read_csr(misa) & check_mask;

    printf("misa = 0x%08X vs. 0x%08X\n", misa, golden);

    // Check
    return (misa == golden) ? 0 : -1;
}
