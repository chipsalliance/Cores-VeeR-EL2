#include <stdio.h>

#define read_csr(csr) ({ \
    unsigned long res; \
    asm volatile ("csrr %0, " #csr : "=r"(res)); \
    res; \
})

#define U_MODE_MASK (1<<20)

int main () {
    unsigned long golden;

    // Read and print misa
    unsigned long misa = read_csr(misa);

    // This is to make the test work both with U mode and without U mode.
    // we're modifying the golden rather than ignoring a bit because Renode tests assume there's a specific string in the output.
    if (misa & U_MODE_MASK) {
        golden = 0x40101104;
    } else {
        golden = 0x40001104;
    }
    printf("misa = 0x%08X vs. 0x%08X\n", misa, golden);

    // Check
    return (misa == golden) ? 0 : -1;
}
