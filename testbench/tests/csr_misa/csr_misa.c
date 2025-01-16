#include <stdio.h>
#include <defines.h>

#define read_csr(csr) ({ \
    unsigned long res; \
    asm volatile ("csrr %0, " #csr : "=r"(res)); \
    res; \
})

int main () {
    #ifdef RV_USER_MODE
    const unsigned int user_mode = 1;
    #else
    const unsigned int user_mode = 0;
    #endif
    const unsigned int compressed_ext = 1;
    const unsigned int rv32i_base_isa = 1;
    const unsigned int int_mult_ext = 1;
    const unsigned int base = 1;
    const unsigned long golden = base << 30 | user_mode << 20  | int_mult_ext << 12 | \
                                 rv32i_base_isa << 8 | compressed_ext << 2;

    // Read and print misa
    unsigned long misa = read_csr(misa);
    printf("misa = 0x%08X vs. 0x%08X\n", misa, golden);

    // Check
    return (misa == golden) ? 0 : -1;
}
