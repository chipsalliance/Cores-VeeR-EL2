#include <stdint.h>
#include <stdio.h>

int main () {

    uint32_t value = 0;
    __asm__ volatile (
        "csrw 0x7f8, %0"        // Write the value of foo to MCGC CSR
        :                       // No output operands
        : "r"(value)            // Input operand (value) as register
    );

    for (int bit = 0; bit <= 9; bit++) {
        value = 1 << bit;
        __asm__ volatile (
            "csrw 0x7f8, %0"
            :
            : "r"(value)
        );
    }
    return 0;
}
