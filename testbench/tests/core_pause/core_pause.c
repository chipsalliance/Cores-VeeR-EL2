#include <stdint.h>
#include <stdio.h>

int main () {
    /* pause the core for 0xfff cycles */
    uint32_t value = 0xfff;
    __asm__ volatile (
        "csrw 0x7c2, %0"        // Write the value of foo to MCPC CSR
        :                       // No output operands
        : "r"(value)            // Input operand (value) as register
    );
    return 0;
}
