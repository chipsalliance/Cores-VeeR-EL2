#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

// ============================================================================

#define CMD_INJ_VEER         0x91
#define CMD_INJ_LOCKSTEP     0x92

extern uint32_t tohost;

// ============================================================================

void user_main ();

int main () {
    printf("Hello VeeR\n");

    int r = 42;

    printf("Injecting error into signal of ID %0d\n", r);
    // Inject error
    tohost = r << 8 | CMD_INJ_VEER;

    return 0;
}