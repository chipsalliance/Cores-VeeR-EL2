#include <stdio.h>

#define read_csr(csr) ({ \
    unsigned long res; \
    asm volatile ("csrr %0, " #csr : "=r"(res)); \
    res; \
})

#define write_csr(csr, val) { \
    asm volatile ("csrw " #csr ", %0" : : "r"(val)); \
}

#define do_ecall() asm volatile ("ecall")

unsigned long trap_causes[4];
unsigned long trap_count = 0;

void trap_handler () {

    unsigned long mstatus = read_csr(mstatus);
    unsigned long mcause  = read_csr(mcause);
    printf("trap! mstatus=0x%08X, mcause=0x%08X\n", mstatus, mcause);

    // Store cause
    if (trap_count < (sizeof(trap_causes) / sizeof(trap_causes[0]))) {
        trap_causes[trap_count++] = mcause;
    }
}

void user_main ();

__attribute__((noreturn)) void main () {
    printf("Hello VeeR\n");

    // main() gets called from _start. We should be in machine mode
    // make an ECALL which should set mcause to 11 (0xB)
    printf("doing ECALL...\n");
    do_ecall();
    printf("mstatus=0x%08X, continuing.\n", read_csr(mstatus));

    // Go to user mode
    unsigned long mstatus = read_csr(mstatus);
    mstatus &= ~(3 << 11);  // MPP  = 00 (user)
    mstatus &= ~(1 << 17);  // MPRV = 0
    write_csr(mstatus, mstatus);

    void* ptr = (void*)user_main;
    write_csr(mepc, (unsigned long)ptr);
    asm volatile ("mret");
}

__attribute__((noreturn)) void user_main () {
    printf("Hello from user_main(), mstatus=0x%08X\n", read_csr(mstatus));

    // We should be now in user mode
    // make an ECALL which should set mcause to 8 (0x8)
    printf("doing ECALL...\n");
    do_ecall();
    printf("mstatus=0x%08X, continuing.\n", read_csr(mstatus));

    // Verify trap causes
    unsigned char res = 0xFF; // success

    printf("traps taken:\n");
    for (unsigned long i=0; i<trap_count; ++i) {
        printf(" %d. 0x%08X\n", i, trap_causes[i]);
    }

    if (trap_count == 2) {
        // Incorrect causes
        if (trap_causes[0] != 0xb || trap_causes[1] != 0x8) {
            res = 1;
        }
    }
    else {
        // Incorrect trap count
        res = 1;
    }

    // Terminate the simulation
    // set the exit code to 0xFF and jump to _finish.
    asm volatile (
        "mv a0, %0\n"
        "j  _finish\n"
        : : "r"(res)
    );
}
