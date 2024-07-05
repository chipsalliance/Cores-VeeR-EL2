#include <stdio.h>

#define read_csr(csr) ({ \
    unsigned long res; \
    asm volatile ("csrr %0, " #csr : "=r"(res)); \
    res; \
})

#define write_csr(csr, val) { \
    asm volatile ("csrw " #csr ", %0" : : "r"(val)); \
}

#define MISA_U  (1 << 20)

#define do_ecall()  asm volatile ("ecall")
#define do_ebreak() asm volatile ("ebreak\nnop") // EBREAK can translate to C.EBREAK. Insert a nop to align to 4
#define do_wfi()    asm volatile ("wfi")
#define do_sret()   asm volatile ("sret")
#define do_mret()   asm volatile ("mret")

#define is_ecall(x)  ((x) == 0x00000073)
#define is_ebreak(x) ((x) == 0x00100073 || ((x) & 0xFFFF) == 0x9002) // EBREAK or C.EBREAK
#define is_wfi(x)    ((x) == 0x10500073)
#define is_sret(x)   ((x) == 0x10200073)
#define is_mret(x)   ((x) == 0x30200073)

struct trap_info_t {
    uint32_t mcause;
    uint32_t insn;
};

volatile struct trap_info_t trap_info;

void trap_handler () {

    uint32_t mstatus = read_csr(mstatus);
    uint32_t mepc    = read_csr(mepc);

    trap_info.mcause = read_csr(mcause);
    trap_info.insn   = *((uint32_t*)mepc);

    printf("trap! mstatus=0x%08X, mcause=0x%08X, mepc=0x%08X, insn=0x%08X\n",
        mstatus, trap_info.mcause, mepc, trap_info.insn);
}

void clear_trap () {
    trap_info.mcause = 0x00;
    trap_info.insn   = 0x00;
}

volatile int global_result = 1; // Success

void check (int cond) {
    if (cond) {
        printf("pass\n");
    } else {
        printf("fail\n");
        global_result = 0;
    }
}

void user_main ();

int main () {
    printf("Hello VeeR\n");

    // The test requires user mode support
    if ((read_csr(misa) & MISA_U) == 0) {
        printf("ERROR: The test requires user mode support. Aborting.\n");
        return -1;
    }

    // Do EBREAK
    printf("testing EBREAK\n");
    clear_trap();
    do_ebreak();
    check(trap_info.mcause == 0x3 && is_ebreak(trap_info.insn));

    // Do ECALL
    printf("testing ECALL\n");
    clear_trap();
    do_ecall();
    check(trap_info.mcause == 0xb && is_ecall(trap_info.insn));

    // Do WFI
    printf("testing WFI\n");
    clear_trap();
    do_wfi();
    check(!trap_info.mcause); // No trap expected

    // Do SRET
    printf("testing SRET\n");
    clear_trap();
    do_sret();
    check(trap_info.mcause == 0x2 && is_sret(trap_info.insn));

    // Do not test MRET here. It is going to be used to go to user mode later
    // anyways.

    // Go to user mode
    unsigned long mstatus = read_csr(mstatus);
    mstatus &= ~(3 << 11);  // MPP  = 00 (user)
    mstatus &= ~(1 << 17);  // MPRV = 0
    write_csr(mstatus, mstatus);

    void* ptr = (void*)user_main;
    write_csr(mepc, (unsigned long)ptr);
    asm volatile ("mret");

    return 0;
}

__attribute__((noreturn)) void user_main () {
    printf("Hello from user_main()\n");

    // Do EBREAK
    printf("testing EBREAK\n");
    clear_trap();
    do_ebreak();
    check(trap_info.mcause == 0x3 && is_ebreak(trap_info.insn));

    // Do ECALL
    printf("testing ECALL\n");
    clear_trap();
    do_ecall();
    check(trap_info.mcause == 0x8 && is_ecall(trap_info.insn));

    // Do WFI
    printf("testing WFI\n");
    clear_trap();
    do_wfi();
    check(!trap_info.mcause); // No trap expected

    // Do SRET
    printf("testing SRET\n");
    clear_trap();
    do_sret();
    check(trap_info.mcause == 0x2 && is_sret(trap_info.insn));

    // Do MRET
    printf("testing MRET\n");
    clear_trap();
    do_mret();
    check(trap_info.mcause == 0x2 && is_mret(trap_info.insn));

    // Terminate the simulation
    // set the exit code to 0xFF or 0x1 and jump to _finish.
    unsigned char res = (global_result) ? 0xFF : 1;
    asm volatile (
        "mv a0, %0\n"
        "j  _finish\n"
        : : "r"(res)
    );

    while (1); // Make compiler not complain
}
