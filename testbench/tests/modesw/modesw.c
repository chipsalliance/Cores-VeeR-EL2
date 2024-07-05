#include <stdio.h>
#include <stdint.h>

#define read_csr(csr) ({ \
    unsigned long res; \
    asm volatile ("csrr %0, " #csr : "=r"(res)); \
    res; \
})

#define write_csr(csr, val) { \
    asm volatile ("csrw " #csr ", %0" : : "r"(val)); \
}

#define MISA_U              (1 << 20)

#define MSTATUS_MPRV        (1 << 17)

#define MSTATUS_MPP_MASK    (3 << 11)
#define MSTATUS_MPP_MACHINE (3 << 11)
#define MSTATUS_MPP_USER    (0 << 11)

#define MCAUSE_ECALL_U      0x8
#define MCAUSE_ECALL_M      0xb

extern int32_t do_ecall (uint32_t cmd, uint32_t arg);

#define ECALL_HELLO         0x10
#define ECALL_CLR_MPRV      0x20
#define ECALL_SET_MPRV      0x21
#define ECALL_GET_MSTATUS   0x30

struct trap_data_t {
    uint32_t    mcause;
    uint32_t    mstatus;
};

struct trap_data_t trap_data[32];
uint32_t trap_count = 0;

volatile int32_t global_fail = 0;

int32_t trap_handler (uint32_t cmd, uint32_t arg) {

    unsigned long mstatus = read_csr(mstatus);
    unsigned long mcause  = read_csr(mcause);
    unsigned long mepc    = read_csr(mepc);

    // Store trap data
    if (trap_count < (sizeof(trap_data) / sizeof(trap_data[0]))) {
        trap_data[trap_count].mcause  = mcause;
        trap_data[trap_count].mstatus = mstatus;
        trap_count++;
    }

    printf("trap! mstatus=0x%08X, mcause=0x%08X, mepc=0x%08X\n", mstatus, mcause, mepc);

    // Handle ecall
    if (mcause == MCAUSE_ECALL_U || mcause == MCAUSE_ECALL_M) {
        printf("Hello ECALL.%c\n", (mcause == MCAUSE_ECALL_U) ? 'U' :
                                   (mcause == MCAUSE_ECALL_M) ? 'M' : '?');
        if (cmd == ECALL_HELLO) {
            return 0;
        }
        if (cmd == ECALL_CLR_MPRV) {
            printf(" clearing mstatus.MPRV\n");
            mstatus &= ~MSTATUS_MPRV;
            write_csr(mstatus, mstatus);
            return mstatus;
        }
        if (cmd == ECALL_SET_MPRV) {
            printf(" setting mstatus.MPRV\n");
            mstatus |=  MSTATUS_MPRV;
            write_csr(mstatus, mstatus);
            return mstatus;
        }
        if (cmd == ECALL_GET_MSTATUS) {
            return mstatus;
        }

        printf(" unknown ECALL code 0x%08X !\n", cmd);
        return -1;
    }

    return 0; // Ignored
}

void user_main ();

int main () {

    // The test requires user mode support
    if ((read_csr(misa) & MISA_U) == 0) {
        printf("ERROR: The test requires user mode support. Aborting.\n");
        return -1;
    }

    uint32_t mstatus = read_csr(mstatus);

    // main() gets called from _start. We should be in machine mode.
    printf("Hello VeeR\n");

    // Verify initial state of mstatus after reset
    if (!(mstatus & MSTATUS_MPRV)) {
        printf("[  OK  ] MPRV cleared\n");
    } else {
        printf("[ FAIL ] MPRV is set!\n");
        global_fail = 1;
    }

    // Check if MPP is set to 11
    if ((mstatus & MSTATUS_MPP_MASK) == MSTATUS_MPP_MACHINE) {
        printf("[  OK  ] MPP is 11\n");
    } else {
        printf("[ FAIL ] MPP is not 11\n");
        global_fail = 1;
    }

    // Clear MPRV, make an ECALL which should set mcause to 11 (0xB) and
    // leave MPRV 
    mstatus = read_csr(mstatus);
    mstatus &= ~MSTATUS_MPRV;
    write_csr(mstatus, mstatus);

    printf("doing ECALL (MPRV=0)...\n");
    do_ecall(ECALL_HELLO, 0);

    // Check if MPRV is cleared
    mstatus = read_csr(mstatus);
    if (!(mstatus & MSTATUS_MPRV)) {
        printf("[  OK  ] MPRV cleared\n");
    } else {
        printf("[ FAIL ] MPRV is set!\n");
        global_fail = 1;
    }

    // Check if MPP is set to 00
    if ((mstatus & MSTATUS_MPP_MASK) == MSTATUS_MPP_USER) {
        printf("[  OK  ] MPP is 00\n");
    } else {
        printf("[ FAIL ] MPP is not 00\n");
        global_fail = 1;
    }

    // Set MPRV and do the ECALL again
    mstatus = read_csr(mstatus);
    mstatus |= MSTATUS_MPRV;
    write_csr(mstatus, mstatus);

    printf("doing ECALL (MPRV=1)\n");
    do_ecall(ECALL_HELLO, 0);

    // Check if MPRV is set
    mstatus = read_csr(mstatus);
    if (mstatus & MSTATUS_MPRV) {
        printf("[  OK  ] MPRV is set\n");
    } else {
        printf("[ FAIL ] MPRV is cleared!\n");
        global_fail = 1;
    }

    // Check if MPP is set to 00
    if ((mstatus & MSTATUS_MPP_MASK) == MSTATUS_MPP_USER) {
        printf("[  OK  ] MPP is 00\n");
    } else {
        printf("[ FAIL ] MPP is not 00\n");
        global_fail = 1;
    }

    // Go to user mode, clear MPRV
    mstatus = read_csr(mstatus);
    mstatus &= ~MSTATUS_MPP_MASK;
    mstatus &= ~MSTATUS_MPRV;
    write_csr(mstatus, mstatus);

    void* ptr = (void*)user_main;
    write_csr(mepc, (unsigned long)ptr);
    asm volatile ("mret");

    return 0;
}

__attribute__((noreturn)) void user_main () {

    uint32_t mstatus;

    // We should be now in user mode
    printf("Hello from user_main()\n");

    // Do an ECALL to clear MPRV
    printf("doing ECALL...\n");
    mstatus = do_ecall(ECALL_CLR_MPRV, 0);

    // ECALL returns mstatus value right before returning to user mode.
    // Check if MPP is set to 00 as we called from user mode
    if ((mstatus & MSTATUS_MPP_MASK) == MSTATUS_MPP_USER) {
        printf("[  OK  ] MPP is 00\n");
    } else {
        printf("[ FAIL ] MPP is not 00\n");
        global_fail = 1;
    }

    // Do an ECALL to get mstatus
    printf("doing ECALL...\n");
    mstatus = do_ecall(ECALL_GET_MSTATUS, 0);

    // Check if MPRV was cleared
    if (!(mstatus & MSTATUS_MPRV)) {
        printf("[  OK  ] MPRV was cleared\n");
    } else {
        printf("[ FAIL ] MPRV was set!\n");
        global_fail = 1;
    }

    // Do an ECALL to set MPRV
    printf("doing ECALL...\n");
    mstatus = do_ecall(ECALL_SET_MPRV, 0);

    // ECALL returns mstatus value right before returning to user mode.
    // Check if MPP is set to 00 as we called from user mode
    if ((mstatus & MSTATUS_MPP_MASK) == MSTATUS_MPP_USER) {
        printf("[  OK  ] MPP is 00\n");
    } else {
        printf("[ FAIL ] MPP is not 00\n");
        global_fail = 1;
    }

    // Do an ECALL to get mstatus
    printf("doing ECALL...\n");
    mstatus = do_ecall(ECALL_GET_MSTATUS, 0);

    // Check if MPRV was cleared
    if (!(mstatus & MSTATUS_MPRV)) {
        printf("[  OK  ] MPRV was cleared\n");
    } else {
        printf("[ FAIL ] MPRV was set!\n");
        global_fail = 1;
    }

    // Verify trap data
    unsigned char res = 0xFF;

    printf("traps taken:\n");
    for (unsigned long i=0; i<trap_count; ++i) {
        printf(" %d. mcause=0x%08X mstatus=0x%08X\n", i, trap_data[i].mcause, trap_data[i].mstatus);
    }

    if (trap_count == 6) {

        // mcause
        if (trap_data[0].mcause != MCAUSE_ECALL_M) res = 1;
        if (trap_data[1].mcause != MCAUSE_ECALL_M) res = 1;
        if (trap_data[2].mcause != MCAUSE_ECALL_U) res = 1;
        if (trap_data[3].mcause != MCAUSE_ECALL_U) res = 1;
        if (trap_data[4].mcause != MCAUSE_ECALL_U) res = 1;
        if (trap_data[5].mcause != MCAUSE_ECALL_U) res = 1;

        // MPP
        if ((trap_data[0].mstatus & MSTATUS_MPP_MASK) != MSTATUS_MPP_MACHINE) res = 1;
        if ((trap_data[1].mstatus & MSTATUS_MPP_MASK) != MSTATUS_MPP_MACHINE) res = 1;
        if ((trap_data[2].mstatus & MSTATUS_MPP_MASK) != MSTATUS_MPP_USER)    res = 1;
        if ((trap_data[3].mstatus & MSTATUS_MPP_MASK) != MSTATUS_MPP_USER)    res = 1;
        if ((trap_data[4].mstatus & MSTATUS_MPP_MASK) != MSTATUS_MPP_USER)    res = 1;
        if ((trap_data[5].mstatus & MSTATUS_MPP_MASK) != MSTATUS_MPP_USER)    res = 1;

        // MPRV
        if ( (trap_data[0].mstatus & MSTATUS_MPRV)) res = 1;
        if (!(trap_data[1].mstatus & MSTATUS_MPRV)) res = 1;
        if ( (trap_data[2].mstatus & MSTATUS_MPRV)) res = 1;
        if ( (trap_data[3].mstatus & MSTATUS_MPRV)) res = 1;
        if ( (trap_data[4].mstatus & MSTATUS_MPRV)) res = 1;
        if ( (trap_data[5].mstatus & MSTATUS_MPRV)) res = 1;
    }
    else {
        // Incorrect trap count
        res = 1;
    }

    if (res != 1) {
        printf("[  OK  ] trap sequence verified\n");
    } else {
        printf("[ FAIL ] Incorrect trap sequence!\n");
    }

    if (global_fail) {
        res = 1;
    }

    // Terminate the simulation
    // set the exit code to 0xFF and jump to _finish.
    asm volatile (
        "mv a0, %0\n"
        "j  _finish\n"
        : : "r"(res)
    );

    while (1); // Make the compiler not complain
}
