#include <stdio.h>
#include <stdint.h>
#include <string.h>

#define read_csr(csr) ({ \
    unsigned long res; \
    asm volatile ("csrr %0, %1" : "=r"(res) : "i"(csr)); \
    res; \
})

#define write_csr(csr, val) { \
    asm volatile ("csrw %0, %1" : : "i"(csr), "r"(val)); \
}

#define MISA_U          (1 << 20)

#define CSR_MISA        0x301
#define CSR_MSTATUS     0x300
#define CSR_MCAUSE      0x342
#define CSR_MEPC        0x341

#define CSR_MCOUNTEREN  0x306
#define CSR_CYCLE       0xC00
#define CSR_CYCLEH      0xC80
#define CSR_INSTRET     0xC02
#define CSR_INSTRETH    0xC82

#define ECALL_GET_MCOUNTEREN    0x10
#define ECALL_SET_MCOUNTEREN    0x20

#define MSTATUS_MPP_MASK        (3 << 11)
#define MSTATUS_MPRV            (1 << 17)

#define MCAUSE_ILLEGAL_INSTR    0x2
#define MCAUSE_ECALL_U          0x8
#define MCAUSE_ECALL_M          0xb

#define MCOUNTEREN_CY           (1 << 0)
#define MCOUNTEREN_IR           (1 << 2)

#define TEST_RESULT_SUCCESS     0xFF
#define TEST_RESULT_FAILURE     1

volatile int32_t  global_result = 0;
volatile uint32_t last_trap     = 0xFFFFFFFF;

int32_t do_ecall (uint32_t cmd, uint32_t arg);

int32_t ecall_handler (uint32_t cmd, uint32_t arg) {

    if (cmd == ECALL_GET_MCOUNTEREN) {
        return read_csr(CSR_MCOUNTEREN);
    }
    if (cmd == ECALL_SET_MCOUNTEREN) {
        printf("set mcounteren=0x%08X\n", arg);
        write_csr(CSR_MCOUNTEREN, arg);
        return 0;
    }

    printf("unknown ECALL code 0x%08X\n", cmd);
    global_result = -1;

    return -1;
}

int32_t trap_handler (uint32_t a0, uint32_t a1) {

    uint32_t mstatus = read_csr(CSR_MSTATUS);
    uint32_t mcause  = read_csr(CSR_MCAUSE);
    printf("trap! mstatus=0x%08X, mcause=0x%08X\n", mstatus, mcause);

    // Handle ECALL
    if (mcause == MCAUSE_ECALL_U || mcause == MCAUSE_ECALL_M) {
        return ecall_handler(a0, a1);
    }

    // Store mcause code
    last_trap = mcause;

    return 0;
}

void user_main ();

int main () {
    printf("\nHello VeeR\n");

    // The test requires user mode support
    if ((read_csr(CSR_MISA) & MISA_U) == 0) {
        printf("ERROR: The test requires user mode support. Aborting.\n");
        return -1;
    }

    // Write mcounteren.CY and mcounteren.IR to allow access cycle and instret
    // from user mode
    write_csr(CSR_MCOUNTEREN, MCOUNTEREN_IR | MCOUNTEREN_CY);

    // Go to user mode
    uint32_t mstatus = read_csr(CSR_MSTATUS);
    mstatus &= ~MSTATUS_MPP_MASK; // MPP  = 00 (user)
    mstatus &= ~MSTATUS_MPRV;     // MPRV = 0
    write_csr(CSR_MSTATUS, mstatus);

    void* ptr = (void*)user_main;
    write_csr(CSR_MEPC, (unsigned long)ptr);
    asm volatile ("mret");

    return 0;
}

const char* get_csr_name (int32_t csr) {

    switch (csr)
    {
    case CSR_CYCLE:     return "cycle";
    case CSR_CYCLEH:    return "cycleh";
    case CSR_INSTRET:   return "instret";
    case CSR_INSTRETH:  return "instreth";
    }

    return "";
}

uint32_t read_and_check (int32_t csr, int should_succeed) {

    // Clear trap code
    last_trap = 0xFFFFFFFF;

    // Read the CSR of interest
    uint32_t val = 0;
    switch (csr)
    {
    case CSR_CYCLE:     val = read_csr(CSR_CYCLE);      break;
    case CSR_CYCLEH:    val = read_csr(CSR_CYCLEH);     break;
    case CSR_INSTRET:   val = read_csr(CSR_INSTRET);    break;
    case CSR_INSTRETH:  val = read_csr(CSR_INSTRETH);   break;
    }

    // Check
    if (should_succeed) {
        if (last_trap != 0xFFFFFFFF) {
            printf("[ FAILED ] %s access should succeed, but trap encountered\n", get_csr_name(csr));
            global_result = -1;
            return 0;
        }
    }
    else {
        if (last_trap != MCAUSE_ILLEGAL_INSTR) { // Illegal instruction
            if (last_trap == 0xFFFFFFFF) {
                printf("[ FAILED ] %s access should fail, but no trap encountered\n", get_csr_name(csr));
            } else {
                printf("[ FAILED ] %s access should fail, but with different mcause code\n", get_csr_name(csr));
            }
            global_result = -1;
            return 0;
        }
    }
    
    printf("[   OK   ] %s = %d\n", get_csr_name(csr), val);
    return val;
}

void check_counters (uint64_t cur_cycle, uint64_t cur_instret) {

    static uint64_t prv_cycle   = 0;
    static uint64_t prv_instret = 0;

    // Compute and print diffs
    printf("cycle:   cur %lld, prv %lld, diff %lld\n", cur_cycle,   prv_cycle,   cur_cycle   - prv_cycle);
    printf("instret: cur %lld, prv %lld, diff %lld\n", cur_instret, prv_instret, cur_instret - prv_instret);

    // Check diffs, counters should always increase monotonically
    if (cur_cycle > prv_cycle && cur_instret > prv_instret) {
        printf("[   OK   ] counters ok\n");
    } else {
        printf("[ FAILED ] counters do not increase!\n");
        global_result = -1;
    }

    // Store previous value
    prv_cycle   = cur_cycle;
    prv_instret = cur_instret;
}

__attribute__((noreturn)) void user_main () {
    printf("\nHello from user_main()\n");

    uint32_t cycle_l;
    uint32_t cycle_h;
    uint32_t instret_l;
    uint32_t instret_h;

    uint64_t cycle;
    uint64_t instret;

    // User-mode perf counters should be accessible. Read them and check if
    // they operate correctly
    printf("Testing counters operation...\n");
    for (int i=0; i<2; ++i) {
        cycle_h   = read_and_check(CSR_CYCLEH,   1);
        cycle_l   = read_and_check(CSR_CYCLE,    1);
        instret_h = read_and_check(CSR_INSTRETH, 1);
        instret_l = read_and_check(CSR_INSTRET,  1);

        cycle   = (((uint64_t)cycle_h)   << 32) | cycle_l;
        instret = (((uint64_t)instret_h) << 32) | instret_l;
        check_counters(cycle, instret);
    }

    // For all combinations of mcounteren CY and IR set their value and check
    // if counter accesses are allowed / denied accordingly.
    printf("Testing counters access...\n");
    for (int i=0; i<4; ++i) {
        int cy = (i & 1) != 0;
        int ir = (i & 2) != 0;

        // Set access rights. Do that by calling ECALL handler which does the
        // actual job since the CSR is not writable from user mode.
        printf("setting CY=%d, IR=%d in mcounteren\n", cy, ir);
        do_ecall(ECALL_SET_MCOUNTEREN, ir * MCOUNTEREN_IR | cy * MCOUNTEREN_CY);

        // Test access, ignore values
        cycle_h   = read_and_check(CSR_CYCLEH,   cy);
        cycle_l   = read_and_check(CSR_CYCLE,    cy);
        instret_h = read_and_check(CSR_INSTRETH, ir);
        instret_l = read_and_check(CSR_INSTRET,  ir);
    }

    // Terminate the simulation
    // set the exit code to 0xFF / 0x01 and jump to _finish.
    uint32_t res = (global_result == 0) ? TEST_RESULT_SUCCESS :
                                          TEST_RESULT_FAILURE;
    asm volatile (
        "mv a0, %0\n"
        "j  _finish\n"
        : : "r"(res)
    );

    while (1); // Make compiler not complain
}
