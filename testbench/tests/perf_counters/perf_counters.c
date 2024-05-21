#include <stdio.h>
#include <stdint.h>
#include <string.h>

// Clear the destination reg before reading so that when the read fails the
// returned value is 0
#define read_csr(csr) ({ \
    unsigned long res; \
    asm volatile ( \
        "li %0, 0\n" \
        "csrr %0, %1" \
        : "=r"(res) : "i"(csr) \
    ); \
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

#define CSR_HPMCOUNTER3         0xC03
#define CSR_HPMCOUNTER3H        0xC83
#define CSR_HPMCOUNTER4         0xC04
#define CSR_HPMCOUNTER4H        0xC84
#define CSR_HPMCOUNTER5         0xC05
#define CSR_HPMCOUNTER5H        0xC85
#define CSR_HPMCOUNTER6         0xC06
#define CSR_HPMCOUNTER6H        0xC86

#define CSR_MHPMEVENT3          0x323
#define CSR_MHPMEVENT4          0x324
#define CSR_MHPMEVENT5          0x325
#define CSR_MHPMEVENT6          0x326

#define ECALL_GET_MCOUNTEREN    0x10
#define ECALL_SET_MCOUNTEREN    0x20

#define MSTATUS_MPP_MASK        (3 << 11)
#define MSTATUS_MPRV            (1 << 17)

#define MCAUSE_ILLEGAL_INSTR    0x2
#define MCAUSE_ECALL_U          0x8
#define MCAUSE_ECALL_M          0xb

#define MCOUNTEREN_CY           (1 << 0)
#define MCOUNTEREN_IR           (1 << 2)
#define MCOUNTEREN_HPM3         (1 << 3)
#define MCOUNTEREN_HPM4         (1 << 4)
#define MCOUNTEREN_HPM5         (1 << 5)
#define MCOUNTEREN_HPM6         (1 << 6)
#define MCOUNTEREN_ALL          0x7D
#define MCOUNTEREN_NONE         0x00

#define TEST_RESULT_SUCCESS     0xFF
#define TEST_RESULT_FAILURE     1

#define VEER_EVT_INSTR_COMMITTED_16      5
#define VEER_EVT_INSTR_COMMITTED_32      6
#define VEER_EVT_BRANCHES_COMMITTED      24
#define VEER_EVT_BRANCHES_MISPREDICTED   25

#define COUNTER_COUNT           6

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

    // Setup VeeR performance counter events. See VeeR EL2 manual table 7-1
    // for the complete event list and their codes.
    write_csr(CSR_MHPMEVENT3, VEER_EVT_INSTR_COMMITTED_16);
    write_csr(CSR_MHPMEVENT4, VEER_EVT_INSTR_COMMITTED_32);
    write_csr(CSR_MHPMEVENT5, VEER_EVT_BRANCHES_COMMITTED);
    write_csr(CSR_MHPMEVENT6, VEER_EVT_BRANCHES_MISPREDICTED);

    // Write mcounteren to allow counter access from user_mode
    write_csr(CSR_MCOUNTEREN, MCOUNTEREN_ALL);

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
    case CSR_CYCLE:         return "cycle";
    case CSR_CYCLEH:        return "cycleh";
    case CSR_INSTRET:       return "instret";
    case CSR_INSTRETH:      return "instreth";
    case CSR_HPMCOUNTER3:   return "hpmcounter3";
    case CSR_HPMCOUNTER3H:  return "hpmcounter3h";
    case CSR_HPMCOUNTER4:   return "hpmcounter4";
    case CSR_HPMCOUNTER4H:  return "hpmcounter4h";
    case CSR_HPMCOUNTER5:   return "hpmcounter5";
    case CSR_HPMCOUNTER5H:  return "hpmcounter5h";
    case CSR_HPMCOUNTER6:   return "hpmcounter6";
    case CSR_HPMCOUNTER6H:  return "hpmcounter6h";
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
    case CSR_CYCLE:         val = read_csr(CSR_CYCLE);        break;
    case CSR_CYCLEH:        val = read_csr(CSR_CYCLEH);       break;
    case CSR_INSTRET:       val = read_csr(CSR_INSTRET);      break;
    case CSR_INSTRETH:      val = read_csr(CSR_INSTRETH);     break;
    case CSR_HPMCOUNTER3:   val = read_csr(CSR_HPMCOUNTER3);  break;
    case CSR_HPMCOUNTER3H:  val = read_csr(CSR_HPMCOUNTER3H); break;
    case CSR_HPMCOUNTER4:   val = read_csr(CSR_HPMCOUNTER4);  break;
    case CSR_HPMCOUNTER4H:  val = read_csr(CSR_HPMCOUNTER4H); break;
    case CSR_HPMCOUNTER5:   val = read_csr(CSR_HPMCOUNTER5);  break;
    case CSR_HPMCOUNTER5H:  val = read_csr(CSR_HPMCOUNTER5H); break;
    case CSR_HPMCOUNTER6:   val = read_csr(CSR_HPMCOUNTER6);  break;
    case CSR_HPMCOUNTER6H:  val = read_csr(CSR_HPMCOUNTER6H); break;
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

uint64_t read_and_check64(int32_t csr_base, int should_succeed) {
    // CSRs for high 32-bit parts of counters have the same addresses but
    // logically or-ed with 0x80.
    uint32_t hi = read_and_check(csr_base | 0x80, should_succeed);
    uint32_t lo = read_and_check(csr_base,        should_succeed);
    return (((uint64_t)hi) << 32) | lo;
}

void check_counters (const uint64_t* cur_counters) {

    const char* counter_names[COUNTER_COUNT] = {
        "cycle  ",
        "instret",
        "hpm3   ",
        "hpm4   ",
        "hpm5   ",
        "hpm6   "
    };

    static uint64_t prv_counters [COUNTER_COUNT] = {0};

    // Compute and print diffs
    int counters_ok = 1;
    for (int i=0; i<COUNTER_COUNT; ++i) {

        int64_t diff = cur_counters[i] - prv_counters[i];
        if (diff < 0) counters_ok = 0;

        printf("%s: cur %lld, prv %lld, diff %lld\n",
            counter_names[i], cur_counters[i], prv_counters[i], diff);
    }

    // Check diffs, counters should always increase monotonically
    if (counters_ok) {
        printf("[   OK   ] counters ok\n");
    } else {
        printf("[ FAILED ] counter(s) do not increase!\n");
        global_result = -1;
    }

    // Store previous values
    memcpy(prv_counters, cur_counters, sizeof(uint64_t) * COUNTER_COUNT);
}

__attribute__((noreturn)) void user_main () {
    printf("\nHello from user_main()\n");

    uint32_t cnt_l;
    uint32_t cnt_h;
    uint64_t counters[COUNTER_COUNT];

    const int32_t base_csrs [] = {
        CSR_CYCLE,
        CSR_INSTRET,
        CSR_HPMCOUNTER3,
        CSR_HPMCOUNTER4,
        CSR_HPMCOUNTER5,
        CSR_HPMCOUNTER6
    };

    const uint32_t access_cases [] = {
        MCOUNTEREN_NONE,
        MCOUNTEREN_CY,
        MCOUNTEREN_IR,
        MCOUNTEREN_HPM3,
        MCOUNTEREN_HPM4,
        MCOUNTEREN_HPM5,
        MCOUNTEREN_HPM6
    };

    // User-mode perf counters should be accessible. Read them and check if
    // they operate correctly
    for (int i=0; i<2; ++i) {
        printf("Testing counters operation (round %d)...\n", i + 1);

        for (int j=0; j<COUNTER_COUNT; ++j) {
            counters[j] = read_and_check64(base_csrs[j], 1);
        }
        check_counters(counters);

        printf("\n");
    }

    // Check if individual bits of mcounteren control CSR access correctly
    printf("Testing counters access...\n");
    for (int i=0; i < sizeof(access_cases) / sizeof(access_cases[0]); ++i) {

        // Set access rights. Do that by calling ECALL handler which does the
        // actual job since the CSR is not writable from user mode.
        uint32_t access = access_cases[i];
        do_ecall(ECALL_SET_MCOUNTEREN, access);

        // Test access, ignore values
        read_and_check64(CSR_CYCLE,       (access & MCOUNTEREN_CY)   != 0);
        read_and_check64(CSR_INSTRET,     (access & MCOUNTEREN_IR)   != 0);
        read_and_check64(CSR_HPMCOUNTER3, (access & MCOUNTEREN_HPM3) != 0);
        read_and_check64(CSR_HPMCOUNTER4, (access & MCOUNTEREN_HPM4) != 0);
        read_and_check64(CSR_HPMCOUNTER5, (access & MCOUNTEREN_HPM5) != 0);
        read_and_check64(CSR_HPMCOUNTER6, (access & MCOUNTEREN_HPM6) != 0);

        printf("\n");
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
