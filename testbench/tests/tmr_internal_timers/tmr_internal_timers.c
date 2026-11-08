#include <stdio.h>
#include <stdint.h>

// ============================================================================

#define read_csr(csr) ({ \
    unsigned long res; \
    asm volatile ("csrr %0, " #csr : "=r"(res)); \
    res; \
})

#define write_csr(csr, val) { \
    asm volatile ("csrw " #csr ", %0" : : "r"(val)); \
}

#define MSTATUS_MPP_MASK    (3 << 11)
#define MSTATUS_MPP_MACHINE (3 << 11)
#define MSTATUS_MPP_USER    (0 << 11)
#define MSTATUS_MPP_MPRV    (1 << 17)
#define MSTATUS_MIE         (1 << 3)
#define MSTATUS_MPIE        (1 << 7)

#define MIE_MITIP0          (1 << 29)
#define MIE_MITIP1          (1 << 28)

#define MCAUSE_MITIP0       0x8000001D
#define MCAUSE_MITIP1       0x8000001C

#define TEST_RESULT_SUCCESS 0xFF
#define TEST_RESULT_FAILURE 1

// ============================================================================

#define CMD_SET_FAULTY_CORE 0xB0
#define CMD_RECOVERY        0xB1

extern uint32_t tohost;

void set_faulty_core (int core) {
    tohost = (core << 8) | CMD_SET_FAULTY_CORE;
}

void start_recovery (int run) {
    tohost = (run << 8) | CMD_RECOVERY;
}

// ============================================================================

void trap_handler () {

    uint32_t mstatus = read_csr(mstatus);
    uint32_t mcause  = read_csr(mcause);
    uint32_t mepc    = read_csr(mepc);

    printf("trap! mstatus=0x%08X, mcause=0x%08X, mepc=0x%08X\n", mstatus, mcause, mepc);
}

void nmi_handler () {
    // Handle NMIs as regular traps. For purpose of this test it is sufficient
    trap_handler();
}

// ============================================================================

#define mcpc    0x7C2

#define mitcnt0 0x7D2
#define mitcnt1 0x7D5
#define mitb0   0x7D3
#define mitb1   0x7D6
#define mitctl0 0x7D4
#define mitctl1 0x7D7
#define MITCTL_ENABLE     (1 << 0)
#define MITCTL_HALT_EN    (1 << 1)
#define MITCTL_PAUSE_EN   (1 << 2)
#define MITCTL_CASCADE    (1 << 3)

uint32_t timer0_test (int run_recovery) {
    uint32_t tmp = 0;
    printf("Run timer 0, with recovery %d\n", run_recovery);
    write_csr(mitcnt0, 0);
    write_csr(mitb0,   0xFFFFFFFF);
    write_csr(mitctl0, MITCTL_ENABLE | MITCTL_PAUSE_EN); // Enable and count while paused
    set_faulty_core(run_recovery);
    start_recovery(run_recovery);
    write_csr(mcpc, 0x1FF);
    tmp = read_csr(mitcnt0);
    write_csr(mitctl0, 0);
    return tmp;
}

uint32_t timer1_test (int run_recovery) {
    uint32_t tmp = 0;
    printf("Run timer 1, with recovery %d\n", run_recovery);
    write_csr(mitcnt1, 0);
    write_csr(mitb1,   0xFFFFFFFF);
    write_csr(mitctl1, MITCTL_ENABLE | MITCTL_PAUSE_EN); // Enable and count while paused
    set_faulty_core(run_recovery);
    start_recovery(run_recovery);
    write_csr(mcpc, 0x1FF);
    tmp = read_csr(mitcnt1);
    write_csr(mitctl1, 0);
    return tmp;
}

int main () {
    printf("Hello VeeR\n");

    uint32_t time_taken[2][2] = {{0, 0}, {0, 0}};

    for (int j=0; j<2; ++j) {
        for (int i=0; i<10; ++i) {
            time_taken[0][j] += timer0_test(j);
        }
        time_taken[0][j] = time_taken[0][j] / 10;
    }

    for (int j=0; j<2; ++j) {
        for (int i=0; i<10; ++i) {
            time_taken[1][j] += timer1_test(j);
        }
        time_taken[1][j] = time_taken[1][j] / 10;
    }

    for (int i=0; i<2; ++i) {
        if (time_taken[i][0] >= time_taken[i][1]) {
            printf("Error: Timer %d took less time during recovery than in normal mode! (%d) vs (%d)\n", i, time_taken[i][0], time_taken[i][1]);
            return -1;
        }
    }

    return 0;
}
