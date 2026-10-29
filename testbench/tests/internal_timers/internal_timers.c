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

void trigger_internal_timer0_irq(void) {
    uint32_t tmp = 0;
    write_csr(mitcnt0, tmp);
    tmp = 0x1FF;
    write_csr(mitb0, tmp);
    tmp = MITCTL_ENABLE | MITCTL_PAUSE_EN;  // Enable and count while paused
    write_csr(mitctl0, tmp);                // Enable and count while paused
    tmp = 0x2FF;
    write_csr(mcpc, tmp);
}

void trigger_internal_timer1_irq(void) {
    uint32_t tmp = 0;
    write_csr(mitcnt1, tmp);
    tmp = 0x1FF;
    write_csr(mitb1, tmp);
    tmp = MITCTL_ENABLE | MITCTL_PAUSE_EN;  // Enable and count while paused
    write_csr(mitctl1, tmp);                // Enable and count while paused
    tmp = 0x2FF;
    write_csr(mcpc, tmp);
}

void trigger_cascade_internal_timer_irq(void) {
    uint32_t tmp = 0;
    write_csr(mitcnt0, tmp);
    write_csr(mitcnt1, tmp);
    tmp = 0x1F;
    write_csr(mitb0, tmp);
    tmp = 0x10;
    write_csr(mitb1, tmp);
    tmp = MITCTL_ENABLE | MITCTL_PAUSE_EN;                  // Enable and count while paused
    write_csr(mitctl0, tmp);
    tmp = MITCTL_ENABLE | MITCTL_PAUSE_EN | MITCTL_CASCADE; // Enable, cascade and count while paused
    write_csr(mitctl1, tmp);
    tmp = 0x2FF;
    write_csr(mcpc, tmp);
}

void disable_timers(void) {
    write_csr(mitcnt0, 0);
    write_csr(mitcnt1, 0);
}

// ============================================================================

struct trap_data_t {
    uint32_t    mcause;
    uint32_t    mstatus;
};

volatile struct trap_data_t trap_data[32];
volatile uint32_t trap_count = 0;

void trap_handler () {

    uint32_t mstatus = read_csr(mstatus);
    uint32_t mcause  = read_csr(mcause);
    uint32_t mepc    = read_csr(mepc);

    // Disable timers
    disable_timers();

    printf("trap! mstatus=0x%08X, mcause=0x%08X, mepc=0x%08X\n", mstatus, mcause, mepc);

    // Store trap data
    if (trap_count < (sizeof(trap_data) / sizeof(trap_data[0]))) {
        trap_data[trap_count].mcause  = mcause;
        trap_data[trap_count].mstatus = mstatus;
        trap_count++;
    }
}

void nmi_handler () {
    // Handle NMIs as regular traps. For purpose of this test it is sufficient
    trap_handler();
}

// ============================================================================

void user_main ();

int main () {
    printf("Hello VeeR\n");

    // Enable interrupts
    unsigned long mie = read_csr(mie);
    mie |= MIE_MITIP0 | MIE_MITIP1;
    write_csr(mie, mie);

    // ..............................
    // Set mstatus.MIE to 0. This should disable interrupts in M mode
    printf("Machine mode, MIE=0\n");

    unsigned long mstatus = read_csr(mstatus);
    mstatus &= ~MSTATUS_MIE;
    write_csr(mstatus, mstatus);

    // Internal timer 0
    trigger_internal_timer0_irq();
    printf("Internal Timer0 triggered\n");

    // Internal timer 1
    trigger_internal_timer1_irq();
    printf("Internal Timer1 triggered\n");

    // Internal timer cascade
    mie = read_csr(mie);
    mie &= ~MIE_MITIP0;
    write_csr(mie, mie);
    trigger_cascade_internal_timer_irq();
    printf("Cascade internal timer triggered\n");

    // Disable timers
    disable_timers();

    mie = read_csr(mie);
    mie |= MIE_MITIP0 | MIE_MITIP1;
    write_csr(mie, mie);
    // ..............................
    // Set mstatus.MIE to 1. This should enable interrupts in M mode
    printf("Machine mode, MIE=1\n");

    mstatus  = read_csr(mstatus);
    mstatus |= MSTATUS_MIE;
    write_csr(mstatus, mstatus);

    // Internal timer 0
    trigger_internal_timer0_irq();
    printf("Internal Timer0 triggered\n");

    // Internal timer 1
    trigger_internal_timer1_irq();
    printf("Internal Timer1 triggered\n");

    // Internal timer cascade
    mie = read_csr(mie);
    mie &= ~MIE_MITIP0;
    write_csr(mie, mie);
    trigger_cascade_internal_timer_irq();
    printf("Cascade internal timer triggered\n");

    // Report traps
    printf("traps taken: %d\n", trap_count);
    for (unsigned long i=0; i<trap_count; ++i) {
        printf(" %d. mcause=0x%08X mstatus=0x%08X\n", i, trap_data[i].mcause, trap_data[i].mstatus);
    }

    // Check traps. Should be:
    const uint32_t golden_trap_causes[] = {
        MCAUSE_MITIP0,      // Internal timer 0
        MCAUSE_MITIP1,      // Internal timer 1
        MCAUSE_MITIP1,      // Cascade internal timers 0 and 1
    };
    const uint32_t golden_trap_count = sizeof(golden_trap_causes) /
                                       sizeof(golden_trap_causes[0]);

    if (trap_count == golden_trap_count) {
        for (uint32_t i=0; i<trap_count; ++i) {
            if (trap_data[i].mcause != golden_trap_causes[i]) {
                return -1;
            }
        }
    }
    else {
        return -1;
    }

    return 0;
}
