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

#define MISA_U (1 << 20)

#define MSTATUS_MPP_MASK    (3 << 11)
#define MSTATUS_MPP_MACHINE (3 << 11)
#define MSTATUS_MPP_USER    (0 << 11)
#define MSTATUS_MPP_MPRV    (1 << 17)
#define MSTATUS_MIE         (1 << 3)
#define MSTATUS_MPIE        (1 << 7)

#define MIE_MEIE            (1 << 11)
#define MIE_MTIE            (1 << 7)
#define MIE_MSIE            (1 << 3)

#define MCAUSE_NMI          0x0
#define MCAUSE_TIMER_M      0x80000007
#define MCAUSE_SOFTINT_M    0x80000003

#define TEST_RESULT_SUCCESS 0xFF
#define TEST_RESULT_FAILURE 1

// ============================================================================

#define CMD_EXT_IRQ_CLR     0x80
#define CMD_EXT_IRQ_SET     0x81
#define CMD_CORE_IRQ_CLR    0x82
#define CMD_CORE_IRQ_SET    0x83
#define CMD_IRQ_CLR_ALL     0x90

#define CORE_IRQ_NMI        (1 << 8)
#define CORE_IRQ_TIMER      (2 << 8)
#define CORE_IRQ_SOFT       (4 << 8)

extern uint32_t tohost;

void trigger_nmi_irq (int state) {
    uint32_t cmd = (state) ? CMD_CORE_IRQ_SET : CMD_CORE_IRQ_CLR;
    tohost = cmd | CORE_IRQ_NMI;
}

void trigger_timer_irq (int state) {
    uint32_t cmd = (state) ? CMD_CORE_IRQ_SET : CMD_CORE_IRQ_CLR;
    tohost = cmd | CORE_IRQ_TIMER;
}

void trigger_soft_irq (int state) {
    uint32_t cmd = (state) ? CMD_CORE_IRQ_SET : CMD_CORE_IRQ_CLR;
    tohost = cmd | CORE_IRQ_SOFT;
}

void trigger_ext_irq (int state, int irq) {
    uint32_t cmd = (state) ? CMD_EXT_IRQ_SET : CMD_EXT_IRQ_CLR;
    tohost = cmd | (irq << 8);
}

void release_all_irqs () {
    tohost = CMD_IRQ_CLR_ALL;
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

    // Release interrupt lines
    release_all_irqs();

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
    mie |= MIE_MEIE | MIE_MTIE | MIE_MSIE;
    write_csr(mie, mie);

    // ..............................
    // Set mstatus.MIE to 0. This should disable interrupts in M mode
    printf("Machine mode, MIE=0\n");

    unsigned long mstatus = read_csr(mstatus);
    mstatus &= ~MSTATUS_MIE;
    write_csr(mstatus, mstatus);

    // NMI
    trigger_nmi_irq(1);
    printf(" NMI triggered\n");

    // Timer IRQ
    trigger_timer_irq(1);
    printf(" timer irq triggered\n");

    // Soft IRQ
    trigger_soft_irq(1);
    printf(" soft IRQ triggered\n");

    // No exceptions should have occurred
    // Release interrupt lines
    release_all_irqs();

    // ..............................
    // Set mstatus.MIE to 1. This should enable interrupts in M mode
    printf("Machine mode, MIE=1\n");

    mstatus  = read_csr(mstatus);
    mstatus |= MSTATUS_MIE;
    write_csr(mstatus, mstatus);

    // NMI
    trigger_nmi_irq(1);
    printf(" NMI triggered\n");

    // Timer IRQ
    trigger_timer_irq(1);
    printf(" timer irq triggered\n");

    // Soft IRQ
    trigger_soft_irq(1);
    printf(" soft IRQ triggered\n");

    // Exceptions should have occurred and got recorded.
    // Release interrupt lines
    release_all_irqs();

    // ..............................
    // User mode not supported
    if ((read_csr(misa) & MISA_U) == 0) {
        printf("WARNING: User mode not supported\n");

        // Report traps
        printf("traps taken: %d\n", trap_count);
        for (unsigned long i=0; i<trap_count; ++i) {
            printf(" %d. mcause=0x%08X mstatus=0x%08X\n", i, trap_data[i].mcause, trap_data[i].mstatus);
        }

        // Check traps. Should be:
        const uint32_t golden_trap_causes[] = {
            MCAUSE_NMI,         // NMI
            MCAUSE_NMI,         // NMI
            MCAUSE_TIMER_M,     // M timer
            MCAUSE_SOFTINT_M,   // M soft int
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

    // ..............................
    // Set mstatus.MPIE to 0 and go to user mode. On the mode change MPIE
    // should be copied to MIE. This should not prevent interrupts from
    // occurring.
    printf("Going to user mode, MPIE=0\n");

    mstatus  = read_csr(mstatus);
    mstatus &= ~MSTATUS_MPIE;
    write_csr(mstatus, mstatus);

    // Go to user mode
    mstatus = read_csr(mstatus);
    mstatus &= ~MSTATUS_MPP_MASK; // MPP  = 00 (user)
    mstatus &= ~MSTATUS_MPP_MPRV; // MPRV = 0
    write_csr(mstatus, mstatus);

    void* ptr = (void*)user_main;
    write_csr(mepc, (unsigned long)ptr);
    asm volatile ("mret");

    return 0;
}

__attribute__((noreturn)) void user_main () {
    printf("Hello VeeR in user mode\n");

    // ..............................
    // mstatus.MIE should be 0 (we can't check it from user mode) but interrupts
    // should trigger.

    // NMI
    trigger_nmi_irq(1);
    printf(" NMI triggered\n");

    // Timer IRQ
    trigger_timer_irq(1);
    printf(" timer irq triggered\n");

    // Soft IRQ
    trigger_soft_irq(1);
    printf(" soft IRQ triggered\n");

    // Exceptions should have occurred and got recorded.
    // Release interrupt lines
    release_all_irqs();

    // ..............................
    // Verify trap causes
    unsigned char res = TEST_RESULT_SUCCESS; // success

    // Report traps
    printf("traps taken:\n");
    for (unsigned long i=0; i<trap_count; ++i) {
        printf(" %d. mcause=0x%08X mstatus=0x%08X\n", i, trap_data[i].mcause, trap_data[i].mstatus);
    }

    // Check traps. Should be:
    const uint32_t golden_trap_causes[] = {
        MCAUSE_NMI,         // NMI
        MCAUSE_NMI,         // NMI
        MCAUSE_TIMER_M,     // M timer
        MCAUSE_SOFTINT_M,   // M soft int
        MCAUSE_NMI,         // NMI
        MCAUSE_TIMER_M,     // M timer
        MCAUSE_SOFTINT_M,   // M soft int
    };
    const uint32_t golden_trap_count = sizeof(golden_trap_causes) /
                                       sizeof(golden_trap_causes[0]);

    if (trap_count == golden_trap_count) {
        for (uint32_t i=0; i<trap_count; ++i) {

            // Check causes
            if (trap_data[i].mcause != golden_trap_causes[i]) {
                res = TEST_RESULT_FAILURE;
                break;
            }

            // Check modes
            if ((trap_data[0].mstatus & MSTATUS_MPP_MASK) != MSTATUS_MPP_MACHINE) res = TEST_RESULT_FAILURE;
            if ((trap_data[1].mstatus & MSTATUS_MPP_MASK) != MSTATUS_MPP_MACHINE) res = TEST_RESULT_FAILURE;
            if ((trap_data[2].mstatus & MSTATUS_MPP_MASK) != MSTATUS_MPP_MACHINE) res = TEST_RESULT_FAILURE;
            if ((trap_data[3].mstatus & MSTATUS_MPP_MASK) != MSTATUS_MPP_MACHINE) res = TEST_RESULT_FAILURE;
            if ((trap_data[4].mstatus & MSTATUS_MPP_MASK) != MSTATUS_MPP_USER)    res = TEST_RESULT_FAILURE;
            if ((trap_data[5].mstatus & MSTATUS_MPP_MASK) != MSTATUS_MPP_USER)    res = TEST_RESULT_FAILURE;
            if ((trap_data[6].mstatus & MSTATUS_MPP_MASK) != MSTATUS_MPP_USER)    res = TEST_RESULT_FAILURE;
        }
    }
    else {
        res = TEST_RESULT_FAILURE; // failure
    }

    // Terminate the simulation
    // set the exit code to 0xFF and jump to _finish.
    asm volatile (
        "mv a0, %0\n"
        "j  _finish\n"
        : : "r"(res)
    );

    // Make the compiler not complain
    while (1);
}
