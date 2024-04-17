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

// ============================================================================

extern uint32_t tohost;

void trigger_nmi_irq (int state) {
    uint32_t cmd = (state) ? (0x83 | (1 << 8)) : (0x82 | (1 << 8));
    tohost = cmd;
}

void trigger_timer_irq (int state) {
    uint32_t cmd = (state) ? (0x83 | (2 << 8)) : (0x82 | (2 << 8));
    tohost = cmd;
}

void trigger_soft_irq (int state) {
    uint32_t cmd = (state) ? (0x83 | (4 << 8)) : (0x82 | (4 << 8));
    tohost = cmd;
}

void trigger_ext_irq (int state, int irq) {
    uint32_t cmd = (state) ? (0x81 | (irq << 8)) : (0x80 | (irq << 8));
    tohost = cmd;
}

void release_all_irqs () {
    tohost = 0x90;
}

// ============================================================================

volatile uint32_t trap_causes[32];
volatile uint32_t trap_count = 0;

void trap_handler () {

    uint32_t mstatus = read_csr(mstatus);
    uint32_t mcause  = read_csr(mcause);
    printf("trap! mstatus=0x%08X, mcause=0x%08X\n", mstatus, mcause);

    // Release interrupt lines
    release_all_irqs();

    // Store cause
    if (trap_count < (sizeof(trap_causes) / sizeof(trap_causes[0]))) {
        trap_causes[trap_count++] = mcause;
    }
}

// ============================================================================

void user_main ();

__attribute__((noreturn)) void main () {
    printf("Hello VeeR\n");

    // Enable interrupts
    unsigned long mie = read_csr(mie);
    mie |= 0x888; // MEIE, MTIE, MSIE = 1
    write_csr(mie, mie);

    // ..............................
    // Set mstatus.MIE to 0. This should disable interrupts in M mode
    printf("Machine mode, MIE=0\n");

    unsigned long mstatus = read_csr(mstatus);
    mstatus &= ~0x08; // MIE = 0
    write_csr(mstatus, mstatus);

    // Timer IRQ
    trigger_timer_irq(1);
    printf(" timer irq triggered\n");

    // Soft IRQ
    trigger_soft_irq(1);
    printf(" soft IRQ triggered\n");

    // Ext IRQ
    trigger_ext_irq(1, 1);
    printf(" ext IRQ triggered\n");

    // No exceptions should have occurred
    // Release interrupt lines
    release_all_irqs();

    // ..............................
    // Set mstatus.MIE to 1. This should enable interrupts in M mode
    printf("Machine mode, MIE=1\n");

    mstatus  = read_csr(mstatus);
    mstatus |= 0x08; // MIE = 1
    write_csr(mstatus, mstatus);

    // Timer IRQ
    trigger_timer_irq(1);
    printf(" timer irq triggered\n");

    // Soft IRQ
    trigger_soft_irq(1);
    printf(" soft IRQ triggered\n");

    // Ext IRQ
    trigger_ext_irq(1, 1);
    printf(" ext IRQ triggered\n");

    // Exceptions should have occurred and got recorded.
    // Release interrupt lines
    release_all_irqs();

    // ..............................
    // Set mstatus.MPIE to 0 and go to user mode. On the mode change MPIE
    // should be copied to MIE. This should not prevent interrupts from
    // occurring.
    printf("Going to user mode, MPIE=0\n");

    mstatus  = read_csr(mstatus);
    mstatus &= ~0x80; // MPIE = 0
    write_csr(mstatus, mstatus);

    // Go to user mode
    mstatus = read_csr(mstatus);
    mstatus &= ~(3 << 11);  // MPP  = 00 (user)
    mstatus &= ~(1 << 17);  // MPRV = 0
    write_csr(mstatus, mstatus);

    void* ptr = (void*)user_main;
    write_csr(mepc, (unsigned long)ptr);
    asm volatile ("mret");
}

__attribute__((noreturn)) void user_main () {
    printf("Hello VeeR in user mode\n");

    // ..............................
    // mstatus.MIE should be 0 (we can't check it from user mode) but interrupts
    // should trigger.

    // Timer IRQ
    trigger_timer_irq(1);
    printf(" timer irq triggered\n");

    // Soft IRQ
    trigger_soft_irq(1);
    printf(" soft IRQ triggered\n");

    // Ext IRQ
    trigger_ext_irq(1, 1);
    printf(" ext IRQ triggered\n");

    // Exceptions should have occurred and got recorded.
    // Release interrupt lines
    release_all_irqs();

    // ..............................
    // Verify trap causes
    unsigned char res = 0xFF; // success

    // Report traps
    printf("traps taken: %d\n", trap_count);
    for (uint32_t i=0; i<trap_count; ++i) {
        printf(" %d. 0x%08X\n", i, trap_causes[i]);
    }

    // Check traps. Should be:
    //  M timer
    //  M soft int
    //  M timer
    //  M soft int
    const uint32_t golden_trap_causes[] = {0x80000007, 0x80000003, 0x80000007, 0x80000003};
    const uint32_t golden_trap_count    = sizeof(golden_trap_causes) / sizeof(golden_trap_causes[0]);

    if (trap_count == golden_trap_count) {
        for (uint32_t i=0; i<trap_count; ++i) {
            if (trap_causes[i] != golden_trap_causes[i]) {
                res = 1;
                break;
            }
        }
    }
    else {
        res = 1; // failure
    }

    // Terminate the simulation
    // set the exit code to 0xFF and jump to _finish.
    asm volatile (
        "mv a0, %0\n"
        "j  _finish\n"
        : : "r"(res)
    );
}
