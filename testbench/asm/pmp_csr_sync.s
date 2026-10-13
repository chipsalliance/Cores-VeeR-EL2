// Check that a load/store immediately following a PMP CSR write is checked
// against the new PMP configuration (https://github.com/chipsalliance/Cores-VeeR-EL2/issues/557).
// Locked entries (L=1) constrain M-mode, so the test runs with and without user mode.

#include "common.s"

#define LOAD_WINDOW        0xf0040100      // DCCM
#define LOAD_WINDOW_NAPOT  0x3c01005f      // pmpaddr value: NAPOT, 256 B at LOAD_WINDOW
#define STORE_WINDOW       0xf0040200      // DCCM
#define STORE_WINDOW_NAPOT 0x3c01009f      // pmpaddr value: NAPOT, 256 B at STORE_WINDOW

#define CFG_OPEN           0x00000018      // entry 0: A=NAPOT, L=0 (does not constrain M-mode)
#define CFG_LOAD_LOCKED    0x00000098      // entry 0: A=NAPOT, L=1, R=W=X=0
#define CFG_STORE_LOCKED   0x00009998      // entry 1: A=NAPOT, L=1, R=1, W=X=0 (entry 0 unchanged)

// a0 = pmpcfg0 value, a1 = 1 if the load must trap
pmp_write_then_load:
    csrw pmpcfg0, a0
    lw   x6, 0(s5)                         // first instruction after the PMP write
    beqz a1, 1f
    j    fail_if_not_serviced              // reached only if the load did not trap
1:  ret

// a0 = pmpcfg0 value, store must trap
pmp_write_then_store:
    csrw pmpcfg0, a0
    sw   x0, 0(s6)                         // first instruction after the PMP write
    j    fail_if_not_serviced              // reached only if the store did not trap

main:
    li   s5, LOAD_WINDOW
    li   s6, STORE_WINDOW
    li   t0, LOAD_WINDOW_NAPOT
    csrw pmpaddr0, t0
    li   t0, STORE_WINDOW_NAPOT
    csrw pmpaddr1, t0

    // warm-up: an unlocked entry does not constrain M-mode, must not trap
    li   a0, CFG_OPEN
    li   a1, 0
    call pmp_write_then_load

    // lock entry 0 with no permissions, the next load must fault
    li   x4, 5                             // expected mcause: load access fault
    li   x5, 3                             // expected mscause: PMP/MPU fault
    li   a0, CFG_LOAD_LOCKED
    li   a1, 1
    call pmp_write_then_load

    // lock entry 1 read-only, the next store must fault
    li   x4, 7                             // expected mcause: store access fault
    li   x5, 3                             // expected mscause: PMP/MPU fault
    li   a0, CFG_STORE_LOCKED
    call pmp_write_then_store

    j    _finish
