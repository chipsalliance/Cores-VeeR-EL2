#include "common.s"

.section .data
.balign 4
next_addr:
    .word 0
.section .text

// Each write must trap at exactly the expected instruction. A failed read
// must not count as successful verification of read-only protection.
.macro test_read_only csr
    la t0, 1f
    la t1, next_addr
    sw t0, 0(t1)
    // Put address of instruction that caused exception into s1
    la s1, 2f
    li s2, 2
    li t0, 0x12345678
2:
    csrw \csr, t0
    j fail
1:
.endm

main:
    csrci mstatus, 8
    csrw mie, zero
    la t0, handler
    csrw mtvec, t0

    call test_machine_csrs
#ifdef RV_USER_MODE
    call test_user_csrs

    // Allow U-mode reads of the counters, so writes cannot trap merely because
    // counter access is disabled.
    li t0, 0x7d
    csrw mcounteren, t0
#if RV_PMP_ENTRIES > 0
    // Allow U-mode to fetch code and access test data (TOR, RWX).
    li t0, -1
    csrw pmpaddr0, t0
    li t0, 0x0f
    csrw pmpcfg0, t0
#endif
    la t0, user_main
    csrw mepc, t0
    li t0, (3 << 11) | (1 << 17)
    csrc mstatus, t0             // MPP=U, MPRV=0
    mret
#endif
    j _finish

test_machine_csrs:
    test_read_only mvendorid
    test_read_only marchid
    test_read_only mimpid
    test_read_only mhartid
    test_read_only 0xfc0         // mdseac
    test_read_only 0xfc8         // meihap
    ret

#ifdef RV_USER_MODE
test_user_csrs:
    test_read_only cycle
    test_read_only cycleh
    test_read_only instret
    test_read_only instreth
    test_read_only hpmcounter3
    test_read_only hpmcounter4
    test_read_only hpmcounter5
    test_read_only hpmcounter6
    test_read_only hpmcounter3h
    test_read_only hpmcounter4h
    test_read_only hpmcounter5h
    test_read_only hpmcounter6h
    ret

user_main:
    call test_user_csrs
    la t0, _finish
    la t1, next_addr
    sw t0, 0(t1)
    ecall
    j fail
#endif

.balign 256
handler:
    csrr t0, mcause
#ifdef RV_USER_MODE
    li t1, 8
    bne t0, t1, check_write_exception
    li t1, (3 << 11)
    csrs mstatus, t1             // ECALL.U returns to M-mode
    j resume_test
#endif
check_write_exception:
    bne t0, s2, fail
    csrr t1, mepc
    // s1 should contain address of illegal instruction, it is set in test_read_only macro
    bne t1, s1, fail
resume_test:
    la t0, next_addr
    lw t0, 0(t0)
    csrw mepc, t0
    mret
