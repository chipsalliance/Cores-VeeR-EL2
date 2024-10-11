#include "common.s"

machine_software_interrupt:
    la x4, 0x80000003
    li x5, 0x0
    // enable software interrupt
    li x2, 0x8
    csrw mie, x2
    // trigger soft interrupt
    li x2, TRIGGER_SOFT_INT
    li x3, STDOUT
    sw x2, 0(x3)
    j fail_if_not_serviced

machine_timer_interrupt:
    la x4, 0x80000007
    li x5, 0x0
    // enable machine timer interrupt
    li x2, 0x80
    csrw mie, x2
    // trigger timer interrupt
    li x2, TRIGGER_TIMER_INT
    li x3, STDOUT
    sw x2, 0(x3)
    j fail_if_not_serviced

main:
    call machine_software_interrupt
    call machine_timer_interrupt
    j _finish