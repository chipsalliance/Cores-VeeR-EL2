#include "common.s"

machine_internal_timer0_local_interrupt:
    li x4, 0x8000001d
    li x5, 0x0
    csrw 0x7D4, 0x0 // disable incrementing timer0
    csrw 0x7D2, 0x0 // reset timer0 count value
    csrw 0x7D3, 0x8 // set timer0 threshold to 8
    li x2, 0x20000000
    csrw mie, x2    // enable timer0 local interrupt
    csrw 0x7D4, 0x1 // reenable incrementing timer0
    j fail_if_not_serviced

machine_internal_timer1_local_interrupt:
    li x4, 0x8000001c
    li x5, 0x0
    csrw 0x7D7, 0x0 // disable incrementing timer0
    csrw 0x7D5, 0x0 // reset timer0 count value
    csrw 0x7D6, 0x8 // set timer0 threshold to 8
    li x2, 0x10000000
    csrw mie, x2    // enable timer0 local interrupt
    csrw 0x7D7, 0x1 // reenable incrementing timer0
    j fail_if_not_serviced

main:
    call machine_internal_timer0_local_interrupt
    call machine_internal_timer1_local_interrupt
    j _finish