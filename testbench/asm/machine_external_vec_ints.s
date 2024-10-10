#include "common.s"

enable_ext_int1:
    // set up gateway configuration - level triggered active high
    li x2, 0x0
    li x3, (RV_PIC_BASE_ADDR + 0x4004)  // meigwctrl1
    sw x2, 0(x3)
    // clear interrupt bit for gateway
    li x3, (RV_PIC_BASE_ADDR + 0x5004)  // meigwclr1
    sw zero, 0(x3)
    // set up priority level
    li x3, (RV_PIC_BASE_ADDR + 0x4) // meipl1
    li x2, 0x1
    sw x2, 0(x3)

    // interrupt priority threshold and priority nesting are
    // already initialized at correct value and we're only
    // testing one interrupt so we don't bother setting them explicitly

    // enable external interrupt 1
    li x3, (RV_PIC_BASE_ADDR + 0x2004)
    li x2, 0x1
    sw x2, 0(x3)
    // enable external interrupts
    li x2, 0x800
    csrw mie, x2
    ret

machine_external_interrupt:
    la x4, 0x8000000b
    la x5, 0x0
    // Set up external interrupt vector table at the beginning of DCCM
    la x2, exc_int_handler
    li x3, RV_DCCM_SADR
    sw x2, 0(x3)
    // set up base interrupt vector table address
    csrw 0xBC8, x3  // meivt

    mv x6, x1 // save return address
    call enable_ext_int1
    mv x1, x6 // restore return address

    li x2, TRIGGER_EXT_INT1
    li x3, STDOUT
    sw x2, 0(x3)
    j fail_if_not_serviced

fast_interrupt_dccm_region_access_error:
    la x4, 0xF0001001
    la x5, 0x0
    // set up base interrupt vector table address at some address
    // *not* in DCCM but in DCCM region
    // assume somewhat optimistically that DCCM isn't allocated
    // at the end of its region so RV_DCCM_EADR + 1 is still in DCCM region
    li x2, RV_DCCM_EADR + 1
    csrw 0xBC8, x2  // meivt

    mv x6, x1 // save return address
    call enable_ext_int1
    mv x1, x6 // restore return address

    // trigger external interrupt 1
    li x2, TRIGGER_EXT_INT1
    li x3, STDOUT
    sw x2, 0(x3)
    j fail_if_not_serviced

fast_interrupt_non_dccm_region:
    la x4, 0xF0001002
    la x5, 0x0
    // set up interrupt vector table address at an address that's
    // not in DCCM region
    li x2, ((RV_DCCM_REGION + 1) % 0x10) << 28
    csrw 0xBC8, x2  // meivt

    mv x6, x1 // save return address
    call enable_ext_int1
    mv x1, x6 // restore return address

    // trigger external interrupt 1
    li x2, TRIGGER_EXT_INT1
    li x3, STDOUT
    sw x2, 0(x3)
    j fail_if_not_serviced

main:
    call machine_external_interrupt
    call fast_interrupt_dccm_region_access_error
    call fast_interrupt_non_dccm_region
    j _finish