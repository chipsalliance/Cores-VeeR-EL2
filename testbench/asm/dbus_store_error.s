#include "common.s"

dbus_store_error:
    li x4, 0xF0000000
    li x5, 0x0
    // address of some data that resides in memory (and not in iccm/dccm)
    lw x6, _start
    // trigger bus fault at next store
    li x2, TRIGGER_DBUS_FAULT
    li x3, STDOUT
    sw x2, 0(x3)
    // bus fault is triggered on this instruction
    sw x2, 0(x6)
    j fail_if_not_serviced

main:
    call dbus_store_error
    j _finish
