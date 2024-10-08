#include "common.s"

dbus_nonblocking_load_error:
    li x4, 0xF0000001
    li x5, 0x0
    // trigger bus fault at next load
    li x2, TRIGGER_DBUS_FAULT
    li x3, STDOUT
    sw x2, 0(x3)
    // bus fault is triggered on this instruction
    lw x2, 0(zero)
    j fail_if_not_serviced

main:
    call dbus_nonblocking_load_error
    j _finish