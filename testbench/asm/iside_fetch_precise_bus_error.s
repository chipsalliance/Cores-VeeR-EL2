#include "common.s"

iside_fetch_precise_bus_error:
    li x4, 0x1
    li x5, 0x9
    li x2, TRIGGER_IBUS_FAULT
    li x3, STDOUT
    sw x2, 0(x3)
    // ibus fault is triggered on subsequent instruction - force refetch from memory
    // since testbench relies on bus transaction happening to trigger bus error
    fence.i
    j fail_if_not_serviced

main:
    call iside_fetch_precise_bus_error
    j _finish