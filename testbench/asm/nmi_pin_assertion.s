#include "common.s"

nmi_pin_assertion:
    li x4, 0x0
    li x5, 0x0 
    // trigger NMI
    li x2, TRIGGER_NMI
    li x3, STDOUT
    sw x2, 0(x3)
    j fail_if_not_serviced

main:
    call nmi_pin_assertion
    j _finish