#include "common.s"

lsu_trigger_hit:
    la x4, 0x3
    la x5, 0x1
    // set up address to trigger on
    li x2, 0xdeadbeef
    csrw tdata2, x2
    // enable trigger in M-mode, fire on address of a load
    li x3, 0x41
    csrw mcontrol, x3
    // load from that address
    lw x2, 0(x2)
    j fail_if_not_serviced

main:
    call lsu_trigger_hit
    j _finish