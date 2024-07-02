#include "common.s"

dside_load_across_region_boundary:
    li x4, 0x4
    li x5, 0x2
    // load from across region boundary
    li x2, 0xe0000000-2
    lw x2, 0(x2)
    j fail_if_not_serviced

dside_store_across_region_boundary:
    li x4, 0x6
    li x5, 0x2
    // store across region boundary
    li x2, 0xe0000000-2
    sw x2, 0(x2)
    j fail_if_not_serviced

main:
    call dside_load_across_region_boundary
    call dside_store_across_region_boundary
    j _finish