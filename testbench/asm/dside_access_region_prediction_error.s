#include "common.s"

dside_load_region_prediction_error:
    li x4, 0x5
    li x5, 0x5
    // We take a large address that will overflow to another region
    // when offset is used in an 'lw' instruction: 0xFFFFFFFC + 0x4
    li x2, 0xFFFFFFFC
    lw x2, 0x4(x2)
    j fail_if_not_serviced

dside_store_region_prediction_error:
    li x4, 0x7
    li x5, 0x5
    // same as in load region prediction error
    li x2, 0xFFFFFFFC
    sw x2, 0x4(x2)
    j fail_if_not_serviced

main:
    call dside_load_region_prediction_error
    call dside_store_region_prediction_error
    j _finish