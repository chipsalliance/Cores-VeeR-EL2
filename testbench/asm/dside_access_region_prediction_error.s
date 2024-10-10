#include "common.s"

dside_load_region_prediction_error:
    li x4, 0x5
    li x5, 0x5
    // this assumes that RV_PIC_BASE_ADDR is as high in the region
    // as realistically allowed, e.g. 0xffff8000, this allows us
    // to construct an address that will overflow to another region
    // when offset is used in an 'lw' instruction: 0xfffffffc + 0x4
    li x2, RV_PIC_BASE_ADDR + 0x7ffc
    lw x2, 0x4(x2)
    j fail_if_not_serviced

dside_store_region_prediction_error:
    li x4, 0x7
    li x5, 0x5
    // same as in load region prediction error
    li x2, RV_PIC_BASE_ADDR + 0x7ffc
    sw x2, 0x4(x2)
    j fail_if_not_serviced

main:
    call dside_load_region_prediction_error
    call dside_store_region_prediction_error
    j _finish