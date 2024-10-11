#include "common.s"

dside_pic_load_access_error:
    li x4, 0x5
    li x5, 0x6
    // perform not word-sized load from PIC
    li x2, RV_PIC_BASE_ADDR
    lb x2, 0(x2)
    j fail_if_not_serviced

dside_pic_store_access_error:
    li x4, 0x7
    li x5, 0x6
    // perform not word-sized store to PIC
    li x2, RV_PIC_BASE_ADDR
    sb x2, 0(x2)
    j fail_if_not_serviced

main:
    call dside_pic_load_access_error
    call dside_pic_store_access_error
    j _finish