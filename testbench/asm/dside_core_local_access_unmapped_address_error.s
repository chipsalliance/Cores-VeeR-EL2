#include "common.s"

dside_core_local_load_unmapped_address_error:
    li x4, 0x5
    li x5, 0x2
    // load from DCCM upper boundary (this also triggers unmapped address error)
    li x2, RV_DCCM_EADR - 1
    lw x2, 0(x2)
    j fail_if_not_serviced

dside_core_local_store_unmapped_address_error:
    li x4, 0x7
    li x5, 0x2
    // store to DCCM upper boundary (this also triggers unmapped address error)
    li x2, RV_DCCM_EADR - 1
    sw x2, 0(x2)
    j fail_if_not_serviced

main:
    call dside_core_local_load_unmapped_address_error
    call dside_core_local_store_unmapped_address_error
    j _finish