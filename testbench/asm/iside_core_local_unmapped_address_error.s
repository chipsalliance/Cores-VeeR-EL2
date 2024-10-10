#include "common.s"

iside_core_local_unmapped_address_error:
    li x4, 0x1
    li x5, 0x2
    // jump to address that's only halfway inside ICCM
    li x2, 0xee000000-2
    jalr x2, 0(x2)
    j fail_if_not_serviced

main:
    call iside_core_local_unmapped_address_error
    j _finish