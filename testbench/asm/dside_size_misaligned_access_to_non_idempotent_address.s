#include "common.s"

dside_size_misaligned_load_to_non_idempotent_address:
    li x4, 0x4
    li x5, 0x1
    // load from across non-idempotent address (with side effects)
    // we take advantage of the fact that STDOUT is such an address
    li x2, STDOUT-2
    lw x2, 0(x2)
    j fail_if_not_serviced

dside_size_misaligned_store_to_non_idempotent_address:
    li x4, 0x6
    li x5, 0x1
    // store to across non-idempotent address (with side effect)
    // we take advantage of the fact that STDOUT is such an address
    li x2, STDOUT-2
    sw x2, 0(x2)
    j fail_if_not_serviced

main:
    call dside_size_misaligned_load_to_non_idempotent_address
    call dside_size_misaligned_store_to_non_idempotent_address
    j _finish