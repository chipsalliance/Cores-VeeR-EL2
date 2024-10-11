#include "common.s"

illegal_instruction:
    li x4, 0x2
    li x5, 0x0
    .word 0
    j fail_if_not_serviced

main:
    call illegal_instruction
    j _finish