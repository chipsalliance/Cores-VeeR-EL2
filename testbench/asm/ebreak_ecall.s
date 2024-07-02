#include "common.s"

breakpoint_ebreak:
    li x4, 0x3
    li x5, 0x2
    ebreak
    j fail_if_not_serviced

environment_call_from_m_mode:
    li x4, 0xB
    li x5, 0x0
    ecall
    j fail_if_not_serviced

main:
    call breakpoint_ebreak
    call environment_call_from_m_mode
    j _finish