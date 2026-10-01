# SPDX-License-Identifier: Apache-2.0
#
# ICCM kernel for the iccm_addr_xor_ecc_corr test.
#
# Linked at the ICCM base (0xEE000000) and copied there at runtime. Compressed
# instructions are disabled so every instruction occupies exactly one 32-bit
# ICCM word, which makes the even/odd word index of each instruction fixed:
#
#   0xEE000000  word 0 (even)  addi a0, a0, 1
#   0xEE000004  word 1 (odd)   addi a0, a0, 2
#   0xEE000008  word 2 (even)  addi a0, a0, 4
#   0xEE00000C  word 3 (odd)   addi a0, a0, 8
#   0xEE000010  word 4 (even)  ret
#
# iccm_kernel(x) returns x + 15. The trailing nops keep the words the fetch
# unit prefetches past the ret initialised with valid (XOR-folded) data.

.section .iccm_data0, "ax"
.option push
.option norvc
.balign 16
.global iccm_kernel
.type iccm_kernel, @function
iccm_kernel:
    addi a0, a0, 1
    addi a0, a0, 2
    addi a0, a0, 4
    addi a0, a0, 8
    ret
.size iccm_kernel, .-iccm_kernel
    .rept 15
    nop
    .endr
.option pop
