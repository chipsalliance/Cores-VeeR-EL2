# SPDX-License-Identifier: Apache-2.0

.section .text.init
.global _start
_start:

  # Setup stack
  la sp, STACK

  # Setup trap handler (located in ICCM .text.nmi)
  la t0, _trap_handler
  csrw mtvec, t0

  # Call main()
  call main

  # Map exit code: == 0 - success, != 0 - failure
  mv  a1, a0
  li  a0, 0xfe # ok (check for `corruption_detected_o` status)
  beq a1, x0, _finish
  li  a0, 1 # fail

.global _finish
_finish:
  la t0, tohost
  sb a0, 0(t0) # Signal testbench termination
  beq x0, x0, _finish
  .rept 10
  nop
  .endr

.section .text.nmi
.align 4
.global _nmi
_nmi:
  j _trap_handler

.align 4
.global _trap_handler
_trap_handler:
  # Clear NMI and fault injection via tohost using only GPRs before
  # touching the DCCM stack or fetching from .text (0x80000000).
  la t0, tohost
  li t1, 0x182 # CLEAR_NMI_INT
  sw t1, 0(t0)
  li t1, 0x95  # CMD_INJ_CLEAR
  sw t1, 0(t0)
  fence
  la t0, trap_handler
  jalr ra, t0, 0
  la t0, _start
  jr t0

.section .data.io
.global tohost
tohost: .word 0
