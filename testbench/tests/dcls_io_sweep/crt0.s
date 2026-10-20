# SPDX-License-Identifier: Apache-2.0

  .section .text.init
  .global _start
  .type _start, @function
_start:
  // Setup stack
  la sp, STACK

  // Setup trap handler (located in ICCM `.text.nmi`)
  la t0, _trap_handler
  csrw mtvec, t0

  // Call `main()`
  call main

  // Map exit code: == 0 - success, != 0 - failure
  mv a1, a0
  li a0, 0xfe  // ok (check for `corruption_detected_o` status)
  beqz a1, _finish
  li a0, 1     // fail
  .size _start, .-_start

  .global _finish
  .type _finish, @function
_finish:
  la t0, tohost
  sb a0, 0(t0)  // Signal testbench termination
  j _finish
  .rept 10
  nop
  .endr
  .size _finish, .-_finish

  .balign 16
  .global _text_trap_handler
  .type _text_trap_handler, @function
_text_trap_handler:
  // Used when testing `VEER.iccm_rd_data_ecc` (`ID 24`): clears fault injection
  // from `.text` (`0x80000000`) before jumping to `_trap_handler` in ICCM.
  la t0, tohost
  li t1, 0x95  // CMD_INJ_CLEAR
  sw t1, 0(t0)
  fence
  tail _trap_handler
  .size _text_trap_handler, .-_text_trap_handler

  .section .text.nmi
  .balign 16
  .global _nmi
  .type _nmi, @function
_nmi:
  j _trap_handler
  .size _nmi, .-_nmi

  .balign 16
  .global _trap_handler
  .type _trap_handler, @function
_trap_handler:
  // Clear fault injection and NMI via `tohost` using only GPRs before
  // touching the DCCM stack or fetching from `.text` (`0x80000000`).
  la t0, tohost
  li t1, 0x95   // CMD_INJ_CLEAR
  sw t1, 0(t0)
  fence
  li t1, 0x182  // CLEAR_NMI_INT
  sw t1, 0(t0)
  fence
  call trap_handler
  tail _start
  .size _trap_handler, .-_trap_handler

  .section .data.io
  .global tohost
  .type tohost, @object
tohost:
  .4byte 0
  .size tohost, .-tohost
