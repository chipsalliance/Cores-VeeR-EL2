/* SPDX-License-Identifier: Apache-2.0 */

OUTPUT_ARCH( "riscv" )
ENTRY(_start)

SECTIONS {
  .handler : {
    KEEP(*(.handler))
  } > RAM = 0x0

  . = 0xee000000;
  .text.nmi : { KEEP(*(.text.nmi*)) }
  . = 0x80000000;
  .text : { *(.text.init*) *(.text*) }
  _end = .;

  . = 0xd0580000;
  .data.io . : { *(.data.io) }

  /* DCCM */
  . = 0xf0040000;
  dccm = .;
  .data : { *(.*data) *(.rodata*) *(.sbss)}
  .bss : { *(.bss); . = ALIGN(4); }
  STACK = ALIGN(16) + 0x1000;

  . = 0xfffffff0;
  .iccm.ctl : { LONG(ADDR(.text.nmi)); LONG(ADDR(.text.nmi) + SIZEOF(.text.nmi)) }
  . = 0xfffffff8;
  .data.ctl : AT(0xfffffff8) { LONG(0xf0040000); LONG(STACK) }
}
