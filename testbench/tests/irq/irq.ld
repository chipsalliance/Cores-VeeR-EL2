/* SPDX-License-Identifier: Apache-2.0 */

OUTPUT_ARCH( "riscv" )
ENTRY(_start)

SECTIONS {
  . = 0xee000000;
  .text.nmi : { KEEP(*(.text.nmi*)) }
  . = 0x80000000;
  .text.init : { *(.text.init*) }
  .text : { *(.text*) }
  _end = .;
  .data :  { *(.*data) *(.rodata*) *(.sbss) STACK = ALIGN(16) + 0x1000;}
  .bss : { *(.bss) }
  . = 0xd0580000;
  .data.io . : { *(.data.io) }
  /* The following constants tell the testbench to do ICCM preload */
  . = 0xfffffff0;
  .iccm.ctl : { LONG(ADDR(.text.nmi)); LONG(ADDR(.text.nmi) + SIZEOF(.text.nmi)) }
}
