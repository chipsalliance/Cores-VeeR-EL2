/* SPDX-License-Identifier: Apache-2.0 */

OUTPUT_ARCH( "riscv" )
ENTRY(_start)

SECTIONS {
  .handler : {
    KEEP(*(.handler))
  } > RAM = 0x0

  . = 0x80000000;
  .text : { *(.text.init*) *(.text*) }
  _end = .;
  .data :  { *(.*data) *(.rodata*) *(.sbss) STACK = ALIGN(16) + 0x1000;}
  .bss : { *(.bss) }
  . = 0xd0580000;
  .data.io . : { *(.data.io) }
}
