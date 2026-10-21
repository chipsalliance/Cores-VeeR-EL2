/* SPDX-License-Identifier: Apache-2.0 */

OUTPUT_ARCH( "riscv" )
ENTRY(_start)

SECTIONS
{
    . = 0x80000000;
    .text   : { *(.text*) }

    /* Dedicated cache-aligned sections for EL2_IC_DATA outside-DCLS sub-tests */
    . = 0x8000b000;
    .subtest1_text : { KEEP(*(.subtest1_text)) }
    . = 0x8000b400;
    .subtest2_text : { KEEP(*(.subtest2_text)) }
    . = 0x8000bc00;
    .subtest2_stale : { KEEP(*(.subtest2_stale)) }
    . = 0x8000d000;
    .subtest3_text : { KEEP(*(.subtest3_text)) }
    _end = .;

    /* STDOUT */
    . = 0xd0580000;
    .data.io . : { *(.data.io) }

    /* DCCM */
    . = 0xf0040000;
    dccm = .;
    .data : { *(.*data) *(.rodata*) *(.sbss)}
    .bss : { *(.bss); . = ALIGN(4); }
    STACK = ALIGN(16) + 0x1000;

    . = 0xfffffff8;
    .data.ctl : AT(0xfffffff8) { LONG(0xf0040000); LONG(STACK) }
}
