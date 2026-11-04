/* SPDX-License-Identifier: Apache-2.0 */

OUTPUT_ARCH( "riscv" )
ENTRY(_start)

SECTIONS
{
    . = 0x80000000;
    .text   : { *(.text*) }

    /* Set-aliased ICache ways (spaced by 16KB = 0x4000 bytes, mapped to Set 64) */
    . = 0x80009000;
    .way0_text : { KEEP(*(.way0_text)) }
    . = 0x8000d000;
    .way1_text : { KEEP(*(.way1_text)) }
    . = 0x80011000;
    .way2_text : { KEEP(*(.way2_text)) }
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

    /* ICCM */
    iccm_start = .;
    .iccm_data0 0xee000000 : AT(iccm_start) {
        KEEP(*(.iccm_data0));
        . = ALIGN(4);
    } = 0x0000,
    iccm_end = iccm_start + SIZEOF(.iccm_data0);

    . = 0xfffffff8;
    .data.ctl : AT(0xfffffff8) { LONG(0xf0040000); LONG(STACK) }
}
