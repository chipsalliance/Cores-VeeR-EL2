OUTPUT_ARCH( "riscv" )
ENTRY(_start)

SECTIONS
{
    . = 0x80000000;
    .text   : { *(.text*) }
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
