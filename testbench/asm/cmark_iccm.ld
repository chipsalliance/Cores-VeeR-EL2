OUTPUT_ARCH( "riscv" )
ENTRY(_start)

SECTIONS {
  .text   : { crt0.o (.text*) }
 _end = .;
  . = 0xee000000 ;
  .text.init   : { cmark.o (.text*) }
  . = 0xd0580000;
  .data.io .  : { *(.data.io) }
  . = 0xf0040000;
  .data  :  { *(.*data) *(.rodata*) *(.sbss) STACK = ALIGN(16) + 0x1000;}
  .bss : { *(.bss) }
  . = 0xfffffff0;
  .iccm.ctl : { LONG(0xee000000); LONG(0xee008000) }
  . = 0xfffffff8;
  .data.ctl : { LONG(0xf0040000); LONG(STACK) }
}
