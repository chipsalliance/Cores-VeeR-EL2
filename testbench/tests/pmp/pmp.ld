OUTPUT_ARCH( "riscv" )
ENTRY(_start)

SECTIONS {

  . = 0x80000000;
  .text : { *(.text.init*) *(.text*) }
  _text_end = .;
  _end = .;

  . = ALIGN(4096);
  _data = .;
  .data :  { *(.*data) *(.rodata*) *(.sbss) }
  .bss : { *(.bss) }
  _data_end = .;

  . = ALIGN(4096);
  .area1 : { *(.area1*) }
  .area2 : { *(.area2*) }

  . = ALIGN(4096);
  STACK = .;
  . = 0xd0580000;
  .data.io . : { *(.data.io) }
}
