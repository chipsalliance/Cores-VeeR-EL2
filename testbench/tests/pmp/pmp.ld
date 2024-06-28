OUTPUT_ARCH( "riscv" )
ENTRY(_start)

SECTIONS {

  . = 0x80000000;
  _text = .;
  .text : { *(.text.init*) *(.text*) }
  _text_end = .;
  _end = .;

  . = ALIGN(4096);
  _data = .;
  .data :  { *(.*data) *(.rodata*) *(.sbss) }
  _bss = .;
  .bss : { *(.bss) }
  _data_end = .;

  . = ALIGN(4096);
  _area = .;
  .area : { *(.area.bufr) *(.area.code) }
  . = ALIGN(4096);

  . = ALIGN(8192);
  _stack_lo = .;
  . += 8192;
  _stack_hi = .;

  . = 0xd0580000;
  .data.io . (NOLOAD) : { KEEP( *(.data.io) ) }
}
