OUTPUT_ARCH( "riscv" )
ENTRY(_start)

SECTIONS {
  .text  :  { *(.text*) }
  . = 0x10000;
  .data  :  { *(.*data) *(.rodata*)}
}
