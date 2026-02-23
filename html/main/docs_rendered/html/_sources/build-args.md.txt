# Build Arguments

## Memory Protection Build Arguments

### Memory Protection Build Argument Rules

The rules for valid memory protection address (INST/DATA_ACCESS_ADDRx) and mask (INST/DATA_ACCESS_MASKx) build arguments are:

* INST/DATA_ACCESS_ADDRx must be 64B-aligned (i.e., 6 least significant bits must be '0')
* INST/DATA_ACCESS_MASKx must be an integer multiple of 64B minus 1 (i.e., 6 least significant bits must be '1')
* For INST/DATA_ACCESS_MASKx, all '0' bits (if any) must be left-justified and all '1' bits must be right-justified
* No bit in INST/DATA_ACCESS_ADDRx may be '1' if the corresponding bit in INST/DATA_ACCESS_MASKx is also '1' (i.e., for each bit position, at most one of the bits in INST/DATA_ACCESS_ADDRx and INST/DATA_ACCESS_MASKx may be '1')

### Memory Protection Build Arguments

* **Instructions**
  * Instruction Access Window *x* (*x* = 0..7)
    * Enable (INST_ACCESS_ENABLEx): 0,1 *(0 = window disabled; 1 = window enabled)*
    * Base address (INST_ACCESS_ADDRx): 0x0000_0000..0xFFFF_FFC0, *see [](build-args.md#memory-protection-build-argument-rules)*
    * Mask (INST_ACCESS_MASKx): 0x0000_003F..0xFFFF_FFFF, *see [](build-args.md#memory-protection-build-argument-rules)*
* **Data**
  * Data Access Window x (x = 0..7)
    * Enable (DATA_ACCESS_ENABLEx): 0,1 *(0 = window disabled; 1 = window enabled)*
    * Base address (DATA_ACCESS_ADDRx): 0x0000_0000..0xFFFF_FFC0, *see [](build-args.md#memory-protection-build-argument-rules)*
    * Mask (DATA_ACCESS_MASKx): 0x0000_003F..0xFFFF_FFFF, *see [](build-args.md#memory-protection-build-argument-rules)*

## Core Memory-Related Build Arguments

### Core Memories and Memory-Mapped Register Blocks Alignment Rules

Placement of VeeR EL2's core memories and memory-mapped register blocks in the 32-bit address range is very flexible.
Each memory or register block may be assigned to any region and within the region's 28-bit address range to any start address on a naturally aligned power-of-two address boundary relative to its own size (i.e., *start_address* = *n × size*, whereas n is a positive integer number).

For example, the start address of an 8KB-sized DCCM may be 0x0000_0000, 0x0000_2000, 0x0000_4000, 0x0000_6000, etc.
A memory or register block with a non-power-of-two size must be aligned to the next bigger power-of-two size.
For example, the starting address of a 48KB-sized DCCM must aligned to a 64KB boundary, i.e., it may be 0x0000_0000, 0x0001_0000, 0x0002_0000, 0x0003_0000, etc.

Also, no two memories or register blocks may overlap each other, and no memory or register block may cross a region boundary.

The start address of the memory or register block is specified with an offset relative to the start address of the region.

This offset must follow the rules described above.

### Memory-Related Build Arguments
* **ICCM**
  * Enable (RV_ICCM_ENABLE): 0, 1 *(0 = no ICCM; 1 = ICCM enabled)*
  * Region (RV_ICCM_REGION): 0..15
  * Offset (RV_ICCM_OFFSET): *offset in bytes from start of region satisfying rules in [](build-args.md#core-memories-and-memory-mapped-register-blocks-alignment-rules)*
  * Size (RV_ICCM_SIZE): 4, 8, 16, 32, 64, 128, 256, 512 *(in KB)*
* **DCCM**
  * Region (RV_DCCM_REGION): 0..15
  * Offset (RV_DCCM_OFFSET): *offset in bytes from start of region satisfying rules in [](build-args.md#core-memories-and-memory-mapped-register-blocks-alignment-rules)*
  * Size (RV_DCCM_SIZE): 4, 8, 16, 32, 48, 64, 128, 256, 512 *(in KB)*
* **I-Cache**
  * Enable (RV_ICACHE_ENABLE): 0, 1 *(0 = no I-cache; 1 = I-cache enabled)*
  * Size (RV_ICACHE_SIZE): 16, 32, 64, 128, 256 *(in KB)*
  * Protection (RV_ICACHE_ECC): 0, 1 *(0 = parity; 1 = ECC)*
* **PIC Memory-mapped Control Registers**
  * Region (RV_PIC_REGION): 0..15
  * Offset (RV_PIC_OFFSET): *offset in bytes from start of region satisfying rules in [](build-args.md#core-memories-and-memory-mapped-register-blocks-alignment-rules)*
  * Size (RV_PIC_SIZE): 32, 64, 128, 256 *(in KB)*
