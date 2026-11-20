# Cache Control

This chapter describes the features to control the VeeR EL2 core's instruction cache (I-cache).

## Features

The VeeR EL2's I-cache control features are:
* Flushing the I-cache
* Capability to enable/disable I-cache
* Diagnostic access to data, tag, and status information of the I-cache

:::{note}
The I-cache is an optional core feature. Instantiation of the I-cache is controlled by the RV_ICACHE_ENABLE build argument.
:::

## Feature Descriptions

### Cache Flushing

As described in [](memory-map.md#memory-synchronization-trigger-register-dmst), a debugger may initiate an operation that is equivalent to a `fence.i` instruction by writing a '1' to the *fence_i* field of the `dmst` register.
As part of executing this operation, the I-cache is flushed (i.e., all entries in the I-cache are invalidated).

### Enabling/Disabling I-Cache

As described in [](memory-map.md#region-access-control-register-mrac), each of the 16 memory regions has two control bits which are hosted in the `mrac` register.
One of these control bits, *cacheable*, controls if accesses to that region may be cached.
If the *cacheable* bits of all 16 regions are set to '0', the I-cache is effectively turned off.

### Diagnostic Access

For firmware as well as hardware debug, direct access to the raw content of the data array, tag array, and status bits of the I-cache may be important.
Instructions stored in the cache, the tag of a cache line as well as status information including a line's valid bit and a set's LRU bits can be manipulated.
It is also possible to inject a parity/ECC error in the data or tag array to check error recovery.
Five control registers are used to provide read/write diagnostic access to the two arrays and status bits.
The `dicawics` register controls the selection of the array, way, and index of a cache line.
The `dicad0/0h/1` and `dicago` registers are used to perform a read or write access to the selected array location.
See sections [](cache.md#i-cache-arraywayindex-selection-register-dicawics) - [](cache.md#i-cache-array-go-register-dicago) for more detailed information.

:::{note}
The instructions and the tags are stored in parity/ECC-protected SRAM arrays. The status bits are stored in flops.
:::

## Use Cases

The I-cache control features can be broadly divided into two categories:

1. Debug Support A few examples how diagnostic accesses ([](cache.md#diagnostic-access)) may be useful for debug:
   * Generating an I-cache dump (e.g., to investigate performance issues).
   * Injecting parity/ECC errors in the data or tag array of the I-cache.
   * Diagnosing stuck-at bits in the data or tag array of the I-cache.
   * Preloading the I-cache if a hardware bug prevents instruction fetching from memory.

2. Performance Evaluation
   * To evaluate the performance advantage of the I-cache, it is useful to run code with and without the cache enabled.
     Enabling and disabling the I-cache ([](cache.md#enablingdisabling-i-cache)) is an essential feature for this.

## Theory Of Operation

### Read a Chunk of an I-cache Cache Line

The following steps must be performed to read a 64-bit chunk of instruction data and its associated 4 parity / 7 ECC bits in an I-cache cache line:

1. Write array/way/address information which location to access in the I-cache to the `dicawics` register:
   * *array* field: 0 (i.e., I-cache data array),
   * *way* field: way to be accessed (i.e., 0..1 for 2-way or 0..3 for 4-way set-associative cache), and
   * *index* field: index of cache line to be accessed.
2. Read the `dicago` register which causes a read access from the I-cache data array at the location selected by the dicawics register.
3. Read the `dicad0` and `dicad0h` registers to get the selected 64-bit cache line chunk (*instr* fields), and read the `dicad1` register to get the associated parity/ECC bits (*parity0/1/2/3* / *ecc* fields).

### Write a Chunk of an I-Cache Cache Line

The following steps must be performed to write a 64-bit chunk of instruction data and its associated 4 parity / 7 ECC bits in an I-cache cache line:
1. Write array/way/address information which location to access in the I-cache to the `dicawics` register:
   * *array* field: 0 (i.e., I-cache data array),
   * *way* field: way to be accessed (i.e., 0..1 for 2-way or 0..3 for 4-way set-associative cache), and
   * *index* field: index of cache line to be accessed.
2. Write the new instruction data to the *instr* fields of the `dicad0` and `dicad0h` registers, and write the calculated correct instruction parity/ECC bits (unless error injection should be performed) to the *parity0/1/2/3* / *ecc* and fields of the dicad1 register.
3. Write a '1' to the go field of the dicago register which causes a write access to the I-cache data array copying the information stored in the `dicad0/0h/1` registers to the location selected by the `dicawics` register.

### Read or Write a Full I-Cache Cache Line

The following steps must be performed to read or write instruction data and associated parity/ECC bits of a full Icache cache line:

1. Start with an index naturally aligned to the 64- or 32-byte cache line size (i.e., *index[5:3]* = '000' for 64-byte or *index[4:3]* = '00' for 32-byte).
2. Perform steps in [](cache.md#read-a-chunk-of-an-i-cache-cache-line) to read or [](cache.md#write-a-chunk-of-an-i-cache-cache-line) to write.
3. Increment the index.
4. Go back to step 2.) for a total of 8 (for 64-byte line size) or 4 (for 32-byte line size) iterations.

### Read a Tag and Status Information of an I-cache Cache Line

The following steps must be performed to read the tag, tag's parity/ECC bit(s), and status information of an I-cache cache line:
1. Write array/way/address information which location to access in the I-cache to the `dicawics` register:
   * *array* field: 1 (i.e., I-cache tag array and status),
   * *way* field: way to be accessed (i.e., 0..1 for 2-way or 0..3 for 4-way set-associative cache), and
   * *index* field: index of cache line to be accessed.
2. Read the `dicago` register which causes a read access from the I-cache tag array and status bits at the location selected by the `dicawics` register.
3. Read the `dicad0` register to get the selected cache line's tag (*tag* field) and valid bit (*valid* field) as well as the set's LRU bits (*lru* field), and read the `dicad1` register to get the tag's parity/ECC bit(s) (*parity0* / *ecc* field).

### Write a Tag and Status Information of an I-Cache Cache Line

The following steps must be performed to write the tag, tag's parity/ECC bit, and status information of an I-cache cache line:

1. Write array/way/address information which location to access in the I-cache to the `dicawics` register:
   * *array* field: 1 (i.e., I-cache tag array and status),
   * *way* field: way to be accessed (i.e., 0..1 for 2-way or 0..3 for 4-way set-associative cache), and
   * *index* field: index of cache line to be accessed.
2. Write the new tag, valid, and LRU information to the *tag, valid*, and *lru* fields of the `dicad0` register, and write the calculated correct tag parity/ECC bit (unless error injection should be performed) to the *parity0* / *ecc* field of the `dicad1` register.
3. Write a '1' to the *go* field of the `dicago` register which causes a write access to the I-cache tag array and status bits copying the information stored in the dicad0/1 registers to the location selected by the `dicawics` register.

## I-Cache Control/Status Registers

A summary of the I-cache control/status registers in CSR address space:
* [](cache.md#i-cache-arraywayindex-selection-register-dicawics)
* [](cache.md#i-cache-array-data-0-register-dicad0)
* [](cache.md#i-cache-array-data-0-high-register-dicad0h)
* [](cache.md#i-cache-array-data-1-register-dicad1)
* [](cache.md#i-cache-array-go-register-dicago)

All reserved and unused bits in these control/status registers must be hardwired to '0'.
Unless otherwise noted, all read/write control/status registers must have WARL (Write Any value, Read Legal value) behavior.

### I-Cache Array/Way/Index Selection Register (dicawics)

The `dicawics` register is used to select a specific location in either the data array or the tag array / status of the Icache.
In addition to selecting the array, the location in the array must be specified by providing the way, and index.
Once selected, the `dicad0/0h/1` registers (see [](cache.md#i-cache-array-data-0-register-dicad0), [](cache.md#i-cache-array-data-0-high-register-dicad0h), and [](cache.md#i-cache-array-data-1-register-dicad1)) hold the information read from or to be written to the specified location, and the dicago register (see [](cache.md#i-cache-array-go-register-dicago)) is used to control the read/write access to the specified I-cache array.

The cache line size of the I-cache is either 64 or 32 bytes.
The `dicawics` register addresses a 64-bit chunk of instruction data or a cache line tag with its associated status.
Each 64-bit instruction data chunk is protected either with four parity bits (each covering 16 consecutive instruction data bits) or with 7-bit ECC (covering all 64 instruction data bits).
There are 8 such chunks in a 64-byte or 4 such chunks in a 32-byte cache line.
Each cache line tag is protected either with a single parity bit or with 5-bit ECC.

:::{note}
This register is accessible in **Debug Mode only**. Attempting to access this register in machine mode raises an illegal instruction exception.
:::

This register is mapped to the non-standard read-write CSR address space.

:::{list-table} I-Cache Array/Way/Index Selection Register (dicawics, at CSR 0x7C8)
:name: tab-cache-array-dicawics
:header-rows: 1

* - **Field**
  - **Bits**
  - **Description**
  - **Access**
  - **Reset**
* - Reserved
  - 31:25
  - Reserved
  - R
  - 0
* - array
  - 24
  - Array select:

    0: I-cache data array (incl. parity/ECC bits)

    1: I-cache tag array (incl. parity/ECC bits) and status (incl. valid and  LRU bits)
  - R/W
  - 0
* - Reserved
  - 23:22
  - Reserved
  - R
  - 0
* - way
  - 21:20
  - Way select:

    Four-way set-associative cache: *way[21:20]*

    Two-way set-associative cache: *way[20]* (*way[21]* reserved, must be 0)
  - R/W
  - 0
* - Reserved
  - 19:17
  - Reserved
  - R
  - 0
* - index [^fn-cache-1]
  - 16:3
  - Index address bits select

    **Notes:**

    - Index bits are right-justified:

    	- For 4-way set-associative cache, *index[16]* and other unused upper  bits (for I-cache sizes smaller than 256KB) must be 0

    	- For 2-way set-associative cache, unused upper bits (for I-cache  sizes smaller than 256KB) must be 0

    - For tag array and status access:

    	- For 64-byte cache line size, bits 5..3 are ignored by hardware

    	- For 32-byte cache line size, bits 4..3 are ignored by hardware

    - This field does not have WARL behavior
  - R/W
  - 0
* - Reserved
  - 2:0
  - Reserved
  - R
  - 0
:::

[^fn-cache-1]: VeeR EL2’s I-cache supports four- or two-way set-associativity and cache line sizes of 64 or 32 bytes. Each way is subdivided into 2 banks, and each bank is 8 bytes wide. A bank is selected by index[3], and index[2:0] address a byte of the 8-byte wide bank.

### I-Cache Array Data 0 Register (dicad0)

The `dicad0` register, in combination with the `dicad0h/1` registers (see [](cache.md#i-cache-array-data-0-high-register-dicad0h) and [](cache.md#i-cache-array-data-1-register-dicad1)), is used to store information read from or to be written to the I-cache array location specified with the `dicawics` register (see [](cache.md#i-cache-arraywayindex-selection-register-dicawics)).
Triggering a read or write access of the I-cache array is controlled by the `dicago` register (see [](cache.md#i-cache-array-go-register-dicago)).

The layout of the dicad0 register is different for the data array and the tag array / status, as described in {numref}`tab-cache-array-dicad0` below.

:::{note}
During normal operation, the parity/ECC bits over the 64-bit instruction data as well as the tag are generated and checked by hardware.
However, to enable error injection, the parity/ECC bits must be computed by software for I-cache data and tag array diagnostic writes.
:::

:::{note}
This register is accessible in **Debug Mode only**.
Attempting to access this register in machine mode raises an illegal instruction exception.
:::

This register is mapped to the non-standard read-write CSR address space.

:::{list-table} I-Cache Array Data 0 Register (dicad0, at CSR 0x7C9)
:name: tab-cache-array-dicad0
:header-rows: 1

* - **Field**
  - **Bits**
  - **Description**
  - **Access**
  - **Reset|**
* - **I-cache data array**
  -
  -
  -
  -
* - instr
  - 31:0
  - Instruction data

    31:16: instruction data bytes 3/2 (protected by *parity1* / *ecc*)

    15:0: instruction data bytes 1/0 (protected by *parity0* / *ecc*)
  - R/W
  - 0
* - **I-cache tag array and status bits**
  -
  -
  -
  -
* - tag
  - 31:11
  - Tag

    **Note:**

    Tag bits are right-justified; unused higher bits (for I-cache sizes larger than 8KB) must be 0
  - R/W
  - 0
* - Unused
  - 10:7
  - Unused
  - R/W
  - 0
* - lru
  - 6:4
  - Pseudo LRU bits (same bits are accessed independent of selected way):

    Four-way set-associative cache:

      - *lru[4]*: way0/1 / way2/3 selection

    	  - 0: way0/1

    	  - 1: way2/3

      - *lru[5]*: way0 / way1 selection

    	  - 0: way0

    	  - 1: way1

  	  - *lru[6]*: way2 / way3 selection

    	  - 0: way2

    	  - 1: way3

    Two-way set-associative cache:

      - *lru[4]*: way0 / way1 selection

    	  - 0: way0

    	  - 1: way1

	    - *lru[6:5]*: Reserved (must be 0)
  - R/W
  - 0
* - Unused
  - 3:1
  - Unused
  - R/W
  - 0
* - valid
  - 0
  - Cache line valid/invalid:

  	  - 0: cache line invalid

      - 1: cache line valid
  - R/W
  - 0
:::

### I-Cache Array Data 0 High Register (dicad0h)

The `dicad0h` register, in combination with the `dicad0` and `dicad1` registers (see [](cache.md#i-cache-array-data-0-register-dicad0) and [](cache.md#i-cache-array-data-1-register-dicad1)), is used to store information read from or to be written to the I-cache array location specified with the `dicawics` register (see [](cache.md#i-cache-arraywayindex-selection-register-dicawics)).
Triggering a read or write access of the I-cache array is controlled by the dicago register (see [](cache.md#i-cache-array-go-register-dicago)).
The layout of the `dicad0h` register is described in {numref}`tab-cache-array-dicad0h` below.

:::{note}
During normal operation, the parity/ECC bits over the 64-bit instruction data as well as the tag are generated and checked by hardware.
However, to enable error injection, the parity/ECC bits must be computed by software for I-cache data and tag array diagnostic writes.
:::

:::{note}
This register is accessible in **Debug Mode only**.
Attempting to access this register in machine mode raises an illegal instruction exception.
:::

This register is mapped to the non-standard read-write CSR address space.

:::{list-table} I-Cache Array Data 0 High Register (dicad0h, at CSR 0x7CC)
:name: tab-cache-array-dicad0h
:header-rows: 1

* - **Field**
  - **Bits**
  - **Description**
  - **Access**
  - **Reset**
* - instr
  - 31:0
  - Instruction data

    31:16: instruction data bytes 7/6 (protected by *parity3* / *ecc*)

    15:0: instruction data bytes 5/4 (protected by *parity2* / *ecc*)
  - R/W
  - 0
:::

### I-Cache Array Data 1 Register (dicad1)

The `dicad1` register, in combination with the `dicad0/0h` registers (see [](cache.md#i-cache-array-data-0-register-dicad0) and [](cache.md#i-cache-array-data-0-high-register-dicad0h)), is used to store information read from or to be written to the I-cache array location specified with the `dicawics` register (see [](cache.md#i-cache-arraywayindex-selection-register-dicawics)).
Triggering a read or write access of the I-cache array is controlled by the `dicago` register (see [](cache.md#i-cache-array-go-register-dicago)).

The layout of the `dicad1` register is described in {numref}`tab-cache-array-dicad1` below.

:::{note}
During normal operation, the parity/ECC bits over the 64-bit instruction data as well as the tag are generated and checked by hardware.
However, to enable error injection, the parity/ECC bits must be computed by software for I-cache data and tag array diagnostic writes.
:::

:::{note}
This register is accessible in **Debug Mode only**.
Attempting to access this register in machine mode raises an illegal instruction exception.
:::

This register is mapped to the non-standard read-write CSR address space.

:::{list-table} I-Cache Array Data 1 Register (dicad1, at CSR 0x7CA).
:name: tab-cache-array-dicad1
:header-rows: 1

* - **Field**
  - **Bits**
  - **Description**
  - **Access**
  - **Reset**
* - **Parity**
  -
  -
  -
  -
* - **Instruction data**
  -
  -
  -
  -
* - Reserved
  - 31:4
  - Reserved
  - R
  - 0
* - parity3
  - 3
  - Even parity for I-cache data bytes 7/6 (*instr[31:16]* in `dicad0h`)
  - R/W
  - 0
* - parity2
  - 2
  - Even parity for I-cache data bytes 5/4 (*instr[15:0]* in `dicad0h`)
  - R/W
  - 0
* - parity1
  - 1
  - Even parity for I-cache data bytes 3/2 (*instr[31:16]* in `dicad0`)
  - R/W
  - 0
* - parity0
  - 0
  - Even parity for I-cache data bytes 1/0 (*instr[15:0]* in `dicad0`)
  - R/W
  - 0
* - **Tag**
  -
  -
  -
  -
* - Reserved
  - 31:1
  - Reserved
  - R
  - 0
* - parity0
  - 0
  - Even parity for I-cache tag (tag)
  - R/W
  - 0
* - **ECC**
  -
  -
  -
  -
* - **Instruction data**
  -
  -
  -
  -
* - Reserved
  - 31:7
  - Reserved
  - R
  - 0
* - ecc
  - 6:0
  - ECC for I-cache data bytes 7/6/5/4/3/2/1/0 (*instr[31:0]* in `dicad0h` and *instr[31:0]* in `dicad0`)
  - R/W
  - 0
* - **Tag**
  -
  -
  -
  -
* - Reserved
  - 31:5
  - Reserved
  - R
  - 0
* - ecc
  - 4:0
  - ECC for I-cache tag (tag)
  - R/W
  - 0
:::

### I-Cache Array Go Register (dicago)

The `dicago` register is used to trigger a read from or write to the I-cache array location specified with the `dicawics` register (see [](cache.md#i-cache-arraywayindex-selection-register-dicawics)).
Reading the `dicago` register populates the `dicad0/dicad0h/dicad1` registers (see [](cache.md#i-cache-array-data-0-register-dicad0), [](cache.md#i-cache-array-data-0-high-register-dicad0h), and [](cache.md#i-cache-array-data-1-register-dicad1)) with the information read from the I-cache array.
Writing a '1' to the go field of the dicago register copies the information stored in the dicad0/dicad0h /dicad1 registers to the I-cache array.
The layout of the dicago register is described in {numref}`tab-cache-array-dicago` below.

:::{note}
This register is accessible in **Debug Mode only**. Attempting to access this register in machine mode raises an illegal instruction exception.
:::

The *go* field of the `dicago` register has W1R0 (Write 1, Read 0) behavior, as also indicated in the 'Access' column.

This register is mapped to the non-standard read-write CSR address space.

:::{list-table} I-Cache Array Go Register (dicago, at CSR 0x7CB)
:name: tab-cache-array-dicago
:header-rows: 1

* - **Field**
  - **Bits**
  - **Description**
  - **Access**
  - **Reset**
* - Reserved
  - 31:1
  - Reserved
  - R
  - 0
* - go
  - 0
  - Read triggers an I-cache read, write-1 triggers an I-cache write
  - R0/W1
  - 0
:::
