# Memory Map

This chapter describes the memory map as well as the various memories and their properties of the VeeR EL2 core.

## Address Regions

The 32-bit address space is subdivided into sixteen fixed-sized, contiguous 256MB regions.
Each region has a set of access control bits associated with it ([](memory-map.md#region-access-control-register-mrac)).

## Access Properties

Each region has two access properties which can be independently controlled. They are:

* **Cacheable:** Indicates if this region is allowed to be cached or not.
* **Side effect:** Indicates if read/write accesses to this region may have side effects (i.e., non-idempotent accesses which may potentially have side effects on any read/write access; typical for I/O, speculative or redundant accesses must be avoided) or have no side effects (i.e., idempotent accesses which have no side effects even if the same access is performed multiple times; typical for memory).
  Note that stores with potential side effects (i.e., to non-idempotent addresses) cannot be combined with other stores in the core's unified read/write buffer.

## Memory Types

There are two different classes of memory types mapped into the core's 32-bit address range, core local and system bus attached.

### Core Local

#### ICCM and DCCM

Two dedicated memories, one for instruction and the other for data, are tightly coupled to the core.
These memories provide low-latency access and SECDED ECC protection.
Their respective sizes (4, 8, 16, 32, 48 [^fn-iccm-dccm-1], 64, 128, 256, or 512KB) are set as arguments at build time of the core.

[^fn-iccm-dccm-1]: DCCM only

#### Local Memory-Mapped Control/Status Registers

To provide control for regular operation, the core requires a number of memory-mapped control/status registers.
For example, some external interrupt functions are controlled and serviced with accesses to various registers while the system is running.

### Accessed via System Bus

#### System ROMs
The SoC may host ROMs which are mapped to the core's memory address range and accessed via the system bus.
Both instruction and data accesses are supported to system ROMs.

#### System SRAMs
The SoC hosts a variety of SRAMs which are mapped to the core's memory address range and accessed via the system bus.

#### System Memory-Mapped I/O

The SoC hosts a variety of I/O device interfaces which are mapped to the core's memory address range and accessed via the system bus.

### Mapping Restrictions

Core-local memories and system bus-attached memories must be mapped to different regions. Mapping both classes of memory types to the same region is not allowed.

Furthermore, it is recommended that all core-local memories are mapped to the same region.

## Memory Type Access Properties

{numref}`tab-access-properites-memory-type` specifies the access properties of each memory type. During system boot, firmware must initialize the properties of each region based on the memory type present in that region.

:::{note}
Some memory-mapped I/O and control/status registers may have no side effects (i.e., are idempotent), but characterizing all these registers as having potentially side effects (i.e., are non-idempotent) is safe.
:::

:::{list-table} Access Properties for each Memory Type
:name: tab-access-properites-memory-type
:header-rows: 1

* - **Region**
  - **Memory Type**
  - **Cacheable**
  - **Side Effect**
* - **Core Local**
  - ICCM
  - No
  - No
* - Core Local
  - DCCM
  - No
  - No
* - Core Local
  - Memory-mapped control/status registers
  - No
  - Yes
* - Accessed via System Bus
  - ROMs
  - Yes
  - No
* - Accessed via System Bus
  - SRAMs
  - Yes
  - No
* - Accessed via System Bus
  - I/Os
  - No
  - Yes
* - Accessed via System Bus
  - Memory-mapped control/status registers
  - No
  - Yes
:::

:::{note}
 'Cacheable = Yes' and 'Side Effect = Yes' is an illegal combination.
:::

## Memory Access Ordering

Loads and stores to system bus-attached memory (i.e. accesses with no side effects, idempotent) and devices (i.e. accesses with potential side effects, non-idempotent) pass through a unified read/write buffer.
The buffer is implemented as a FIFO.

### Load-To-Load and Store-To-Store Ordering

All loads are sent to the system bus interface in program order. Also, all stores are sent to the system bus interface in program order.

### Load/Store Ordering

#### Accesses with Potential Side Effects (i.e., Non-Idempotent)

When a load with potential side effects (i.e., non-idempotent) enters the buffer, the entire unified buffer is emptied, i.e., both stores with no side effects (i.e., idempotent) and with potential side effects (i.e., non-idempotent) are drained out.
Loads with potential side effects (i.e., non-idempotent) are sent out to the system bus with their exact size.

Stores with potential side effects (i.e., non-idempotent) are neither coalesced nor forwarded to a load.

#### Accesses with No Side Effects (i.e., Idempotent)

Loads with no side effects (i.e., idempotent) are always issued as double-words and check the contents of the unified buffer:

1. **Full address match** (all load bytes present in the unified buffer): Data is forwarded from the unified buffer.
   The load does not go out to the system bus.
2. **Partial address match** (some of the load bytes are in the unified buffer): The entire unified buffer is emptied, then the load request goes to the system bus.
3. **No match** (none of the bytes are in the unified buffer): The load is presented to the system bus interface without waiting for the stores to drain.

#### Ordering of Store - Load with No Side Effects (i.e., Idempotent)

A `fence` instruction is required to order an older store before a younger load with no side effects (i.e., idempotent).

:::{note}
 All memory-mapped register writes must be followed by a `fence` instruction to enforce ordering and synchronization.
:::

### Fencing

#### Instructions

The `fence.i` instruction operates on the instruction memory and/or I-cache.
This instruction causes a flush, a flash invalidation of the I-cache, and a refetch of the next program counter (RFNPC).
The refetch is guaranteed to miss the I-cache.
Note that since the `fence.i` instruction is used to synchronize the instruction and data streams, it also includes the functionality of the `fence` instruction (see [](memory-map.md#data)).

#### Data

The `fence` instruction is implemented conservatively in VeeR EL2 to keep the implementation simple.
It always performs the most conservative fencing, independent of the instruction's arguments.
The `fence` instruction is presynced to make sure that there are no instructions in the LSU pipe.
It stalls until the LSU indicates that the store buffer and unified buffer have been fully drained (i.e., are empty).
The `fence` instruction is only committed after all LSU buffers are idle and all outstanding bus transactions are completed.

### Imprecise Data Bus Errors

All store errors as well as non-blocking load errors on the system bus are imprecise.
The address of the first occurring imprecise data system bus error is logged and a non-maskable interrupt (NMI) is flagged for the first reported error only.
For stores, if there are other stores in the unified buffer behind the store which had the error, these stores are sent out on the system bus and any error responses are ignored.
Similarly, for non-blocking loads, any error responses on subsequent loads sent out on the system bus are ignored.
NMIs are fatal, architectural state is lost, and the core needs to be reset.
The reset also unlocks the first error address capture register again.

:::{note}
 It is possible to unlock the first error address capture register with a write to an unlock register as well (see [](memory-map.md#d-bus-error-address-unlock-register-mdeau) for more details), but this may result in unexpected behavior.
:::

## Memory Protection

To eliminate issuing speculative accesses to the IFU and LSU bus interfaces, VeeR EL2 provides a rudimentary memory protection mechanism for instruction and data accesses outside of the ICCM and DCCM memory regions.
Separate core build arguments for instructions and data are provided by the Memory Protection Unit (MPU) to enable and configure up to 8 address windows each.

An instruction fetch to a non-ICCM region must fall within the address range of at least one instruction access window for the access to be forwarded to the IFU bus interface.
If at least one instruction access window is enabled, nonspeculative fetch requests which are not within the address range of any enabled instruction access window cause a precise instruction access fault exception.
If none of the 8 instruction access windows is enabled, the memory protection mechanism for instruction accesses is turned off.
For the ICCM region, accesses within the ICCM's address range are allowed.
However, any access not within the ICCM's address range results in a precise instruction access fault exception.

Similarly, a load/store access to a non-DCCM or non-PIC memory-mapped control register region must fall within the address range of at least one data access window for the access to be forwarded to the LSU bus interface.
If at least one data access window is enabled, non-speculative load/store requests which are not within the address range of any enabled data access window cause a precise load/store address misaligned or access fault exception.
If none of the 8 data access windows is enabled, the memory protection mechanism for data accesses is turned off.
For the DCCM and PIC memory-mapped control register region(s), accesses within the DCCM's or the PIC memory-mapped control register's address range are allowed.
However, any access not within the DCCM's or PIC memory-mapped control register's address range results in a precise load/store address misaligned or access fault exception.

The configuration parameters for each of the 8 instruction and 8 data access windows are:

* Enable/disable instruction/data access window 0..7,
* a base address of the window (which must be 64B-aligned), and
* a mask specifying the size of the window (which must be an integer-multiple of 64 bytes minus 1).

See [](build-args.md#memory-protection-build-arguments) for more information.

## Exception Handling

Capturing the faulting effective address causing an exception helps assist firmware in handling the exception and/or provides additional information for firmware debugging.
For precise exceptions, the faulting effective address is captured in the standard RISC-V `mtval` register (see Section 3.1.17 in [[2]](intro.md#ref-2)).
For imprecise exceptions, the address of the first occurrence of the error is captured in a platform-specific error address capture register (see [](memory-map.md#d-bus-first-error-address-capture-register-mdseac)).

### Imprecise Bus Error Non-Maskable Interrupt

Store bus errors are fatal and cause a non-maskable interrupt (NMI).
The store bus error NMI has an `mcause` value of 0xF000_0000.

Likewise, non-blocking load bus errors are fatal and cause a non-maskable interrupt (NMI).
The non-blocking load bus error NMI has an `mcause` value of 0xF000_0001.

:::{note}
The address of the first store or non-blocking load error on the D-bus is captured in the `mdseac` register (see [](memory-map.md#d-bus-first-error-address-capture-register-mdseac)).
The register is unlocked either by resetting the core after the NMI has been handled or by a write to the `mdeau` register (see [](memory-map.md#d-bus-error-address-unlock-register-mdeau)).
While the `mdseac` register is locked, subsequent D-bus errors are gated (i.e., they do not cause another NMI), but NMI requests originating external to the core are still honored.
:::

:::{note}
The AXI4 bus is able to report a load bus error and a store bus error simultaneously.
If store and non-blocking load bus errors are reported in the same clock cycle, the store bus error has higher priority.
:::

### Correctable Error Local Interrupt

I-cache parity/ECC errors, ICCM correctable ECC errors, and DCCM correctable ECC errors are counted in separate correctable error counters (see sections [I-Cache Error Counter/Threshold Register (micect)](error-protection.md#i-cache-error-counter-threshold-register-micect), [Iccm Correctable Error Counter/Threshold Register (miccmect)](error-protection.md#iccm-correctable-error-counter-threshold-register-miccmect), and [Dccm Correctable Error Counter/Threshold Register (mdccmect)](error-protection.md#dccm-correctable-error-counter-threshold-register-mdccmect), respectively).
Each counter also has its separate programmable error threshold.
If any of these counters has reached its threshold, a correctable error local interrupt is signaled.
Firmware should determine which of the counters has reached the threshold and reset that counter.

A local-to-the-core interrupt for correctable errors has pending (*mceip*) and enable (*mceie*) bits in bit position 30 of the standard RISC-V `mip` (see {numref}`tab-machine-interrupt-pending-register`) and `mie` (see {numref}`tab-machine-interrupt-enable-register`) registers, respectively.
The priority is lower than the RISC-V External interrupt, but higher than the RISC-V Software and Timer interrupts, (see {numref}`tab-veer-el2-platform-specific-and-std-risc-v-interrupt-priorities`).
The correctable error local interrupt has an `mcause` value of 0x8000_001E (see {numref}`tab-machine-cause-register`).

### Rules for Core-Local Memory Accesses

The rules for instruction fetch and load/store accesses to core-local memories are:

1. An instruction fetch access to a region
    1. containing one or more ICCM sub-region(s)causes an exception if
        1. the access is not completely within the ICCM sub-region, or
        1. the boundary of an ICCM to a non-ICCM sub-region and vice versa is crossed, even if the region contains a DCCM/PIC memory-mapped control register sub-region.
    1. not containing an ICCM sub-region goes out to the system bus, even if the region contains a DCCM/PIC memory-mapped control register sub-region.

1. A load/store access to a region
    1. containing one or more DCCM/PIC memory-mapped control register sub-region(s) causes an exception if
        1. the access is not completely within the DCCM/PIC memory-mapped control register subregion, or
        1. the boundary of
            1. a DCCM to a non-DCCM sub-region and vice versa, or
            1. a PIC memory-mapped control register sub-region is crossed, even if the region contains an ICCM sub-region.
    1. not containing a DCCM/PIC memory-mapped control register sub-region goes out to the system bus, even if the region contains an ICCM sub-region.

### Core-Local / D-Bus Access Prediction

In VeeR EL2, a prediction is made early in the pipeline if the access is to a core-local address (i.e., DCCM or PIC memory-mapped register) or to the D-bus (i.e., a memory or register address of the SoC).
The prediction is based on the base address (i.e., value of register *rs1*) of the load/store instruction.
Later in the pipeline, the actual address is calculated also taking the offset into account (i.e., value of register *rs1 + offset*).
A mismatch of the predicted and the actual destination (i.e., a core-local or a D-bus access) results in a load/store access fault exception.

### Unmapped Addresses

:::{list-table} Handling of Unmapped Addresses
:name: tab-handling-unmapped-addresses
:header-rows: 1

* - **Access**
  - **Core/Bus**
  - **Side Effect**
  - **Action**
  - **Comments**
* - Fetch
  - Core
  - N/A
  - Instruction access fault exception [^fn-unmapped-address-1], [^fn-unmapped-address-2]
  - Precise exception (e.g., address out-of-range)
* - Fetch
  - Bus
  - N/A
  - Instruction access fault exception [^fn-unmapped-address-1]
  - Precise exception (e.g., address out-of-range)
* - Load
  - Core
  - No
  - Load access fault exception [^fn-unmapped-address-3], [^fn-unmapped-address-4]
  - Precise exception (e.g., address out-of-range)
* - Load
  - Bus
  - No
  - non-blocking load bus error nmi (see [](memory-map.md#imprecise-bus-error-non-maskable-interrupt))
  -
    - imprecise, fatal
    - capture load address in core bus interface
* - Load
  - Bus
  - Yes
  - non-blocking load bus error nmi (see [](memory-map.md#imprecise-bus-error-non-maskable-interrupt))
  -
    - imprecise, fatal
    - capture load address in core bus interface
* - Store
  - Core
  - No
  - Store/AMO [^fn-unmapped-address-5] access fault exception [^fn-unmapped-address-3], [^fn-unmapped-address-4]
  - Precise exception
* - Store
  - Bus
  - No
  - Store bus error NMI (see [](memory-map.md#imprecise-bus-error-non-maskable-interrupt))
  -
    - Imprecise, fatal
    - Capture store address in core bus interface
* - Store
  - Bus
  - Yes
  - Store bus error NMI (see [](memory-map.md#imprecise-bus-error-non-maskable-interrupt))
  -
    - Imprecise, fatal
    - Capture store address in core bus interface
* - DMA Read / DMA Write
  - Bus
  - N/A
  - DMA slave bus error
  - Send error response to master
:::

:::{note}
 It is recommended to provide address gaps between different memories to ensure unmapped address
:::

[^fn-unmapped-address-1]: If any byte of an instruction is from an unmapped address, an instruction access fault precise exception is flagged.
[^fn-unmapped-address-2]: Exception also flagged for fetches to the DCCM address range if located in the same region, or if located in different regions and no SoC address is a match.
[^fn-unmapped-address-3]: Exception also flagged for PIC load/store not word-sized or address not word-aligned.
[^fn-unmapped-address-4]: Exception also flagged for loads/stores to the ICCM address range if located in the same region, or if located in different regions and no SoC address is a match.
[^fn-unmapped-address-5]: AMO refers to the RISC-V "A" (atomics) extension, which is not implemented in VeeR EL2.

### Misaligned Accesses

General notes:
* The core performs a misalignment check during the address calculation.
* Accesses across region boundaries always cause a misaligned exception.
* Splitting a load/store from/to an address with no side effects (i.e., idempotent) is not of concern for VeeR EL2.

:::{list-table} Handling of Misaligned Accesses
:name: tab-handling-misaligned-addresses
:header-rows: 1

* - **Access**
  - **Core/Bus**
  - **Side Effect**
  - **Region Cross**
  - **Action**
  - **Comments**
* - Fetch
  - Core
  - N/A
  - No
  - N/A
  - Not possible [^fn-misaligned-accesses-1]
* - Fetch
  - Bus
  - N/A
  - No
  - N/A
  - Not possible [^fn-misaligned-accesses-1]
* - Load
  - Core
  - No
  - No
  - Load split into multiple DCCM read accesses
  - Split performed by core
* - Load
  - Bus
  - No
  - No
  - Load split into multiple bus transactions
  - Split performed by core
* - Load
  - Bus
  - Yes [^fn-misaligned-accesses-2]
  - No
  - Load address misaligned exception
  - Precise exception
* - Store
  - Core
  - No
  - No
  - Store split into multiple DCCM write accesses
  - Split performed by core
* - Store
  - Bus
  - No
  - No
  - Store split into multiple bus transactions
  - Split performed by core
* - Store
  - Bus
  - Yes [^fn-misaligned-accesses-2]
  - No
  - Store/AMO address misaligned exception
  - Precise exception
* - Fetch
  - N/A
  - N/A
  - Yes
  - N/A
  - Not possible [^fn-misaligned-accesses-1]
* - Load
  - N/A
  - N/A
  - Yes
  - Load address misaligned exception
  - Precise exception
* - Store
  - N/A
  - N/A
  - Yes
  - Store/AMO address misaligned exception
  - Precise exception
* - DMA Read
  - Bus
  - N/A
  - N/A
  - DMA slave bus error
  - Send error response to master
* - DMA Write [^fn-misaligned-accesses-3]
  - Bus
  - N/A
  - N/A
  - DMA slave bus error
  - Send error response to master
:::

[^fn-misaligned-accesses-1]: Accesses to the I-cache or ICCM initiated by fetches never cross 16B boundaries. I-cache fills are always aligned to 64B. Misaligned accesses are therefore not possible.
[^fn-misaligned-accesses-2]: The RISC-V Privileged specification recommends that misaligned accesses to regions with potential side-effects should trigger an access fault exception, instead of a misaligned exception (see Section 3.5.6 in [[2]](intro.md#ref-2)). Note that VeeR EL2 triggers a misaligned exception in this case. To avoid potential side-effects, the exception handler should not emulate a misaligned access using multiple smaller aligned accesses.
[^fn-misaligned-accesses-3]: This case is in violation with the write alignment rules specified in section [](memory-map.md#write-alignment-rules).

### Uncorrectable Ecc Errors

:::{list-table} Handling of Uncorrectable ECC Errors
:name: tab-handling-uncorrectable-ecc-errors
:header-rows: 1

* - **Access**
  - **Core/Bus**
  - **Side Effect**
  - **Action**
  - **Comments**
* - Fetch
  - Core
  - N/A
  - Instruction access fault exception
  - Precise exception (i.e., for oldest instruction in pipeline only)
* - Fetch
  - Bus
  - N/A
  - Instruction access fault exception
  - Precise exception (i.e., for oldest instruction in pipeline only)
* - Load
  - Core
  - No
  - Load access fault exception
  - Precise exception (i.e., for non-speculative load only)
* - Load
  - Core
  - Yes
  - Load access fault exception
  - Precise exception (i.e., for non-speculative load only)
* - Load
  - Bus
  - No
  - Non-blocking load bus error NMI (see [](memory-map.md#imprecise-bus-error-non-maskable-interrupt))
  -
    - Imprecise, fatal
    - Capture load address in core bus interface
* - Load
  - Bus
  - Yes
  - Non-blocking load bus error NMI (see [](memory-map.md#imprecise-bus-error-non-maskable-interrupt))
  -
    - Imprecise, fatal
    - Capture load address in core bus interface
* - Store
  - Core
  - No
  - Store/AMO access fault exception
  - Precise exception (i.e., for non-speculative store only)
* - Store
  - Core
  - Yes
  - Store/AMO access fault exception
  - Precise exception (i.e., for non-speculative store only)
* - Store
  - Bus
  - No
  - Store bus error NMI (see [](memory-map.md#imprecise-bus-error-non-maskable-interrupt))
  -
    - Imprecise, fatal
    - Capture store address in core bus interface
* - Store
  - Bus
  - Yes
  - Store bus error NMI (see [](memory-map.md#imprecise-bus-error-non-maskable-interrupt))
  -
    - Imprecise, fatal
    - Capture store address in core bus interface
* - DMA Read
  - Bus
  - N/A
  - DMA slave bus error
  - Send error response to master
:::

:::{note}
DMA write accesses to the ICCM or DCCM always overwrite entire 32-bit words and their corresponding ECC bits.
Therefore, ECC bits are never checked and errors not detected on DMA writes.
:::

### Correctable Ecc/Parity Errors

:::{list-table} Handling of Correctable ECC/Parity Errors Access Core/Bus Side Effect Action
:name: tab-handling-correctable-ecc-errors
:header-rows: 1

* - **Access**
  - **Core/Bus**
  - **Side Effect**
  - **Action**
  - **Comments**
* - Fetch
  - Core
  - N/A
  - For I-cache accesses:
    - Increment correctable I-cache error counter in core
    - If I-cache error threshold reached, signal correctable error local interrupt (see [I-Cache Error Counter/Threshold Register (micect)](error-protection.md#i-cache-error-counter-threshold-register-micect))
    - Invalidate all cache lines of set
    - Perform RFPC flush
    - Flush core pipeline
    - Refetch cache line from SoC memory
  -
    - For all fetches from I-cache (i.e., out of pipeline, independent of actual instruction execution)
    - For I-cache with tag/instruction ECC protection, single- and double-bit errors are recoverable
* - Fetch
  - Core
  - N/A
  - For ICCM accesses:
    - Increment correctable ICCM error counter in core
    - If ICCM error threshold reached, signal correctable error local interrupt (see [Iccm Correctable Error Counter/Threshold Register (miccmect)](error-protection.md#iccm-correctable-error-counter-threshold-register-miccmect))
    - Perform RFPC flush
    - Flush core pipeline
    - Write corrected data back to ICCM
    - Refetch instruction(s) from ICCM
  -
    - For all fetches from ICCM (i.e., out of pipeline, independent of actual instruction execution)
    - ICCM errors trigger an RFPC (ReFetch PC) flush since in-line correction would require an additional cycle
* - Fetch
  - Bus
  - N/A
  -
    - Increment correctable error counter in SoC
    - If error threshold reached, signal external interrupt
    - Write corrected data back to SoC memory
  - Errors in SoC memories are corrected at memory boundary and autonomously written back to memory array
* - Load
  - Core
  - No
  -
    - Increment correctable DCCM error counter in core
    - If DCCM error threshold reached, signal correctable error local interrupt (see [Dccm Correctable Error Counter/Threshold Register (mdccmect)](error-protection.md#dccm-correctable-error-counter-threshold-register-mdccmect))
    - Write corrected data back to DCCM
  -
    - For non-speculative accesses only
    - DCCM errors are in-line corrected and written back to DCCM
* - Load
  - Core
  - Yes
  -
    - Increment correctable DCCM error counter in core
    - If DCCM error threshold reached, signal correctable error local interrupt (see [Dccm Correctable Error Counter/Threshold Register (mdccmect)](error-protection.md#dccm-correctable-error-counter-threshold-register-mdccmect))
    - Write corrected data back to DCCM
  -
    - For non-speculative accesses only
    - DCCM errors are in-line corrected and written back to DCCM
* - Load
  - Bus
  - No
  -
    - Increment correctable error counter in SoC
    - If error threshold reached, signal external interrupt
    - Write corrected data back to SoC memory
  - Errors in SoC memories are corrected at memory boundary and autonomously written back to memory array
* - Load
  - Bus
  - Yes
  -
    - Increment correctable error counter in SoC
    - If error threshold reached, signal external interrupt
    - Write corrected data back to SoC memory
  - Errors in SoC memories are corrected at memory boundary and autonomously written back to memory array
* - Store
  - Core
  - No
  -
    - Increment correctable dccm error counter in core
    - If dccm error threshold reached, signal correctable error local interrupt (see [Dccm Correctable Error Counter/Threshold Register (mdccmect)](error-protection.md#dccm-correctable-error-counter-threshold-register-mdccmect))
    - Write corrected data back to dccm
  -
    - For non-speculative accesses only
    - Dccm errors are in-line corrected and written back to dccm
* - Store
  - Core
  - Yes
  -
    - Increment correctable dccm error counter in core
    - If dccm error threshold reached, signal correctable error local interrupt (see [Dccm Correctable Error Counter/Threshold Register (mdccmect)](error-protection.md#dccm-correctable-error-counter-threshold-register-mdccmect))
    - Write corrected data back to dccm
  -
    - For non-speculative accesses only
    - Dccm errors are in-line corrected and written back to dccm
* - Store
  - Bus
  - No
  -
    - Increment correctable error counter in SoC
    - If error threshold reached, signal external interrupt
    - Write corrected data back to SoC memory
  - Errors in SoC memories are corrected at memory boundary and autonomously written back to memory array
* - Store
  - Bus
  - Yes
  -
    - Increment correctable error counter in SoC
    - If error threshold reached, signal external interrupt
    - Write corrected data back to SoC memory
  - Errors in SoC memories are corrected at memory boundary and autonomously written back to memory array
* - DMA Read
  - Bus
  - N/A
  - For ICCM accesses:
    - Increment correctable ICCM error counter in core
    - If ICCM error threshold reached, signal correctable error local interrupt (see [Iccm Correctable Error Counter/Threshold Register (miccmect)](error-protection.md#iccm-correctable-error-counter-threshold-register-miccmect))
    - Write corrected data back to ICCM
  - DMA read access errors to ICCM are in-line corrected and written back to ICCM
* - DMA Read
  - Bus
  - N/A
  - For DCCM accesses:
    - Increment correctable DCCM error counter in core
    - If DCCM error threshold reached, signal correctable error local interrupt (see [Dccm Correctable Error Counter/Threshold Register (mdccmect)](error-protection.md#dccm-correctable-error-counter-threshold-register-mdccmect))
    - Write corrected data back to DCCM
  - DMA read access errors to DCCM are in-line corrected and written back to DCCM
:::

:::{note}
Counted errors could be from different, unknown memory locations.
:::

:::{note}
DMA write accesses to the ICCM or DCCM always overwrite entire 32-bit words and their corresponding ECC bits.
Therefore, ECC bits are never checked and errors not detected on DMA writes.
:::

## Control/Status Registers

A summary of platform-specific control/status registers in CSR space:

* [](memory-map.md#region-access-control-register-mrac)
* [](memory-map.md#memory-synchronization-trigger-register-dmst)
* [](memory-map.md#d-bus-first-error-address-capture-register-mdseac)
* [](memory-map.md#d-bus-error-address-unlock-register-mdeau)
* [](memory-map.md#machine-secondary-cause-register-mscause)

All reserved and unused bits in these control/status registers must be hardwired to '0'. Unless otherwise noted, all read/write control/status registers must have WARL (Write Any value, Read Legal value) behavior.

### Region Access Control Register (mrac)

A single region access control register is sufficient to provide independent control for 16 address regions.

:::{note}
To guarantee that updates to the `mrac` register are in effect, if a region being updated is in the load/store space, a `fence` instruction is required.
Likewise, if a region being updated is in the instruction space, a `fence.i` instruction (which flushes the I-cache) is required.
:::

:::{note}
The *sideeffect* access control bits are ignored by the core for load/store accesses to addresses mapped to core-local memories (i.e., DCCM and ICCM) and PIC memory-mapped control registers as well as for all instruction fetch accesses.
The *cacheable* access control bits are ignored for instruction fetch accesses from addresses mapped to the ICCM, but not for any other addresses.
:::

:::{note}
The combination '11' (i.e., side effect and cacheable) is illegal. Writing '11' is mapped by hardware to the legal value '10' (i.e., side effect and non-cacheable).
:::

This register is mapped to the non-standard read/write CSR address space.

:::{list-table} Region Access Control Register (mrac, at CSR 0x7C0)
:name: tab-region-access-control-register
:header-rows: 1

* - **Field**
  - **Bits**
  - **Description**
  - **Access**
  - **Reset**
* - Y = 0..15 (= Region)
  -
  -
  -
  -
* - sideeffectY
  - Y*2+1
  - Side effect indication for region Y:
    - 0: No side effects (idempotent)
    - 1: Side effects possible (non-idempotent)
  - R/W
  - 0
* - cacheableY
  - Y*2
  - Caching control for region Y:
    - 0: Caching not allowed
    - 1: Caching allowed
  - R/W
  - 0
:::

### Memory Synchronization Trigger Register (dmst)

The `dmst` register provides triggers to force the synchronization of memory accesses. Specifically, it allows a debugger to initiate operations that are equivalent to the `fence.i` (see [](memory-map.md#instructions)) and `fence` (see [](memory-map.md#data)) instructions.

:::{note}
 This register is accessible in **Debug Mode only**. Attempting to access this register in machine mode raises an illegal instruction exception.
:::

The *fence_i* and *fence* fields of the `dmst` register have W1R0 (Write 1, Read 0) behavior, as also indicated in the
'Access' column.

This register is mapped to the non-standard read/write CSR address space.

:::{list-table} Memory Synchronization Trigger Register (dmst, at CSR 0x7C4)
:name: tab-memory-synchronization-trigger-register
:header-rows: 1

* - **Field**
  - **Bits**
  - **Description**
  - **Access**
  - **Reset**
* - Reserved
  - 31:2
  - Reserved
  - R
  - 0
* - fence
  - 1
  - Trigger operation equivalent to `fence` instruction
  - R0/W1
  - 0
* - fence_i
  - 0
  - Trigger operation equivalent to `fence.i` instruction
  - R0/W1
  - 0
:::

### D-Bus First Error Address Capture Register (mdseac)

The address of the first occurrence of a store or non-blocking load error on the D-bus is captured in the `mdseac` register. Latching the address also locks the register. 
While the `mdseac` register is locked, subsequent D-bus errors are gated (i.e., they do not cause another NMI), but NMI requests originating external to the core are still honored.

The `mdseac` register is unlocked by either a core reset (which is the safer option) or by writing to the `mdeau` register (see [](memory-map.md#d-bus-error-address-unlock-register-mdeau)).

:::{note}
The address captured in this register is the target (i.e., base) address of the store or non-blocking load which experienced an error.
:::

:::{note}
The NMI handler may use the value stored in the `mcause` register to differentiate between a D-bus store error, a D-bus non-blocking load error, and a core-external event triggering an NMI.
:::

:::{note}
Capturing an address of a store or non-blocking load D-bus error in the `mdseac` register is independent of the actual taking of an NMI due to the bus error.
For example, if a request on the NMI pin arrives just prior to the detection of a store or non-blocking load error on the D-bus, the address of the bus error may still be logged in the `mdseac` register.
:::

This register is mapped to the non-standard read-only CSR address space.

:::{list-table} D-Bus First Error Address Capture Register (mdseac, at CSR 0xFC0)
:name: tab-d-bus-first-error-address-capture-register
:header-rows: 1

* - **Field**
  - **Bits**
  - **Description**
  - **Access**
  - **Reset**
* - erraddr
  - 31:0
  - Address of first occurrence of D-bus store or non-blocking load error
  - R
  - 0
:::

### D-Bus Error Address Unlock Register (mdeau)

Writing to the `mdeau` register unlocks the `mdseac` register (see [](memory-map.md#d-bus-first-error-address-capture-register-mdseac)) after a D-bus error address has been captured.
This write access also reenables the signaling of an NMI for a subsequent D-bus error.

:::{note}
Nested NMIs might destroy core state and, therefore, receiving an NMI should still be considered fatal.
Issuing a core reset is a safer option to deal with a D-bus error.
:::

The `mdeau` register has WAR0 (Write Any value, Read 0) behavior.
Writing '0' is recommended.

This register is mapped to the non-standard read/write CSR address space.

:::{list-table} D-Bus Error Address Unlock Register (mdeau, at CSR 0xBC0)
:name: tab-d-bus-error-address-unlock-register
:header-rows: 1

* - **Field**
  - **Bits**
  - **Description**
  - **Access**
  - **Reset**
* - erraddr
  - 31:0
  - Address of first occurrence of D-bus store or non-blocking load error
  - R
  - 0
:::

### Machine Secondary Cause Register (mscause)

The `mscause` register, in conjunction with the standard RISC-V `mcause` register (see [](adaptations.md#machine-cause-register-mcause)), allows the determination of the exact cause of a trap for cases where multiple, different conditions share a single trap code.
The standard RISC-V mcause register provides the trap code and the `mscause` register provides supporting information about the trap to disambiguate different sources.
A value of '0' indicates that there is no additional information available.
{numref}`tab-machine-secondary-cause-register` lists VeeR EL2's standard exceptions/interrupts (regular text), platform-specific local interrupts (italic text), and NMI causes (bold text).

The `mscause` register has WLRL (Write Legal value, Read Legal value) behavior.

:::{note}
VeeR EL2 implements only the 4 least-significant bits of the mscause register (i.e., `mscause[3:0]`).
Writes to all higher bits are ignored, reads return 0 for those bits.
:::

This register is mapped to the non-standard read/write CSR address space.

:::{list-table} Machine Secondary Cause Register (mscause, at CSR 0x7FF)
:name: tab-machine-secondary-cause-register
:header-rows: 1

* - **mcause**
  - **mcause Description**
  - **mscause (Rel. Priority)** [^fn-mscause-register-1]
  - **mscause Description**
  - **Section(s)**
* - **Exceptions**
  -
  -
  -
  -
* - 0x1
  - Instruction access fault
  - 0x9 (2)
  - I-side fetch precise bus error
  - [](memory-map.md#unmapped-addresses) and [](error-protection.md#error-detection-and-handling)
* - 0x1
  - Instruction access fault
  - 0x1 (3)
  - I-side ICCM double-bit ECC error
  - [](memory-map.md#uncorrectable-ecc-errors) and [](error-protection.md#error-detection-and-handling)
* - 0x1
  - Instruction access fault
  - 0x2 (0)
  - I-side core-local [^fn-mscause-register-2] unmapped address error
  - [](memory-map.md#unmapped-addresses) and [](error-protection.md#error-detection-and-handling)
* - 0x1
  - Instruction access fault
  - 0x3 (1)
  - I-side access out of MPU range
  - [](memory-map.md#memory-protection)
* - 0x2
  - Illegal instruction
  - 0x0
  - None
  - N/A
* - 0x3
  - Breakpoint
  - 0x2
  - ebreak (not to Debug Mode)
  - N/A
* - 0x3
  - Breakpoint
  - 0x1
  - Trigger hit [^fn-mscause-register-3] (not to Debug Mode)
  - N/A
* - 0x4
  - Load address misaligned
  - 0x2 (0)
  - D-side load across region boundary
  - [](memory-map.md#misaligned-accesses)
* - 0x4
  - Load address misaligned
  - 0x1 (1)
  - D-side size-misaligned load to non-idempotent address
  - [](memory-map.md#misaligned-accesses)
* - 0x5
  - Load access fault
  - 0x2 (0)
  - D-side core-local [^fn-mscause-register-4], [^fn-mscause-register-5] load unmapped address error
  - [](memory-map.md#unmapped-addresses) and [](error-protection.md#error-detection-and-handling)
* - 0x5
  - Load access fault
  - 0x1 (4)
  - D-side DCCM load double-bit ECC error
  - [](memory-map.md#uncorrectable-ecc-errors) and [](error-protection.md#error-detection-and-handling)
* - 0x5
  - Load access fault
  - 0x3 (1)
  - D-side load access out of MPU range
  - [](memory-map.md#memory-protection)
* - 0x5
  - Load access fault
  - 0x5 (2)
  - D-side load region prediction error
  - [Core-Local / D-Bus Access Prediction](memory-map.md#core-local-d-bus-access-prediction)
* - 0x5
  - Load access fault
  - 0x6 (3)
  - D-side PIC [^fn-mscause-register-6] load access error
  - [](memory-map.md#unmapped-addresses)
* - 0x6
  - Store/AMO address misaligned
  - 0x2 (0)
  - D-side store across region boundary
  - [](memory-map.md#misaligned-accesses)
* - 0x6
  - Store/AMO address misaligned
  - 0x1 (1)
  - D-side size-misaligned store to non-idempotent address
  - [](memory-map.md#misaligned-accesses)
* - 0x7
  - Store/AMO access fault
  - 0x2 (0)
  - D-side core-local [^fn-mscause-register-4], [^fn-mscause-register-5] store unmapped address error
  - [](memory-map.md#unmapped-addresses) and [](error-protection.md#error-detection-and-handling)
* - 0x7
  - Store/AMO access fault
  - 0x1 (4)
  - D-side DCCM store double- bit ECC error
  - [](memory-map.md#uncorrectable-ecc-errors) and [](error-protection.md#error-detection-and-handling)
* - 0x7
  - Store/AMO access fault
  - 0x3 (1)
  - D-side store access out of MPU range
  - [](memory-map.md#memory-protection)
* - 0x7
  - Store/AMO access fault
  - 0x5 (2)
  - D-side store region prediction error
  - [Core-Local / D-Bus Access Prediction](memory-map.md#core-local-d-bus-access-prediction)
* - 0x7
  - Store/AMO access fault
  - 0x6 (3)
  - D-side PIC [^fn-mscause-register-6] store access error
  - [](memory-map.md#unmapped-addresses)
* - 0xB
  - Environment call from M- mode
  - 0x0
  - None
  - N/A
* - **Interrupts**
  -
  -
  -
  -
* - 0x8000_0003
  - Machine software interrupt
  - 0x0
  - Machine software
  - [](memory-map.md#software-interrupts)
* - 0x8000_0007
  - Machine timer [^fn-mscause-register-7] interrupt
  - 0x0
  - Machine timer
  - N/A
* - 0x8000_000B
  - Machine external interrupt
  - 0x0
  - External interrupt
  - [](interrupts.md)
* - *0x8000_001C*
  - *Machine internal timer 1 local interrupt*
  - 0x0
  - *Internal timer 1 local interrupt*
  - [](timers.md#internal-timer-local-interrupts)
* - *0x8000_001D*
  - *Machine internal timer 0 local interrupt*
  - 0x0
  - *Internal timer 0 local interrupt*
  - [](timers.md#internal-timer-local-interrupts)
* - *0x8000_001E*
  - *Machine correctable error local interrupt*
  - 0x0
  - *Correctable error local interrupt*
  - [](memory-map.md#correctable-error-local-interrupt)
* - **0x0000_0000**
  - **NMI**
  - **0x0**
  - **NMI pin assertion**
  - [](memory-map.md#non-maskable-interrupt-nmi-signal-and-vector)
* - **0xF000_0000**
  - **NMI**
  - **0x0**
  - **D-bus store error**
  - [](memory-map.md#imprecise-bus-error-non-maskable-interrupt) and [](memory-map.md#non-maskable-interrupt-nmi-signal-and-vector)
* - **0xF000_0001**
  - **NMI**
  - **0x0**
  - **D-bus non-blocking load error**
  - [](memory-map.md#imprecise-bus-error-non-maskable-interrupt) and [](memory-map.md#non-maskable-interrupt-nmi-signal-and-vector)
* - **0xF000_1000**
  - **NMI**
  - **0x0**
  - **Fast Interrupt double-bit ECC error**
  - [](interrupts.md#fast-interrupt-redirect) and [](memory-map.md#non-maskable-interrupt-nmi-signal-and-vector)
* - **0xF000_1001**
  - **NMI**
  - **0x0**
  - **Fast Interrupt DCCM region access error**
  - [](interrupts.md#fast-interrupt-redirect) and [](memory-map.md#non-maskable-interrupt-nmi-signal-and-vector)
* - **0xF000_1002**
  - **NMI**
  - **0x0**
  - **Fast Interrupt non-DCCM region**
  - [](interrupts.md#fast-interrupt-redirect) and [](memory-map.md#non-maskable-interrupt-nmi-signal-and-vector)
:::

:::{note}
 All other values are reserved.
:::

[^fn-mscause-register-1]: Relative priority of load/store exceptions (0: highest priority).
[^fn-mscause-register-2]: Fetch access not within ICCM address range.
[^fn-mscause-register-3]: Trigger hit can also be observed in *hit* bit of mcontrol register (see {numref}`tab-mcontrol`).
[^fn-mscause-register-4]: Load/store access not within DCCM or PIC memory-mapped register address ranges.
[^fn-mscause-register-5]: If a load or store access crosses the upper boundary of either the DCCM or PIC memory-mapped register address range, the error address reported in the mtval register is the base address of the access, not the address of the first byte outside the DCCM or PIC range. Note that firmware cannot recover from this access fault independent of which address is reported.
[^fn-mscause-register-6]: PIC load/store not word-sized or address not word-aligned.
[^fn-mscause-register-7]: Core external timer

## Memory Address Map

{numref}`tab-veer-el2-memory-address-map` summarizes an example of the VeeR EL2 memory address map, including regions as well as start and end addresses for the various memory types.

:::{list-table} VeeR EL2 Memory Address Map (Example)
:name: tab-veer-el2-memory-address-map
:header-rows: 1

* - **Region**
  - **Start Address**
  - **End Address**
  - **Memory Type**
* - 0x0
  - 0x0000_0000
  - 0x0003_FFFF
  - Reserved
* - 0x0
  - 0x0004_0000
  - 0x0005_FFFF
  - ICCM (region: 0, offset: 0x4000, size: 128KB)
* - 0x0
  - 0x0006_0000
  - 0x0007_FFFF
  - Reserved
* - 0x0
  - 0x0008_0000
  - 0x0009_FFFF
  - DCCM (region: 0, offset: 0x8000, size: 128KB)
* - 0x0
  - 0x000A_0000
  - 0x0FFF_FFFF
  - Reserved
* - 0x1
  - 0x1000_0000
  - 0x1FFF_FFFF
  - System memory-mapped CSRs
* - 0x2
  - 0x2000_0000
  - 0x2FFF_FFFF
  - System SRAMs, system ROMs, and system memory-mapped I/O device interfaces
* - 0x3
  - 0x3000_0000
  - 0x3FFF_FFFF
  - System SRAMs, system ROMs, and system memory-mapped I/O device interfaces
* - 0x4
  - 0x4000_0000
  - 0x4FFF_FFFF
  - System SRAMs, system ROMs, and system memory-mapped I/O device interfaces
* - 0x5
  - 0x5000_0000
  - 0x5FFF_FFFF
  - System SRAMs, system ROMs, and system memory-mapped I/O device interfaces
* - 0x6
  - 0x6000_0000
  - 0x6FFF_FFFF
  - System SRAMs, system ROMs, and system memory-mapped I/O device interfaces
* - 0x7
  - 0x7000_0000
  - 0x7FFF_FFFF
  - System SRAMs, system ROMs, and system memory-mapped I/O device interfaces
* - 0x8
  - 0x8000_0000
  - 0x8FFF_FFFF
  - System SRAMs, system ROMs, and system memory-mapped I/O device interfaces
* - 0x9
  - 0x9000_0000
  - 0x9FFF_FFFF
  - System SRAMs, system ROMs, and system memory-mapped I/O device interfaces
* - 0xA
  - 0xA000_0000
  - 0xAFFF_FFFF
  - System SRAMs, system ROMs, and system memory-mapped I/O device interfaces
* - 0xB
  - 0xB000_0000
  - 0xBFFF_FFFF
  - System SRAMs, system ROMs, and system memory-mapped I/O device interfaces
* - 0xC
  - 0xC000_0000
  - 0xCFFF_FFFF
  - System SRAMs, system ROMs, and system memory-mapped I/O device interfaces
* - 0xD
  - 0xD000_0000
  - 0xDFFF_FFFF
  - System SRAMs, system ROMs, and system memory-mapped I/O device interfaces
* - 0xE
  - 0xE000_0000
  - 0xEFFF_FFFF
  - System SRAMs, system ROMs, and system memory-mapped I/O device interfaces
* - 0xF
  - 0xF000_0000
  - 0xFFFF_FFFF
  - System SRAMs, system ROMs, and system memory-mapped I/O device interfaces
:::

## Behavior of Loads to Side-Effect Addresses

Loads with potential side-effects do not stall the pipeline and may be committed before the data is returned from the system bus.
Other loads and stores in the pipeline continue to be executed unless an instruction uses data from a pending side-effect load.
Stalling the instruction control flow until a side-effect load has completed may be accomplished by either issuing a fence instruction or by generating a dependency on the load's data.

## Partial Writes

Rules for partial writes handling are:

* **Core-local addresses:** The core performs a read-modify-write operation and updates ECC to core-local memories (i.e., I- and DCCMs).
* **SoC addresses:** The core indicates the valid bytes for each bus write transaction.
  The addressed SoC memory or device performs a read-modify-write operation and updates its ECC.

## Expected SoC Behavior for Accesses

The VeeR EL2 core expects that the SoC responds to all system bus access requests it receives from the core.
System bus accesses include instruction fetches, load/store data accesses as well as debug system bus accesses.
A response may either be returning the requested data (e.g., instructions sent back to the core for fetches or data for loads), an acknowledgement indicating the successful completion of a bus transaction (e.g., acknowledging a store), an error response (e.g., an error indication in response to an attempt to access an unmapped address).
If the SoC does not respond to every single bus transaction, the core may hang.

## Speculative Bus Accesses

Deep core pipelines require a certain degree of speculation to maximize performance.
The sections below describe instruction and data speculation in the VeeR EL2 core.
Note that speculative accesses to memory addresses with side effects may be entirely avoided by adding the buildargument-selected and -configured memory protection mechanism described in [](memory-map.md#memory-protection).

### Instructions

Instruction cache misses on VeeR EL2 are speculative in nature.
The core may issue speculatively fetch accesses on the IFU bus interface for an instruction cache miss in the following cases:

* due to an earlier exception or interrupt,
* due to an earlier branch mispredict,
* due to an incorrect branch prediction, and
* due to an incorrect Return Address Stack (RAS) prediction.

Issuing speculative accesses on the IFU bus interface is benign as long as the platform is able to handle accesses to unimplemented memory and to prevent accesses to SoC components with read side effects by returning random data and/or a bus error condition.
The decision of which addresses are unimplemented and which addresses with potential side effects need to be protected is left to the platform.

Instruction fetch speculation can be limited, though not entirely avoided, by turning off the core's branch predictor including the return address stack.
Writing a '1' to the *bpd* bit in the `mfdc` register (see {numref}`tab-feature-disable-cr`) disables branch prediction including RAS.

### Data

The VeeR EL2 core does not issue any speculative data accesses on the LSU bus interface.

## DMA Slave Port

The Direct Memory Access (DMA) slave port is used for read/write accesses to core-local memories initiated by external masters.
For example, external masters could be DMA controllers or other CPU cores located in the SoC.

### Access

The DMA slave port allows read/write access to the core's ICCM and DCCM.
However, the PIC memory-mapped control registers are not accessible via the DMA port.

### Write Alignment Rules

For writes to the ICCM and DCCM through the DMA slave port, accesses must be 32- or 64-bit aligned, and 32 bits (word) or 64 bits (double-word), respectively, wide to avoid read-modify-write operations for ECC generation.

More specifically, DMA write accesses to the ICCM or DCCM must have a 32- or 64-bit access size and be aligned to their respective size.
The only write byte enable values allowed for AXI4 are 0x0F, 0xF0, and 0xFF.

### Quality Of Service

Accesses to the ICCM and DCCM by the core have higher priority if the DMA FIFO is not full.
However, to avoid starvation, the DMA slave port's DMA controller may periodically request a stall to get access to the pipe if a DMA request is continuously blocked.

The *dqc* field in the `mfdc` register (see {numref}`tab-feature-disable-cr`) specifies the maximum number of clock cycles a DMA access request waits at the head of the DMA FIFO before requesting a bubble to access the pipe.
For example, if *dqc* is 0, a DMA access requests a bubble immediately (i.e., in the same cycle); if *dqc* is 7 (the default value), a waiting DMA access requests a bubble on the 8th cycle.
For a DMA access to the ICCM, it may take up to 3 additional cycles25 before the access is granted.
Similarly, for a DMA access to the DCCM, it may take up to 4 additional cycles before the access is granted.

### Ordering Of Core and DMA Accesses

Accesses to the DCCM or ICCM by the core and the DMA slave port are asynchronous events relative to one another.
There are no ordering guarantees between the core and the DMA slave port accessing the same or different addresses.

## Reset Signal and Vector

The core provides a 31-bit wide input bus at its periphery for a reset vector.
The SoC must provide the reset vector on the `rst_vec[31:1]` bus, which could be hardwired or from a register.
The `rst_l` input signal is active-low, asynchronously asserted, and synchronously deasserted (see also [](clocks.md#reset)).
When the core is reset, it fetches the first instruction to be executed from the address provided on the reset vector bus.
Note that the applied reset vector must be pointing to the ICCM, if enabled, or a valid memory address, which is within an enabled instruction access window if the memory protection mechanism (see [](memory-map.md#memory-protection)) is used.

:::{note}
The core's 31 general-purpose registers (`x1 - x31`) are cleared on reset.
:::

## Non-Maskable Interrupt (NMI) Signal and Vector

The core provides a 31-bit wide input bus at its periphery for a non-maskable interrupt (NMI) vector.
The SoC must provide the NMI vector on the `nmi_vec[31:1]` bus, either hardwired or sourced from a register.

:::{note}
NMI is entirely separate from the other interrupts and not affected by the selection of Direct vs Vectored mode.
:::

The SoC may trigger an NMI by asserting the low-to-high edge-triggered, `asynchronous nmi_int` input signal.
This signal must be asserted for at least two full core clock cycles to guarantee it is detected by the core since shorter pulses might be dropped by the synchronizer circuit.
Furthermore, the `nmi_int` signal must be deasserted for a minimum of two full core clock cycles and then reasserted to signal the next NMI request to the core.
If the SoC does not use the pin-asserted NMI feature, it must hardwire the `nmi_int` input signal to 0.

In addition to NMIs triggered by the SoC, a core-internal NMI request is signaled when a D-bus store or non-blocking load error has been detected.

When the core receives either an SoC-triggered or a core-internal NMI request, it fetches the next instruction to be executed from the address provided on the NMI vector bus.
The reason for the NMI request is reported in the `mcause` register according to {numref}`tab-summary-nmi-mcause-values`.

:::{list-table} Summary of NMI mcause Values
:name: tab-summary-nmi-mcause-values
:header-rows: 1

* - **Value mcause[31:0]**
  - **Description**
  - **Section**
* - 0x0000_0000
  - NMI pin assertion (`nmi_int` input signal)
  - see above
* - 0xF000_0000
  - Machine D-bus store error NMI
  - [](memory-map.md#imprecise-bus-error-non-maskable-interrupt)
* - 0xF000_0001
  - Machine D-bus non-blocking load error NMI
  - [](memory-map.md#imprecise-bus-error-non-maskable-interrupt)
* - 0xF000_1000
  - Machine Fast Interrupt double-bit ECC error NMI
  - [](interrupts.md#fast-interrupt-redirect)
* - 0xF000_1001
  - Machine Fast Interrupt DCCM region access error NMI
  - [](interrupts.md#fast-interrupt-redirect)
* - 0xF000_1002
  - Machine Fast Interrupt non-DCCM region NMI
  - [](interrupts.md#fast-interrupt-redirect)
:::

:::{note}
 NMIs are typically fatal! Section 3.4 of the RISC-V Privileged specification [[2]](intro.md#ref-2) states that NMIs are only used for hardware error conditions and cause an immediate jump to the address at the NMI vector running in M-mode regardless of the state of a hart's interrupt enable bits. The NMI can thus overwrite state in an active M-mode interrupt handler and normal program execution cannot resume. Unlike resets, NMIs do not reset hart state, enabling diagnosis, reporting, and possible containment of the hardware error. Because NMIs are not maskable, the NMI handling routine performing diagnosis and reporting is itself susceptible to further NMIs, possibly making any such activity meaningless and erroneous in the face of error storms.
:::

## Software Interrupts

The VeeR EL2 core provides a software-interrupt input signal for its hart (see `soft_int` in {numref}`tab-core-complex-signals`).
The `soft_int` signal is an active-high, level-sensitive, asynchronous input signal which feeds the *msip* (machine software-interrupt pending) bit of the standard RISC-V `mip` register (see {numref}`tab-machine-interrupt-pending-register`).
When the *msie* (machine software-interrupt enable) bit of the standard RISC-V `mie` register (see {numref}`tab-machine-interrupt-enable-register`) is set, a machine software interrupt occurs if the *msip* bit of the `mip` register is asserted.

The SoC must implement Machine Software Interrupt (MSI) memory-mapped I/O registers.
These registers provide interrupt control bits which are directly connected to the respective `soft_int` pins of each core.
Writing to the corresponding bit of one of these registers enables remote harts to trigger machine-mode interprocessor interrupts.

Each hart can read its own `mhartid` register (see [](adaptations.md#machine-hardware-thread-id-register-mhartid)) to determine the memory address of the associated memory-mapped MSI register within the platform.
In this manner, an interrupt service routine can reset the corresponding memory-mapped MSI register bit before returning from a software interrupt.
