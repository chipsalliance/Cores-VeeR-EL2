# Memory Error Protection
## General Description
### Parity

Parity is a simple and relatively cheap protection scheme generally used when the corrupted data can be restored from some other location in the system.
A single parity check bit typically covers several data bits.
Two parity schemes are used: even and odd parity.
The total number of '1' bits are counted in the protected data word, including the parity bit.
For even parity, the data is deemed to be correct if the total count is an even number.

Similarly, for odd parity if the total count is an odd number. Note that double-bit errors cannot be detected.

### Error Correcting Code (ECC)

A robust memory hierarchy design often includes ECC functions to detect and, if possible, correct corrupted data.

The ECC functions described are made possible by Hamming code, a relatively simple yet powerful ECC code.
It involves storing and transmitting data with multiple check bits (parity) and decoding the associated check bits when retrieving or receiving data to detect and correct errors.

The ECC feature can be implemented with Hamming based SECDED (Single-bit Error Correction and Double-bit Error Detection) algorithm.
The design can use the (39, 32) code - 32 data bits and 7 parity bits depicted in {numref}`fig-ecc-mem-diag` below.
In other words, the Hamming code word width is 39 bits, comprised of 32 data bits and 7 check bits.
The minimum number of check bits needed for correcting a single-bit error in a 32-bit word is six.
The extra check bit expands the function to detect double-bit errors as well.

ECC codes may also be used for error detection only if other means exist to correct the data.
For example, the Icache stores exact copies of cache lines which are also residing in SoC memory.
Instead of correcting corrupted data fetched from the I-cache, erroneous cache lines may also be invalidated in the I-cache and refetched from SoC memory.
A SEDDED (Single-bit Error Detection and Double-bit Error Detection) code is sufficient in that case and provides even better protection than a SECDED code since double-bit errors are corrected as well but requires fewer bits to protect each codeword.
Note that flushing and refetching is the industry standard mechanism for recovering from I-cache errors, though commonly still referred to as 'SECDED'.

:::{figure-md} fig-ecc-mem-diag
![ECC in a Memory System](img/ecc_mem_diag.png)

Conceptual Block Diagram – ECC in a Memory System
:::

## Selecting the Proper Error Protection Level

Choosing a protection level that is too weak might lead to loss of data or silent data corrupted, choosing a level that is too strong incurs additional chip die area (i.e., cost) and power dissipation.
Supporting multiple protection schemes for the same design increases the design and verification effort.
Sources of errors can be divided into two major categories:

* Hard errors (e.g., stuck-at bits), and
* Soft errors (e.g., weak bits, cosmic-induced soft errors)
Selecting an adequate error protection level - e.g., none, parity, or ECC -- depends on the probability of an error to occur, which depends on several factors:
* Technology node
* SRAM structure size
* SRAM cell design
* Type of stored information
  * E.g., instructions in I-cache can be refetched, but data might be lost if not adequately protected
* Stored information being used again after corruption

Typically, a FIT (Failure In Time) rate analysis is done to determine the proper protection level of each memory in a system.
This analysis is based on FIT rate information for a given process and SRAM cell design which are typically available from chip manufacturer.

Also important is the SRAM array design. The SRAM layout can have an impact on if an error is correctable or not.

For example, a single cosmic-induced soft error event may destroy the content of multiple bit cells in an array.
If the destroyed bits are covered by the same codeword, the data cannot be corrected or possibly even detected.

Therefore, the bits of each codeword should be physically spread in the array as far apart as feasibly possible. In a properly laid out SRAM array, multiple corrupted bits may result in several single-bit errors of different codewords which are correctable.

## Memory Hierarchy

{numref}`tab-memory-hierarchy-components-and-protection` summarizes the components of the VeeR EL2 memory hierarchy and their respective protection scheme.

:::{list-table} Memory Hierarchy Components and Protection
:name: tab-memory-hierarchy-components-and-protection
* - **Memory Type**
  - **Abbreviation**
  - **Protection**
  - **Reason/Justification**
* - Instruction Cache
  - I-cache
  - Parity or  SEDDED  ECC (data  and tag) [^fn-error-protection-1]
  - Instructions can be refetched if error is detected
* - Instruction Closely-Coupled Memory
  - ICCM
  - SECDED ECC
  -
    - Large SRAM arrays
    - Data could be modified and is only valid copy
* - Data Closely-Coupled Memory
  - DCCM
  - SECDED ECC
  -
    - Large SRAM arrays
    - Data could be modified and is only valid copy
* - Core-complex-external Memories
  - SoC memories
  - SECDED ECC
  -
    - Large SRAM arrays
    - Data could be modified and is only valid copy
:::

[^fn-error-protection-1]: Some highly reliable/available applications (e.g., automotive) might want to use an ECC-protected I-cache, instead of parity
protection. Therefore, SEDDED ECC protection is optionally provided in VeeR EL2 as well, selectable as a core build argument.
Note that the I-cache area increases significantly if ECC protection is used.

## Error Detection and Handling

{numref}`tab-error-detection-recovery-logging` summarizes the detection of errors, the recovery steps taken, and the logging of error events for each of the VeeR EL2 memories.

:::{note}
 Memories with parity or ECC protection must be initialized with correct parity or ECC. Otherwise, a read access to an uninitialized memory may report an error. The method of initialization depends on the organization and capabilities of the memory. Initialization might be performed by a memory self-test or depend on firmware to overwrite the entire memory range (e.g., via DMA accesses).
:::

:::{note}
 If the DCCM is uninitialized, a load following a store to the same DCCM address may get incorrect data. If firmware initializes the DCCM, aligned word-sized stores should be used (because they don't check ECC), followed by a fence, before any load instructions to DCCM addresses are executed.
:::

Empty fields shall be ignored as they provide structure information for the table

:::{list-table} Error Detection, Recovery, and Logging
:name: tab-error-detection-recovery-logging

* - **Memory Type**
  - **Detection**
  - **Recovery**
  - **Recovery**
  - **Logging**
  - **Logging**
* -
  -
  - **Single-bit Error**
  - **Double-bit Error**
  - **Single-bit Error**
  - **Double-bit Error**
* - I-cache
  -
    - Each 64-bit chunk of instructions protected with 4 parity bits (one per 16 consecutive bits) or 7 ECC bits
    - Each cache line tag protected with 1 parity bit or 5 ECC bits
    - Parity/ECC bits checked in pipeline
  -
  -
  -
  -
* -
  -
  - **For parity**
  -
  -
  -
* -
  -
  -
    - For instruction and tag parity errors, invalidate all cache lines of set
    - Refetch cache line from SoC memory
  - Undetected
  -
    - Increment I- cache correctable error counter [^fn-error-protection-2]
    - If error counter has reached threshold, signal correctable error local interrupt (see [](error-protection.md#i-cache-error-counter-threshold-register-micect))
  - No action
* -
  -
  - **For ECC**
  -
  -
  -
* -
  -
  -
    - For instruction and tag single- and double ECC errors, invalidate all cache lines of set
    - Refetch cache line from SoC memory [^fn-error-protection-3]
  -
    - For instruction and tag single- and double ECC errors, invalidate all cache lines of set
    - Refetch cache line from SoC memory [^fn-error-protection-3]
  -
    - Increment I-cache correctable error counter [^fn-error-protection-2]
    - If error counter has reached threshold, signal correctable error local interrupt (see [](error-protection.md#i-cache-error-counter-threshold-register-micect))
  -
    - Increment I-cache correctable error counter [^fn-error-protection-2]
    - If error counter has reached threshold, signal correctable error local interrupt (see [](error-protection.md#i-cache-error-counter-threshold-register-micect))
* - ICCM
  -
    - Each 32-bit chunk protected with 7 ECC bits
    - ECC checked in pipeline
  -
    - For fetches [^fn-error-protection-4]:
      - Write corrected data/ECC back to ICCM
      - Refetch instruction from ICCM [^fn-error-protection-3]
    - For DMA reads:
      - Correct error in-line
      - Write corrected data/ECC back to ICCM
  - Fatal error [^fn-error-protection-5] (uncorrectable)
  -
    - Increment [^fn-error-protection-4] ICCM single- bit error counter
    - If error counter has reached threshold, signal correctable error local interrupt (see [](error-protection.md#iccm-correctable-error-counter-threshold-register-miccmect))
  -
    - For fetches [^fn-error-protection-5]:
      - Instruction access fault exception
    - For DMA reads:
      - Send error response on DMA slave bus to master
* - DCCM
  -
    - Each 32-bit chunk protected with 7 ECC bits
    - ECC checked in pipeline
  -
    - Correct error in-line
    - Write [^fn-error-protection-6] corrected data/ECC back to DCCM
  - Fatal error [^fn-error-protection-7] (uncorrectable)
  -
    - Increment [^fn-error-protection-6] DCCM single- bit error counter
    - If error counter has reached threshold, signal correctable error local interrupt (see [](error-protection.md#dccm-correctable-error-counter-threshold-register-mdccmect))
  -
    - For loads [^fn-error-protection-7]:
      - Load access fault exception
    - For stores [^fn-error-protection-7]:
      - Store/AMO access fault exception
    - For DMA reads:
      - Send error response on DMA slave bus to master
* - SoC memories
  - ECC checked at SoC memory boundary
  -
    - Correct error
    - Send corrected data on bus
    - Write corrected data/ECC back to SRAM array
  -
    - Fatal error (uncorrectable)
    - Data sent on bus with error indication
    - Core must ignore sent data
  -
    - Increment SoC single-bit error counter local to memory
    - If error counter has reached threshold, signal external interrupt
  -
    - For fetches:
      - Instruction access fault exception
    - For loads:
      - Non-blocking load bus error NMI (see [](memory-map.md#imprecise-bus-error-non-maskable-interrupt))
    - For stores:
      - Store bus error NMI (see [](memory-map.md#imprecise-bus-error-non-maskable-interrupt))
:::

General comments:

* No address information of each individual correctable error is captured.
* Stuck-at faults:
  * Stuck-at bits would cause the correctable error threshold to be reached relatively quickly but are only reported if interrupts are enabled.
  * Use MBIST to determine exact location of the bad bit.
  * Because ICCM single-bit errors on fetches are not in-line corrected, VeeR EL2's ICCM implements two row's worth of redundant memory which is transparently managed in hardware.
    These extra rows help to avoid that a stuck-at bit may hang the core.

[^fn-error-protection-2]: It is unlikely, but possible that multiple I-cache parity/ECC errors are detected on a cache line in a single cycle, however, the Icache single-bit error counter is incremented only by one.
[^fn-error-protection-3]: A RFPC (ReFetch PC) flush is performed since in-line correction would create timing issues and require an additional clock cycle as well as a different architecture.
[^fn-error-protection-4]: All single-bit errors detected on fetches are corrected, written back to the ICCM, and counted, independent of actual instruction execution.
[^fn-error-protection-5]: For oldest instruction in pipeline only.
[^fn-error-protection-6]: For load/store accesses, the corrected data is written back to the DCCM and counted only if the load/store instruction retires (i.e., access is non-speculative and has no exception).
[^fn-error-protection-7]: For non-speculative accesses only.

## Core Error Counter/Threshold Registers

A summary of platform-specific core error counter/threshold control/status registers in CSR space:

* [](error-protection.md#i-cache-error-counterthreshold-register-micect)
* [](error-protection.md#iccm-correctable-error-counterthreshold-register-miccmect)
* [](error-protection.md#dccm-correctable-error-counterthreshold-register-mdccmect)

All read/write control/status registers must have WARL (Write Any value, Read Legal value) behavior.

### I-Cache Error Counter/Threshold Register (micect)

The `micect` register holds the I-cache error counter and its threshold.
The *count* field of the `micect` register is incremented, if a parity/ECC error is detected on any of the cache line tags of the set or the instructions fetched from the I-cache.
The *thresh* field of the `micect` register holds a pointer to a bit position of the *count* field.
If the selected bit of the *count* field transitions from '0' to '1', the threshold is reached, and a correctable error local interrupt (see [](memory-map.md#correctable-error-local-interrupt)) is signaled.

Hardware increments the *count* field on a detected error.
Firmware can non-destructively read the current *count* and *thresh* values or write to both these fields (e.g., to change the threshold and reset the counter).

:::{note}
The counter may overflow if not serviced and reset by firmware.
:::

:::{note}
The correctable error local interrupt is not latched (i.e., "sticky"), but it stays pending until the counter overflows (i.e., as long as the *count* value is equal to or greater than the threshold value (= {math}`2^{thresh}`)). When firmware resets the counter, the correctable error local interrupt condition is cleared.
:::

:::{note}
The `micect` register is instantiated, accessible, and has the same functional behavior even if the core is built without an I-cache.
:::

This register is mapped to the non-standard read/write CSR address space.

:::{list-table} I-Cache Error Counter/Threshold Register (micect, at CSR 0x7F0)
:name: tab-i-cache-error-counter-threshold-register

* - **Field**
  - **Bits**
  - **Description**
  - **Access**
  - **Reset**
* - thresh
  - 31:27
  - I-cache parity/ECC error threshold:
    - 0..26: Value i selects *count[i]* bit
    - 27..31: Invalid (when written, mapped by hardware to 26)
  - R/W
  - 0
* - count
  - 26:0
  - Counter incremented if I-cache parity/ECC error(s) detected. If *count[thresh]* transitions from '0' to '1', signal correctable error local  interrupt (see [](memory-map.md#correctable-error-local-interrupt)).
  - R/W
  - 0
:::

### ICCM Correctable Error Counter/Threshold Register (miccmect)

The `miccmect` register holds the ICCM correctable error counter and its threshold.
The *count* field of the `miccmect` register is incremented, if a correctable ECC error is detected on either an instruction fetch or a DMA read from the ICCM.
The *thresh* field of the `miccmect` register holds a pointer to a bit position of the *count* field.
If the selected bit of the *count* field transitions from '0' to '1', the threshold is reached, and a correctable error local interrupt (see [](memory-map.md#correctable-error-local-interrupt)) is signaled.

Hardware increments the *count* field on a detected single-bit error.
Firmware can non-destructively read the current count and *thresh* values or write to both these fields (e.g., to change the threshold and reset the counter).

:::{note}
The counter may overflow if not serviced and reset by firmware.
:::

:::{note}
The correctable error local interrupt is not latched (i.e., "sticky"), but it stays pending until the counter overflows (i.e., as long as the *count* value is equal to or greater than the threshold value (= {math}`2^{thresh}`)). When firmware resets the counter, the correctable error local interrupt condition is cleared.
:::

:::{note}
DMA accesses while in power management Sleep (pmu/fw-halt) or debug halt (db-halt) state may encounter ICCM single-bit errors. Correctable errors are counted in the `miccmect` error counter irrespective of the core's power state.
:::

:::{note}
In the unlikely case of a persistent single-bit error in the ICCM on a location needed for execution of the beginning of the ICCM correctable error local interrupt handler and the counter threshold is set to lower than 16 errors, forward progress may not be guaranteed.
:::

:::{note}
The `miccmect` register is instantiated, accessible, and has the same functional behavior even if the core is built without an ICCM.
:::

This register is mapped to the non-standard read/write CSR address space.

:::{list-table} ICCM Correctable Error Counter/Threshold Register (miccmect, at CSR 0x7F1)
:name: tab-iccm-correctable-error-counter-threshold-register

* - **Field**
  - **Bits**
  - **Description**
  - **Access**
  - **Reset**
* - thresh
  - 31:27
  - ICCM correctable ECC error threshold:
    - 0..26: Value i selects *count[i]* bit
    - 27..31: Invalid (when written, mapped by hardware to 26)
  - R/W
  - 0
* - count
  - 26:0
  - Counter incremented for each detected ICCM correctable ECC error.  If *count[thresh]* transitions from '0' to '1', signal correctable error local  interrupt (see [](memory-map.md#correctable-error-local-interrupt)).
  - R/W
  - 0
:::

### DCCM Correctable Error Counter/Threshold Register (mdccmect)

The `mdccmect` register holds the DCCM correctable error counter and its threshold.
The *count* field of the `mdccmect` register is incremented, if a correctable ECC error is detected on either a retired load/store instruction or a DMA read access to the DCCM.
The *thresh* field of the `mdccmect` register holds a pointer to a bit position of the *count* field.
If the selected bit of the *count* field transitions from '0' to '1', the threshold is reached, and a correctable error local interrupt (see [](memory-map.md#correctable-error-local-interrupt)) is signaled.

Hardware increments the *count* field on a detected single-bit error for a retired load or store instruction (i.e., a nonspeculative access with no exception) or a DMA read.
Firmware can non-destructively read the current *count* and *thresh* values or write to both these fields (e.g., to change the threshold and reset the counter).

:::{note}
The counter may overflow if not serviced and reset by firmware.
:::

:::{note}
The correctable error local interrupt is not latched (i.e., "sticky"), but it stays pending until the counter overflows (i.e., as long as the *count* value is equal to or greater than the threshold value (= {math}`2^{thresh}`)).
When firmware resets the counter, the correctable error local interrupt condition is cleared.
:::

:::{note}
DMA accesses while in power management Sleep (pmu/fw-halt) or debug halt (db-halt) state may encounter DCCM single-bit errors.
Correctable errors are counted in the `mdccmect` error counter irrespective of the core's power state.
:::

:::{note}
The `mdccmect` register is instantiated, accessible, and has the same functional behavior even if the core is built without a DCCM.
:::

This register is mapped to the non-standard read/write CSR address space.

:::{list-table} DCCM Correctable Error Counter/Threshold Register (mdccmect, at CSR 0x7F2)
:name: tab-mdccmect

* - **Field**
  - **Bits**
  - **Description**
  - **Access**
  - **Reset**
* - thresh
  - 31:27
  - DCCM correctable ECC error threshold:
    - 0..26: Value i selects *count[i]* bit
    - 27..31: Invalid (when written, mapped by hardware to 26)
  - R/W
  - 0
* - count
  - 26:0
  - Counter incremented for each detected DCCM correctable ECC error.  If *count[thresh]* transitions from '0' to '1', signal correctable error local interrupt (see [](memory-map.md#correctable-error-local-interrupt)).
  - R/W
  - 0
:::
