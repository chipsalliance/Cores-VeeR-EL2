# 3 Memory Error Protection
## 3.1 General Description
### 3.1.1 Parity

Parity is a simple and relatively cheap protection scheme generally used when the corrupted data can be restored from some other location in the system.
A single parity check bit typically covers several data bits.
Two parity schemes are used: even and odd parity.
The total number of '1' bits are counted in the protected data word, including the parity bit.
For even parity, the data is deemed to be correct if the total count is an even number.

Similarly, for odd parity if the total count is an odd number. Note that double-bit errors cannot be detected.

### 3.1.2 Error Correcting Code (ECC)

A robust memory hierarchy design often includes ECC functions to detect and, if possible, correct corrupted data.

The ECC functions described are made possible by Hamming code, a relatively simple yet powerful ECC code.
It involves storing and transmitting data with multiple check bits (parity) and decoding the associated check bits when retrieving or receiving data to detect and correct errors.

The ECC feature can be implemented with Hamming based SECDED (Single-bit Error Correction and Double-bit Error Detection) algorithm.
The design can use the (39, 32) code - 32 data bits and 7 parity bits depicted in Figure 6-1 below.
In other words, the Hamming code word width is 39 bits, comprised of 32 data bits and 7 check bits.
The minimum number of check bits needed for correcting a single-bit error in a 32-bit word is six.
The extra check bit expands the function to detect double-bit errors as well.

ECC codes may also be used for error detection only if other means exist to correct the data.
For example, the Icache stores exact copies of cache lines which are also residing in SoC memory.
Instead of correcting corrupted data fetched from the I-cache, erroneous cache lines may also be invalidated in the I-cache and refetched from SoC memory.
A SEDDED (Single-bit Error Detection and Double-bit Error Detection) code is sufficient in that case and provides even better protection than a SECDED code since double-bit errors are corrected as well but requires fewer bits to protect each codeword.
Note that flushing and refetching is the industry standard mechanism for recovering from I-cache errors, though commonly still referred to as 'SECDED'.

:::{figure-md}
![ECC in a Memory System](img/ecc_mem_diag.png)

Figure 3-1 Conceptual Block Diagram – ECC in a Memory System
:::


## 3.2 Selecting the Proper Error Protection Level

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
  * E.g., instructions in I-cache can be refetched, but
  * data might be lost if not adequately protected
* Stored information being used again after corruption

Typically, a FIT (Failure In Time) rate analysis is done to determine the proper protection level of each memory in a system.
This analysis is based on FIT rate information for a given process and SRAM cell design which are typically available from chip manufacturer.

Also important is the SRAM array design. The SRAM layout can have an impact on if an error is correctable or not.

For example, a single cosmic-induced soft error event may destroy the content of multiple bit cells in an array.
If the destroyed bits are covered by the same codeword, the data cannot be corrected or possibly even detected.

Therefore, the bits of each codeword should be physically spread in the array as far apart as feasibly possible. In a properly laid out SRAM array, multiple corrupted bits may result in several single-bit errors of different codewords which are correctable.

## 3.3 Memory Hierarchy

Table 3-1 summarizes the components of the VeeR EL2 memory hierarchy and their respective protection scheme.

:::{table} Table 3-1 Memory Hierarchy Components and Protection<br>Empty fields note a duplication of the field above

| Memory Type                        | Abbreviation   | Protection                               | Reason/Justification                                  |
|------------------------------------|----------------|------------------------------------------|-------------------------------------------------------|
| Instruction Cache                  | I-cache        | Parity or  SEDDED  ECC (data  and tag)  26 | - Instructions can be refetched if  error is detected |
| Instruction Closely-Coupled Memory | ICCM           | SECDED ECC                                                     | Large SRAM arrays; Data could be modified and is only  valid copy      |
| Data Closely-Coupled Memory        | DCCM           | ||
| Core-complex-external Memories     | SoC memories   |                                          |                                                       |

:::
26: Some highly reliable/available applications (e.g., automotive) might want to use an ECC-protected I-cache, instead of parity
protection. Therefore, SEDDED ECC protection is optionally provided in VeeR EL2 as well, selectable as a core build argument.
Note that the I-cache area increases significantly if ECC protection is used.

## 3.4 Error Detection and Handling

Table 3-2 summarizes the detection of errors, the recovery steps taken, and the logging of error events for each of the VeeR EL2 memories.

:::{note}
 Memories with parity or ECC protection must be initialized with correct parity or ECC. Otherwise, a read access to an uninitialized memory may report an error. The method of initialization depends on the organization and capabilities of the memory. Initialization might be performed by a memory self-test or depend on firmware to overwrite the entire memory range (e.g., via DMA accesses).
:::

:::{note}
 If the DCCM is uninitialized, a load following a store to the same DCCM address may get incorrect data. If firmware initializes the DCCM, aligned word-sized stores should be used (because they don't check ECC), followed by a fence, before any load instructions to DCCM addresses are executed.
:::

:::{table} Table 3-2 Error Detection, Recovery, and Logging<br>Empty fields shall be ignored as they provide structure information for the table

|Memory Type|Detection|Recovery/Single-bit Error|Recovery/Double-bit Error|Logging/Single-bit Error|Logging/Double-bit Error|
|---|---|---|---|---|---|
|||For Parity:||||
|I-cache|• Each 64-bit chunk of instructions protected with 4 parity bits (one per 16 consecutive bits) or 7 ECC bits<br> • Each cache line tag protected with 1 parity bit or 5 ECC bits<br> • Parity/ECC bits checked in pipeline|• For instruction and tag parity errors, invalidate all cache lines of set<br> • Refetch cache line from SoC memory|Undetected|• Increment I- cache correctable error counter27<br> • If error counter has reached threshold, signal correctable error local interrupt (see Section 3.5.1)|No action|
|||For ECC:||||
|I-cache|• Each 64-bit chunk of instructions protected with 4 parity bits (one per 16 consecutive bits) or 7 ECC bits<br> • Each cache line tag protected with 1 parity bit or 5 ECC bits<br> • Parity/ECC bits checked in pipeline|• For instruction and tag single- and double ECC errors, invalidate all cache lines of set<br> • Refetch cache line from SoC memory28|• For instruction and tag single- and double ECC errors, invalidate all cache lines of set<br> • Refetch cache line from SoC memory28|• Increment I-cache correctable error counter27<br> • If error counter has reached threshold, signal correctable error local interrupt (see Section 3.5.1)|• Increment I-cache correctable error counter27<br> • If error counter has reached threshold, signal correctable error local interrupt (see Section 3.5.1)|
||||
|ICCM|• Each 32-bit chunk protected with 7 ECC bits<br> • ECC checked in pipeline|For fetches 29:<br> • Write corrected data/ECC back to ICCM<br> • Refetch instruction from ICCM28|Fatal error 30 (uncorrectable)|• Increment29 ICCM single- bit error counter<br> • If error counter has reached threshold, signal correctable error local interrupt (see Section 3.5.2)|For fetches 30: Instruction access fault exception|
|ICCM|• Each 32-bit chunk protected with 7 ECC bits<br> • ECC checked in pipeline|For DMA reads:<br> • Correct error in-line<br> • Write corrected data/ECC back to ICCM|Fatal error 30 (uncorrectable)|• Increment29 ICCM single- bit error counter<br> • If error counter has reached threshold, signal correctable error local interrupt (see Section 3.5.2)|For DMA reads: Send error response on DMA slave bus to master|
|DCCM|• Each 32-bit chunk protected with 7 ECC bits<br> • ECC checked in pipeline|• Correct error in-line<br> • Write31 corrected data/ECC back to DCCM|Fatal error32 (uncorrectable)|• Increment31 DCCM single- bit error counter<br> • If error counter has reached threshold, signal correctable error local interrupt (see Section 3.5.3)|For loads32: Load access fault exception|
|DCCM|• Each 32-bit chunk protected with 7 ECC bits<br> • ECC checked in pipeline|• Correct error in-line<br> • Write31 corrected data/ECC back to DCCM|Fatal error32 (uncorrectable)|• Increment31 DCCM single- bit error counter<br> • If error counter has reached threshold, signal correctable error local interrupt (see Section 3.5.3)|For stores32: Store/AMO access fault exception|
|DCCM|• Each 32-bit chunk protected with 7 ECC bits<br> • ECC checked in pipeline|• Correct error in-line<br> • Write31 corrected data/ECC back to DCCM|Fatal error32 (uncorrectable)|• Increment31 DCCM single- bit error counter<br> • If error counter has reached threshold, signal correctable error local interrupt (see Section 3.5.3)|For DMA reads: Send error response on DMA slave bus to master|
|SoC memories|ECC checked at SoC memory boundary|• Correct error<br> • Send corrected data on bus<br> • Write corrected data/ECC back to SRAM array|• Fatal error (uncorrectable)<br> • Data sent on bus with error indication<br> • Core must ignore sent data|• Increment SoC single-bit error counter local to memory<br> • If error counter has reached threshold, signal external interrupt|For fetches: Instruction access fault exception|
|SoC memories|ECC checked at SoC memory boundary|• Correct error<br> • Send corrected data on bus<br> • Write corrected data/ECC back to SRAM array|• Fatal error (uncorrectable)<br> • Data sent on bus with error indication<br> • Core must ignore sent data|• Increment SoC single-bit error counter local to memory<br> • If error counter has reached threshold, signal external interrupt|For loads: Non-blocking load bus error NMI (see Section 2.7.1)|
|SoC memories|ECC checked at SoC memory boundary|• Correct error<br> • Send corrected data on bus<br> • Write corrected data/ECC back to SRAM array|• Fatal error (uncorrectable)<br> • Data sent on bus with error indication<br> • Core must ignore sent data|• Increment SoC single-bit error counter local to memory<br> • If error counter has reached threshold, signal external interrupt|For stores: Store bus error NMI (see Section 2.7.1)|

:::
General comments:

* No address information of each individual correctable error is captured.
* Stuck-at faults:
  * Stuck-at bits would cause the correctable error threshold to be reached relatively quickly but are only reported if interrupts are enabled.
  * Use MBIST to determine exact location of the bad bit.
  * Because ICCM single-bit errors on fetches are not in-line corrected, VeeR EL2's ICCM implements two row's worth of redundant memory which is transparently managed in hardware.
    These extra rows help to avoid that a stuck-at bit may hang the core.

27 It is unlikely, but possible that multiple I-cache parity/ECC errors are detected on a cache line in a single cycle, however, the Icache single-bit error counter is incremented only by one.

28 A RFPC (ReFetch PC) flush is performed since in-line correction would create timing issues and require an additional clock cycle as well as a different architecture.

29 All single-bit errors detected on fetches are corrected, written back to the ICCM, and counted, independent of actual instruction execution.

30 For oldest instruction in pipeline only.

31 For load/store accesses, the corrected data is written back to the DCCM and counted only if the load/store instruction retires (i.e., access is non-speculative and has no exception).

32 For non-speculative accesses only.

## 3.5 Core Error Counter/Threshold Registers

A summary of platform-specific core error counter/threshold control/status registers in CSR space:

- I-Cache Error Counter/Threshold Register (micect) (see Section 3.5.1)
- ICCM Correctable Error Counter/Threshold Register (miccmect) (see Section 3.5.2)
- DCCM Correctable Error Counter/Threshold Register (mdccmect) (see Section 3.5.3)

All read/write control/status registers must have WARL (Write Any value, Read Legal value) behavior.

### 3.5.1 I-Cache Error Counter/Threshold Register (micect)

The micect register holds the I-cache error counter and its threshold.
The *count* field of the micect register is incremented, if a parity/ECC error is detected on any of the cache line tags of the set or the instructions fetched from the I-cache.
The *thresh* field of the micect register holds a pointer to a bit position of the *count* field.
If the selected bit of the *count* field transitions from '0' to '1', the threshold is reached, and a correctable error local interrupt (see Section 2.7.2) is signaled.

Hardware increments the *count* field on a detected error.
Firmware can non-destructively read the current *count* and thresh values or write to both these fields (e.g., to change the threshold and reset the counter).

:::{note}
The counter may overflow if not serviced and reset by firmware.
:::

:::{note}
The correctable error local interrupt is not latched (i.e., "sticky"), but it stays pending until the counter overflows (i.e., as long as the *count* value is equal to or greater than the threshold value (= 2*thresh*)). When firmware resets the counter, the correctable error local interrupt condition is cleared.
:::

:::{note}
The micect register is instantiated, accessible, and has the same functional behavior even if the core is built without an I-cache.
:::

This register is mapped to the non-standard read/write CSR address space.

:::{table} Table 3-3 I-Cache Error Counter/Threshold Register (micect, at CSR 0x7F0)

| Field   | Bits   | Description                                                                                                                                                                | Access   | Reset   |
|---------|--------|----------------------------------------------------------------------------------------------------------------------------------------------------------------------------|----------|---------|
| thresh  | 31:27  | I-cache parity/ECC error threshold:  0..26: Value i selects count[i] bit  27..31: Invalid (when written, mapped by hardware to 26)                                         | R/W      | 0       |
| count   | 26:0   | Counter incremented if I-cache parity/ECC error(s) detected.  If count[thresh] transitions from '0' to '1', signal correctable error local  interrupt (see Section 2.7.2). | R/W      | 0       |

:::
### 3.5.2 Iccm Correctable Error Counter/Threshold Register (miccmect)

The miccmect register holds the ICCM correctable error counter and its threshold.
The *count* field of the miccmect register is incremented, if a correctable ECC error is detected on either an instruction fetch or a DMA read from the ICCM.
The *thresh* field of the miccmect register holds a pointer to a bit position of the *count* field.
If the selected bit of the *count* field transitions from '0' to '1', the threshold is reached, and a correctable error local interrupt (see Section 2.7.2) is signaled.

Hardware increments the *count* field on a detected single-bit error.
Firmware can non-destructively read the current count and *thresh* values or write to both these fields (e.g., to change the threshold and reset the counter).

:::{note}
The counter may overflow if not serviced and reset by firmware.
:::

:::{note}
The correctable error local interrupt is not latched (i.e., "sticky"), but it stays pending until the counter overflows (i.e., as long as the *count* value is equal to or greater than the threshold value (= 2*thresh*)). When firmware resets the counter, the correctable error local interrupt condition is cleared.
:::


:::{note}
DMA accesses while in power management Sleep (pmu/fw-halt) or debug halt (db-halt) state may encounter ICCM single-bit errors. Correctable errors are counted in the miccmect error counter irrespective of the core's power state.
:::

:::{note}
In the unlikely case of a persistent single-bit error in the ICCM on a location needed for execution of the beginning of the ICCM correctable error local interrupt handler and the counter threshold is set to lower than 16 errors, forward progress may not be guaranteed. Note: The miccmect register is instantiated, accessible, and has the same functional behavior even if the core is built without an ICCM.
:::

This register is mapped to the non-standard read/write CSR address space.

:::{table} Table 3-4 ICCM Correctable Error Counter/Threshold Register (miccmect, at CSR 0x7F1)

| Field   | Bits   | Description                                                                                                                                                                     | Access   | Reset   |
|---------|--------|---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|----------|---------|
| thresh  | 31:27  | ICCM correctable ECC error threshold:  0..26: Value i selects count[i] bit  27..31: Invalid (when written, mapped by hardware to 26)                                            | R/W      | 0       |
| count   | 26:0   | Counter incremented for each detected ICCM correctable ECC error.  If count[thresh] transitions from '0' to '1', signal correctable error local  interrupt (see Section 2.7.2). | R/W      | 0       |

:::

### 3.5.3 Dccm Correctable Error Counter/Threshold Register (mdccmect)

The mdccmect register holds the DCCM correctable error counter and its threshold.
The *count* field of the mdccmect register is incremented, if a correctable ECC error is detected on either a retired load/store instruction or a DMA read access to the DCCM.
The *thresh* field of the mdccmect register holds a pointer to a bit position of the count field.
If the selected bit of the *count* field transitions from '0' to '1', the threshold is reached, and a correctable error local interrupt (see Section 2.7.2) is signaled.

Hardware increments the *count* field on a detected single-bit error for a retired load or store instruction (i.e., a nonspeculative access with no exception) or a DMA read.
Firmware can non-destructively read the current *count* and thresh values or write to both these fields (e.g., to change the threshold and reset the counter).

:::{note}
The counter may overflow if not serviced and reset by firmware.
:::

:::{note}
The correctable error local interrupt is not latched (i.e., "sticky"), but it stays pending until the counter overflows (i.e., as long as the *count* value is equal to or greater than the threshold value (= 2*thresh*)).
When firmware resets the counter, the correctable error local interrupt condition is cleared.
:::

:::{note}
DMA accesses while in power management Sleep (pmu/fw-halt) or debug halt (db-halt) state may encounter DCCM single-bit errors.
Correctable errors are counted in the mdccmect error counter irrespective of the core's power state.
:::

:::{note}
The mdccmect register is instantiated, accessible, and has the same functional behavior even if the core is built without a DCCM.
:::

This register is mapped to the non-standard read/write CSR address space.

:::{table} Table 3-5 DCCM Correctable Error Counter/Threshold Register (mdccmect, at CSR 0x7F2)

| Field   | Bits   | Description                                                                                                                                                                     | Access   | Reset   |
|---------|--------|---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|----------|---------|
| thresh  | 31:27  | DCCM correctable ECC error threshold:  0..26: Value i selects count[i] bit  27..31: Invalid (when written, mapped by hardware to 26)                                            | R/W      | 0       |
| count   | 26:0   | Counter incremented for each detected DCCM correctable ECC error.  If count[thresh] transitions from '0' to '1', signal correctable error local  interrupt (see Section 2.7.2). | R/W      | 0       |

:::

