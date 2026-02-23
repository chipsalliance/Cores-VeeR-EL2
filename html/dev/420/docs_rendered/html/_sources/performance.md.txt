# Performance Monitoring

This chapter describes the performance monitoring features of the VeeR EL2 core.

## Features

VeeR EL2 provides these performance monitoring features:

* Four standard 64-bit wide event counters
* Standard separate event selection for each counter
* Standard selective count enable/disable controllability
* Standard synchronized counter enable/disable controllability
* Standard cycle counter
* Standard retired instructions counter
* Support for standard SoC-based machine timer registers

## Control/Status Registers

### Standard RISC-V Registers

A list of performance monitoring-related standard RISC-V CSRs with references to their definitions:

* Machine Hardware Performance Monitor (`mcycle{|h}`, `minstret{|h}`, `mhpmcounter3{|h}`- `mhpmcounter31{|h}`, and `mhpmevent3`-`mhpmevent31`) (see Section 3.1.11 in [[2]](intro.md#ref-2))
* Machine Counter-Inhibit Register [^fn-performance-1] (`mcountinhibit`) (see Section 3.1.13 in [[2]](intro.md#ref-2))
* Machine Timer Registers (`mtime` and `mtimecmp`) (see Section 3.1.10 in [[2]](intro.md#ref-2))

:::{note}
`mtime` and `mtimecmp` are memory-mapped registers which must be provided by the SoC.
:::

[^fn-performance-1]: The standard `mcountinhibit` register which was recently added to [[2]](intro.md#ref-2) replaces the non-standard mgpmc register of the previous VeeR generation. The `mcountinhibit` register provides the same functionality as the `mgpmc` register did, but at a much finer granularity (i.e., an enable/disable control bit per standard hardware performance counter instead of a single control bit for the `mhpmcounter3` - `mhpmcounter6` counters).

## Counters

Only event counters 3 to 6 (`mhpmcounter3{|h}`-`mhpmcounter6{|h}`) and their corresponding event selectors (`mhpmevent3`-`mhpmevent6`) are functional on VeeR EL2.

Event counters 7 to 31 (`mhpmcounter7{|h}`-`mhpmcounter31{|h}`) and their corresponding event selectors (`mhpmevent7`-`mhpmevent31`) are hardwired to '0'.

## Count-Impacting Conditions

A few comments to consider on conditions that have an impact on the performance monitor counting:
* While in the pmu/fw-halt power management state, performance counters (including the `mcycle` counter) are disabled.
* While in debug halt (db-halt) state, the *stopcount* bit of the `dcsr` register (see [](debugging.md#debug-control-and-status-register-dcsr)) determines if performance counters are enabled.
* While in the pmu/fw-halt power management state or the debug halt (db-halt) state with the stopcount bit set, DMA accesses are allowed, but not counted by the performance counters. It would be up to the bus master to count accesses while the core is in a halt state.
* While executing PAUSE, performance counters are enabled.

Also, it is recommended that the performance counters are disabled (using the `mcountinhibit` register) before the counters and event selectors are modified, and then reenabled again.
This minimizes the impact of reading and writing the counter and event selector CSRs on the event count values, specifically for the CSR read/write events (i.e., events #16 and #17).
In general, performance counters are incremented after a read access to the counter CSRs, but before a write access to the counter CSRs.

## Events

{numref}`tab-list-of-countable-events` provides a list of the countable events.

:::{note}
The event selector registers `mhpmevent3`-`mhpmevent6` have WARL behavior. When writing either a value marked as 'Reserved' or larger than the highest supported event number, the event selector is set to '0' (i.e., no event counted).
:::

:::{list-table} List of Countable Events
:name: tab-list-of-countable-events

* - **Event No**
  - **Event Name**
  - **Description**
* - 0
  -
  - Reserved (no event counted)
* - **Events counted while in Active (C0) state**
  -
  -
* - Legend: IP = In-Pipe; OOP = Out-Of-Pipe
  -
  -
* - 1
  - cycles clocks active
  - Number of cycles clock active (OOP)
* - 2
  - I-cache hits
  - Number of I-cache hits (OOP, speculative, valid fetch &amp; hit)
* - 3
  - I-cache misses
  - Number of I-cache misses (OOP, valid fetch &amp; miss)
* - 4
  - instr committed - all
  - Number of all (16b+32b) instructions committed (IP, non-speculative, 0/1)
* - 5
  - instr committed - 16b
  - Number of 16b instructions committed (IP, non-speculative, 0/1)
* - 6
  - instr committed - 32b
  - Number of 32b instructions committed (IP, non-speculative, 0/1)
* - 7
  - instr aligned - all
  - Number of all (16b+32b) instructions aligned (OOP, speculative, 0/1)
* - 8
  - instr decoded - all
  - Number of all (16b+32b) instructions decoded (OOP, speculative, 0/1)
* - 9
  - muls committed
  - Number of multiplications committed (IP, 0/1)
* - 10
  - divs committed
  - Number of divisions and remainders committed (IP, 0/1)
* - 11
  - loads committed
  - Number of loads committed (IP, 0/1)
* - 12
  - stores committed
  - Number of stores committed (IP, 0/1)
* - 13
  - misaligned loads
  - Number of misaligned loads (IP, 0/1)
* - 14
  - misaligned stores
  - Number of misaligned stores (IP, 0/1)
* - 15
  - alus committed
  - Number of ALU [^fn-performance-2] operations committed (IP, 0/1)
* - 16
  - CSR read
  - Number of CSR read instructions committed (IP, 0/1)
* - 17
  - CSR read/write
  - Number of CSR read/write instructions committed (IP, 0/1)
* - 18
  - CSR write rd==0
  - Number of CSR write rd==0 instructions committed (IP, 0/1)
* - 19
  - `ebreak`
  - Number of ebreak instructions committed (IP, 0/1)
* - 20
  - `ecall`
  - Number of ecall instructions committed (IP, 0/1)
* - 21
  - `fence`
  - Number of fence instructions committed (IP, 0/1)
* - 22
  - `fence.i`
  - Number of fence.i instructions committed (IP, 0/1)
* - 23
  - `mret`
  - Number of mret instructions committed (IP, 0/1)
* - 24
  - branches committed
  - Number of branches committed (IP)
* - 25
  - branches mispredicted
  - Number of branches mispredicted (IP)
* - 26
  - branches taken
  - Number of branches taken (IP)
* - 27
  - unpredictable branches
  - Number of unpredictable branches (IP)
* - 28
  - cycles fetch stalled
  - Number of cycles fetch ready but stalled (OOP)
* - 29
  -
  - Reserved
* - 30
  - cycles decode stalled
  - Number of cycles one or more instructions valid in IB but decode stalled (OOP)
* - 31
  - cycles postsync stalled
  - Number of cycles postsync stalled at decode (OOP)
* - 32
  - cycles presync stalled
  - Number of cycles presync stalled at decode (OOP)
* - 33
  -
  - Reserved
* - 34
  - cycles SB/WB stalled (lsu_store_stall_any)
  - Number of cycles decode stalled due to SB or WB full (OOP)
* - 35
  - cycles DMA DCCM transaction stalled (dma_dccm_stall_any)
  - Number of cycles DMA stalled due to decode for load/store (OOP)
* - 36
  - cycles DMA ICCM transaction stalled (dma_iccm_stall_any)
  - Number of cycles DMA stalled due to fetch (OOP)
* - 37
  - exceptions taken
  - Number of exceptions taken (IP)
* - 38
  - timer interrupts taken
  - Number of timer [^fn-performance-3] interrupts taken (IP)
* - 39
  - external interrupts taken
  - Number of external interrupts taken (IP)
* - 40
  - TLU flushes (flush lower)
  - Number of TLU flushes (flush lower) (IP)
* - 41
  - branch error flushes
  - Number of branch error flushes (IP)
* - 42
  - I-bus transactions - instr
  - Number of instr transactions on I-bus interface (OOP)
* - 43
  - D-bus transactions - ld/st
  - Number of ld/st transactions on D-bus interface (OOP)
* - 44
  - D-bus transactions - misaligned
  - Number of misaligned transactions on D-bus interface (OOP)
* - 45
  - I-bus errors
  - Number of transaction errors on I-bus interface (OOP)
* - 46
  - D-bus errors
  - Number of transaction errors on D-bus interface (OOP)
* - 47
  - cycles stalled due to I- bus busy
  - Number of cycles stalled due to AXI4 or AHB-Lite I-bus busy (OOP)
* - 48
  - cycles stalled due to D- bus busy
  - Number of cycles stalled due to AXI4 or AHB-Lite D-bus busy (OOP)
* - 49
  - cycles interrupts disabled
  - Number of cycles interrupts disabled (MSTATUS.MIE==0) (OOP)
* - 50
  - cycles interrupts stalled while disabled
  - Number of cycles interrupts stalled while disabled (MSTATUS.MIE==0) (OOP)
* - 51 - 53
  -
  - Reserved
* - 54
  - bitmanip committed
  - Number of bit-manipulation operations committed (IP, 0/1)
* - 55
  - D-bus loads committed
  - Number of load instructions to D-bus committed (IP, 0/1)
* - 56
  - D-bus stores committed
  - Number of store instructions to D-bus committed (IP, 0/1)
* - 57 - 511
  -
  - Reserved
* - **Events counted while in Active (C0) or Sleep (C3) states**
  -
  -
* - 512
  - cycles in Sleep (C3) state
  - Number of cycles in Sleep (C3) state (OOP)
* - 513
  - DMA reads (all)
  - Total number of DMA slave read transactions (OOP)
* - 514
  - DMA writes (all)
  - Total number of DMA slave write transactions (OOP)
* - 515
  - DMA reads to DCCM
  - Number of DMA slave read transactions to DCCM (OOP)
* - 516
  - DMA writes to DCCM
  - Number of DMA slave write transactions to DCCM (OOP)
:::

:::{note}
If an event shown as 'Reserved' is selected, no error is reported but counter is not incrementing.
:::

[^fn-performance-2]: NOP is an ALU operation. WFI is implemented as a NOP in VeeR EL2 and, hence, counted as an ALU operation was well.
[^fn-performance-3]: Events counted include interrupts triggered by the standard RISC-V platform-level timer as well as by the two internal timers.
