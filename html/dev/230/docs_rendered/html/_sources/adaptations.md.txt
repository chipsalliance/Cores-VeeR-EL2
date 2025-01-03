# Standard RISC-V CSRs with Core-Specific Adaptations

A summary of standard RISC-V control/status registers in CSR space with platform-specific adaptations:

* [](adaptations.md#machine-interrupt-enable-mie-and-machine-interrupt-pending-mip-registers)
* [](adaptations.md#machine-cause-register-mcause)
* [](adaptations.md#machine-hardware-thread-id-register-mhartid)

All reserved and unused bits in these control/status registers must be hardwired to '0'.
Unless otherwise noted, all read/write control/status registers must have WARL (Write Any value, Read Legal value) behavior.

## Machine Interrupt Enable (mie) and Machine Interrupt Pending (mip) Registers

The standard RISC-V `mie` and `mip` registers hold the machine interrupt enable and interrupt pending bits, respectively.
Since VeeR EL2 only supports machine mode, all supervisor- and user-specific bits are not implemented.
In addition, the `mie/mip` registers also host the platform-specific local interrupt enable/pending bits (shown with a gray background in {numref}`tab-machine-interrupt-enable-register` and {numref}`tab-machine-interrupt-pending-register` below).

The `mie` register is a standard read/write CSR.

:::{list-table} Machine Interrupt Enable Register (mie, at CSR 0x304)
:name: tab-machine-interrupt-enable-register
:header-rows: 1

* - **Field**
  - **Bits**
  - **Description**
  - **Access**
  - **Reset**
* - Reserved
  - 31
  - Reserved
  - R
  - 0
* - mceie
  - 30
  - Correctable error local interrupt enable
  - R/W
  - 0
* - mitie0
  - 29
  - Internal timer 0 local interrupt enable
  - R/W
  - 0
* - mitie1
  - 28
  - Internal timer 1 local interrupt enable
  - R/W
  - 0
* - Reserved
  - 27:12
  - Reserved
  - R
  - 0
* - meie
  - 11
  - Machine external interrupt enable
  - R/W
  - 0
* - Reserved
  - 10:8
  - Reserved
  - R
  - 0
* - mtie
  - 7
  - Machine timer interrupt enable
  - R/W
  - 0
* - Reserved
  - 6:4
  - Reserved
  - R
  - 0
* - msie
  - 3
  - Machine software interrupt enable
  - R/W
  - 0
* - Reserved
  - 2:0
  - Reserved
  - R
  - 0
:::

The `mip` register is a standard read/write CSR.

:::{note}
All M-mode interrupt pending bits of the read/write `mip` register are read-only.
:::

:::{list-table} Machine Interrupt Pending Register (mip, at CSR 0x344)
:name: tab-machine-interrupt-pending-register
:header-rows: 1

* - **Field**
  - **Bits**
  - **Description**
  - **Access**
  - **Reset**
* - Reserved
  - 31
  - Reserved
  - R
  - 0
* - mceip
  - 30
  - Correctable error local interrupt pending
  - R
  - 0
* - mitip0
  - 29
  - Internal timer 0 local interrupt pending
  - R
  - 0
* - mitip1
  - 28
  - Internal timer 1 local interrupt pending
  - R
  - 0
* - Reserved
  - 27:12
  - Reserved
  - R
  - 0
* - meip
  - 11
  - Machine external interrupt pending
  - R
  - 0
* - Reserved
  - 10:8
  - Reserved
  - R
  - 0
* - mtip
  - 7
  - Machine timer interrupt pending
  - R
  - 0
* - Reserved
  - 6:4
  - Reserved
  - R
  - 0
* - msip
  - 3
  - Machine software interrupt pending
  - R
  - 0
* - Reserved
  - 2:0
  - Reserved
  - R
  - 0
:::

## Machine Cause Register (mcause)

The standard RISC-V mcause register indicates the cause for a trap as shown in {numref}`tab-machine-cause-register`, including standard exceptions/interrupts, platform-specific local interrupts (with light gray background), and NMI causes (with dark gray background).

Additional trap information is provided in the mscause register, see [](memory-map.md#machine-secondary-cause-register-mscause) which allows the determination of the exact cause of a trap for cases where multiple, different conditions share a single trap code.

The `mcause` register has WLRL (Write Legal value, Read Legal value) behavior.

This register is a standard read/write CSR.

:::{list-table} Machine Cause Register (mcause, at CSR 0x342)
:name: tab-machine-cause-register
:header-rows: 1

* - **Type**
  - **Trap Code**
  - **Value mcause[31:0]**
  - **Description**
  - **Section(s)**
* - **NMI**
  - N/A
  - 0x0000_0000
  - NMI pin assertion
  - [](memory-map.md#non-maskable-interrupt-nmi-signal-and-vector)
* - **Exception**
  - 1
  - 0x0000_0001
  - Instruction access fault
  - [](memory-map.md#unmapped-addresses), [](memory-map.md#uncorrectable-ecc-errors), and [](error-protection.md#error-detection-and-handling)
* -
  - 2
  - 0x0000_0002
  - Illegal instruction
  - \-
* -
  - 3
  - 0x0000_0003
  - Breakpoint
  - \-
* -
  - 4
  - 0x0000_0004
  - Load address misaligned
  - [](memory-map.md#misaligned-accesses)
* -
  - 5
  - 0x0000_0005
  - Load access fault
  - [](memory-map.md#unmapped-addresses), [](memory-map.md#uncorrectable-ecc-errors), and [](error-protection.md#error-detection-and-handling)
* -
  - 6
  - 0x0000_0006
  - Store/AMO address misaligned
  - [](memory-map.md#misaligned-accesses)
* -
  - 7
  - 0x0000_0007
  - Store/AMO access fault
  - [](memory-map.md#unmapped-addresses), [](memory-map.md#uncorrectable-ecc-errors), and [](error-protection.md#error-detection-and-handling)
* -
  - 11
  - 0x0000_000B
  - Environment call from M-mode
  - \-
* - **Interrupt**
  - 3
  - 0x8000_0003
  - Machine software interrupt
  - [](memory-map.md#software-interrupts)
* -
  - 7
  - 0x8000_0007
  - Machine timer [^fn-adaptations-1] interrupt
  - \-
* -
  - 11
  - 0x8000_000B
  - Machine external interrupt
  - [](interrupts.md)
* -
  - 28
  - 0x8000_001C
  - Machine internal timer 1 local interrupt
  - [](timers.md#internal-timer-local-interrupts)
* -
  - 29
  - 0x8000_001D
  - Machine internal timer 0 local interrupt
  - [](timers.md#internal-timer-local-interrupts)
* -
  - 30
  - 0x8000_001E
  - Machine correctable error local interrupt
  - [](memory-map.md#correctable-error-local-interrupt)
* - **NMI**
  - N/A
  - 0xF000_0000
  - Machine D-bus store error NMI
  - [](memory-map.md#imprecise-bus-error-non-maskable-interrupt) and [](memory-map.md#non-maskable-interrupt-nmi-signal-and-vector)
* -
  - N/A
  - 0xF000_0001
  - Machine D-bus non-blocking load error NMI
  - [](memory-map.md#imprecise-bus-error-non-maskable-interrupt) and [](memory-map.md#non-maskable-interrupt-nmi-signal-and-vector)
* -
  - N/A
  - 0xF000_1000
  - Machine Fast Interrupt double-bit ECC error NMI
  - [](interrupts.md#fast-interrupt-redirect) and [](memory-map.md#non-maskable-interrupt-nmi-signal-and-vector)
* -
  - N/A
  - 0xF000_1001
  - Machine Fast Interrupt DCCM region access error NMI
  - [](interrupts.md#fast-interrupt-redirect) and [](memory-map.md#non-maskable-interrupt-nmi-signal-and-vector)
* -
  - N/A
  - 0xF000_1002
  - Machine Fast Interrupt non-DCCM region NMI
  - [](interrupts.md#fast-interrupt-redirect) and [](memory-map.md#non-maskable-interrupt-nmi-signal-and-vector)
:::

[^fn-adaptations-1]: Core external timer

:::{note}
All other values are reserved.
:::

## Machine Hardware Thread ID Register (mhartid)

The standard RISC-V `mhartid` register provides the integer ID of the hardware thread running the code.
Hart IDs must be unique.
Hart IDs might not necessarily be numbered contiguously in a multiprocessor system, but at least one hart must have a hart ID of zero.

:::{note}
In certain cases, it must be ensured that exactly one hart runs some code (e.g., at reset), hence the requirement for one hart to have a known hart ID of zero.
:::

The `mhartid` register is split into two fixed-sized fields.
The SoC must provide a hardwired core ID on the `core_id[31:4]` bus.
The value provided on that bus sources the `mhartid` register's *coreid* field.
If the SoC hosts more than one RISC-V core, each core must have its own unique `core_id` value.
Each hardware thread of the core has a unique, hardwired thread ID which is reflected in the `mhartid` register's *hartid* field starting at 0x0 up to 0xF.

VeeR EL2 implements a single hardware thread with thread ID 0x0.

This register is a standard read-only CSR.

:::{list-table} Machine Hardware Thread ID Register (mhartid, at CSR 0xF14)
:name: tab-machine-hw-thread-id-register
:header-rows: 1

* - **Field**
  - **Bits**
  - **Description**
  - **Access**
  - **Reset**
* - coreid
  - 31:4
  - Core ID of this VeeR EL2
  - R
  - `core_id[31:4]` bus value  (see {numref}`tab-core-complex-signals`)
* - hartid
  - 3:0
  - Hardwired per-core hart ID:  0x0: thread 0 (master thread)
  - R
  - 0x0
:::
