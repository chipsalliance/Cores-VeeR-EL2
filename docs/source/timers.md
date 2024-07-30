# Internal Timers

This chapter describes the internal timer feature of the VeeR EL2 core.

## Features

The VeeR EL2's internal timer features are:

* Two independently controlled 32-bit timers
  * Dedicated counter
  * Dedicated bound
  * Dedicated control to enable/disable incrementing generally, during power management Sleep, and while executing PAUSE
  * Enable/disable local interrupts (in standard RISC-V `mie` register)
* Cascade mode to form a single 64-bit timer

## Description

The VeeR EL2 core implements two internal timers.
The `mitcnt0` and `mitcnt1` registers (see [Internal Timer Counter 0 / 1 Register (mitcnt0/1)](timers.md#internal-timer-counter-0-1-register-mitcnt0-1)) are 32-bit unsigned counters.
Each counter also has a corresponding 32-bit unsigned bound register (i.e., `mitb0` and `mitb1`, see [Internal Timer Bound 0 / 1 Register (mitb0/1)](timers.md#internal-timer-bound-0-1-register-mitb0-1)) and control register (i.e., `mitctl0` and `mitctl1`, see [Internal Timer Control 0 / 1 Register (mitctl0/1)](timers.md#internal-timer-control-0-1-register-mitctl0-1)).

All registers are cleared at reset unless otherwise noted.
After reset, the counters start incrementing the next clock cycle if the increment conditions are met.
All registers can be read as well as written at any time.
The `mitcnt0/1` and `mitb0/1` registers may be written to any 32-bit value.
If the conditions to increment are met, the corresponding counter `mitcnt0/1` increments every clock cycle.

Cascade mode (see [Internal Timer Control 0 / 1 Register (mitctl0/1)](timers.md#internal-timer-control-0-1-register-mitctl0-1)) links the two counters together.
The `mitcnt1` register is only incremented when the conditions to increment `mitcnt1` are met and the `mitcnt0` register is greater than or equal to the bound in its `mitb0` register.

For each timer, a local interrupt (see [](timers.md#internal-timer-local-interrupts)) is triggered when that counter is at or above its bound.
When a counter is at or above its bound, it gets cleared the next clock cycle (i.e., the interrupt condition is not sticky).

:::{note}
If the core is in Debug Mode and being single-stepped, it may take multiple clock cycles to execute a single instruction. If the conditions to increment are met, the counter increments for every clock cycle it takes to execute a single instruction. Therefore, every executed single-stepped instruction in Debug Mode may result in multiple counter increments.
:::

:::{note}
If the core is in the Debug Mode's Halted (i.e., db-halt) state, an internal timer interrupt does not transition the core back to the Active (i.e., Running) state.
:::

## Internal Timer Local Interrupts

Local-to-the-core interrupts for internal timer 0 and 1 have pending [^fn-timers-1] (*mitip0/1*) and enable (*mitie0/1*) bits in bit positions 29 (for internal timer 0) and 28 (for internal timer 1) of the standard RISC-V `mip` (see {numref}`tab-machine-interrupt-pending-register`) and `mie` (see {numref}`tab-machine-interrupt-enable-register`) registers, respectively.
The priority is lower than the RISC-V External, Software, and Timer interrupts (see {numref}`tab-veer-el2-platform-specific-and-std-risc-v-interrupt-priorities`).
The internal timer 0 and 1 local interrupts have an mcause value of 0x8000_001D (for internal timer 0) and 0x8000_001C (for internal timer 1) (see {numref}`tab-machine-cause-register`).

:::{note}
If both internal timer interrupts occur in the same cycle, internal timer 0's interrupt has higher priority than internal timer 1's interrupt.
:::

:::{note}
A common interrupt service routine may be used for both interrupts.
The `mcause` register value differentiates the two local interrupts.
:::

[^fn-timers-1]: Since internal timer interrupts are not latched (i.e., not “sticky”) and these local interrupts are only signaled for one core clock cycle, it is unlikely that they are detected by firmware in the `mip` register.

## Control/Status Registers

A summary of platform-specific internal timer control/status registers in CSR space:

- [Internal Timer Counter 0 / 1 Register (mitcnt0/1)](timers.md#internal-timer-counter-0-1-register-mitcnt0-1)
- [Internal Timer Bound 0 / 1 Register (mitb0/1)](timers.md#internal-timer-bound-0-1-register-mitb0-1)
- [Internal Timer Control 0 / 1 Register (mitctl0/1)](timers.md#internal-timer-control-0-1-register-mitctl0-1)

All reserved and unused bits in these control/status registers must be hardwired to '0'.
Unless otherwise noted, all read/write control/status registers must have WARL (Write Any value, Read Legal value) behavior.

### Internal Timer Counter 0 / 1 Register (mitcnt0/1)

The `mitcnt0` and `mitcnt1` registers are the counters of the internal timer 0 and 1, respectively.

The conditions to increment a counter are:

- The *enable* bit in the corresponding mitctl0/1 register is '1',
- if the core is in Sleep (i.e., pmu/fw-halt) state, the *halt_en* bit in the corresponding `mitctl0/1` register is '1',
- if the core is paused, the *pause_en* bit in the corresponding `mitctl0/1` register is '1', and
- the core is not in Debug Mode, except while executing a single-stepped instruction.

A counter is cleared if its value is greater than or equal to its corresponding mitb0/1 register.

:::{note}
If a write to the `mitcnt0/1` register is committed in the same clock cycle as the timer interrupt condition is met, the internal timer local interrupt is triggered, if enabled, but the counter is not cleared in this case. Instead, the counter is set to the written value.
:::

These registers are mapped to the non-standard read/write CSR address space.

:::{list-table} Internal Timer Counter 0 / 1 Register (mitcnt0/1, at CSR 0x7D2 / 0x7D5)
:name: tab-internal-timer-counter-register
:header-rows: 1
:align: left

* - Field
  - Bits
  - Description
  - Access
  - Reset
* - count
  - 31:0
  - Counter
  - R/W
  - 0
:::

### Internal Timer Bound 0 / 1 Register (mitb0/1)

The `mitb0` and `mitb1` registers hold the upper bounds of the internal timer 0 and 1, respectively.

These registers are mapped to the non-standard read/write CSR address space.

:::{list-table} Internal Timer Bound 0 / 1 Register (mitb0/1, at CSR 0x7D3 / 0x7D6)
:name: tab-internal-timer-bound-register
:header-rows: 1
:align: left

* - Field
  - Bits
  - Description
  - Access
  - Reset
* - bound
  - 31:0
  - Bound
  - R/W
  - 0xFFFF_FFFF
:::

### Internal Timer Control 0 / 1 Register (mitctl0/1)

The `mitctl0` and `mitctl1` registers provide the control bits of the internal timer 0 and 1, respectively.

:::{note}
When in cascade mode, it is highly recommended to program the enable, *halt_en*, and *pause_en* control bits of the `mitctl1` register the same as the `mitctl0` register.
:::

These registers are mapped to the non-standard read/write CSR address space.

:::{list-table} Internal Timer Control 0 / 1 Register (mitctl0/1, at CSR 0x7D4 / 0x7D7)
:name: tab-internal-timer-control-register
:header-rows: 1
:align: left

* - Field
  - Bits
  - Description
  - Access
  - Reset
* - Reserved
  - 31:4
  - Reserved
  - R
  - 0
* - cascade **(mitctl1 only)**
  - 3
  - Cascade mode:
    - 0: Disable cascading (i.e., both internal timers operate independently) (default)
    - 1: Enable cascading (i.e., internal timer 0 and 1 are combined into a single 64-bit timer)
  - R/W
  - 0
* - pause_en
  - 2
  - Enable/disable incrementing timer counter while executing PAUSE:
    - 0: Disable incrementing (default)
    - 1: Enable incrementing 
      
    **Note:** If ‘1’ and the core is pausing (see [](power.md#core-pause-control-register-mcpc)), an internal timer interrupt terminates PAUSE and regular execution is resumed.
  - R/W
  - 0
* - halt_en
  - 1
  - Enable/disable incrementing timer counter while in Sleep (i.e., pmu/fw- halt) state:
    - 0: Disable incrementing (default)
    - 1: Enable incrementing 
    
    **Note:** If ‘1’ and the core is in Sleep (i.e., pmu/fw-halt) state, an internal timer interrupt transitions the core back to the Active (i.e., Running) state and regular execution is resumed.
  - R/W
  - 0
* - enable
  - 0
  - Enable/disable incrementing timer counter:
    - 0: Disable incrementing
    - 1: Enable incrementing (default)
  - R/W
  - 1
:::
