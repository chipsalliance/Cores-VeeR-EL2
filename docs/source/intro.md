# RISC-V VeeR EL2 Programmer's Reference Manual

**Revision:** 1.4 December 22, 2022

![Logo](img/logo.png)

```
SPDX-License-Identifier: Apache-2.0 Copyright © 2022 CHIPS Alliance.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and limitations under the License.
```

## Document Revision History

:::{list-table} Revision History
:name: tab-revision-history
:header-rows: 1

* - Revision
  - Date
  - Contents
* - 1.0
  - Jan 23, 2020
  - Changes:
    - initial revision
* - 1.1
  - Mar 4, 2020
  - Changes:
    - added note that mscause values are subject to change (section [](memory-map.md#machine-secondary-cause-register-mscause))
    - added note that uninitialized DCCM may cause loads to get incorrect data (section []( error-protection.md#error-detection-and-handling))
    - added Debug Module reset description (section [Debug Module Reset (dbg_rst_l)](clocks.md#debug-module-reset-dbg-rst-l))
    - updated port list ({numref}`tab-core-complex-signals`):
      - added dbg_rst_l signal
      - added footnote clarifying trace port signals
      - fixed width of trace_rv_i_interrupt_ip bus
    - added 'Compliance Test Suite Failures' chapter [](tests.md)
* - 1.2
  - Mar 29, 2020
  - Changes:
    - fixed note how writing illegal value to mrac register is handled by hardware in [](memory-map.md#region-access-control-register-mrac)
    - removed note that mscause values are subject to change in [](memory-map.md#machine-secondary-cause-register-mscause)
    - updated mscause values ({numref}`tab-machine-secondary-cause-register`)
    - added [Internal Timers chapter](timers.md) and references throughout document
    - incremented mimpid register value from '1' to '2' ({numref}`tab-veer-el2-core-specific-std-rv-machine-information-csrs`)
* - 1.3
  - Nov 16, 2020
  - Changes:
    - updated versions of RISC-V Base ISA [[1]](ref-1) and Privileged [[2]](ref-2) and link to RISC-V Debug [[3]](ref-3) specifications (Reference Documents)
    - added RISC-V Bit-manipulation sub-extensions (Reference Documents, sections  [](overview.md#features) and [](overview.md#standard-extensions), and {numref}`tab-list-of-countable-events`)
    - added footnote that misaligned accesses to side-effect regions trigger a misaligned exception instead of the recommended access fault exception ({numref}`tab-handling-misaligned-addresses`)
    - added note to mdseac register description clarifying captured address in [](memory-map.md#d-bus-first-error-address-capture-register-mdseac)
    - clarified that mscause value of '0' indicates no additional information available ([](memory-map.md#machine-secondary-cause-register-mscause))
    - added description of SoC access expectation ([](memory-map.md#expected-soc-behavior-for-accesses))
    - added note that NMIs are fatal ([](memory-map.md#non-maskable-interrupt-nmi-signal-and-vector))
    - added note that mitcnt0/1 register is not cleared if write to it coincides with internal timer interrupt ([Internal Timer Counter 0 / 1 Register (mitcnt0/1)](timers.md#internal-timer-counter-0-1-register-mitcnt0-1))
    - clarified note that debug single-step action is delayed while MPC debug halted ([](power.md#power-states))
    - added cross-references to debug CSR descriptions ({numref}`tab-core-activity-states`, {numref}`tab-veer-el2-multi-core-debug-ctrl-status-signals`, {numref}`tab-veer-el2-std-risc-v-csr-address-map`, and sections [](performance.md#count-impacting-conditions) and [](clocks.md#core-complex-reset-to-debug-mode))
    - added note that debug single-stepping stays pending while MPC debug halted ([](power.md#single-stepping))
    - removed note that PMU halt or run request may not be acknowledged if already in requested activity state ([](power.md#power-control-and-status-signals))
    - amended debug_mode_status signal description ({numref}`tab-veer-el2-multi-core-debug-ctrl-status-signals`)
    - added note that mpc_debug_run_req is required to exit Debug Mode if entered after reset using mpc_reset_run_req ([](power.md#multi-core-debug-control-and-status-signals))
    - added PIC I/O power reduction feature description (sections [](interrupts.md#features), [](interrupts.md#power-reduction), and [](interrupts.md#external-interrupt-pending-registers-meipx) and {numref}`tab-clock-gating-cr`)
    - added note that spurious interrupts may be captured for disabled external interrupts ([](interrupts.md#gateway))
    - added note that edge-triggered interrupt lines must be tied off to inactive state ([](interrupts.md#gateway))
    - fixed gateway initialization macro example ([](interrupts.md#example-interrupt-macros))
    - added note that mtime and mtimecmp registers must be provided by SoC ([](performance.md#standard-risc-v-registers))
    - changed value when writing unsupported event number to mhpmevent3-6 registers to '0' ([](performance.md#events))
    - added note that index field does not have WARL behavior ({numref}`tab-cache-array-dicawics`)
    - added [Debug Support chapter](debugging.md)
    - added 'trace disable' bit to mfdc register ({numref}`tab-feature-disable-cr`)
    - clarified effect of sepd bit of mfdc register ({numref}`tab-feature-disable-cr`)
    - added note regarding physical design considerations for rst_l signal ([Core Complex Reset (rst_l)](clocks.md#core-complex-reset-rst-l))
    - updated 'Reset to Debug-Mode' description ([](clocks.md#core-complex-reset-to-debug-mode))
    - updated trace port interrupt/exception signaling to new optimized scheme ({numref}`tab-core-complex-signals`)
    - added erratum for abstract command register read capability ([](errata.md#debug-abstract-command-register-may-return-non-zero-value-on-read))
    - incremented mimpid register value from '2' to '3' ({numref}`tab-veer-el2-core-specific-std-rv-machine-information-csrs`)
* - 1.4
  - Apr 19, 2022
  - Changes:
    - updated version and link of RISC-V Bit-manipulation [[4]](ref-4) specification (Reference Documents)
    - updated list of sub-extension instructions to RISC-V Bitmanip Extension specification version 0.94-draft (1/20/21) ([](overview.md#standard-extensions))
    - updated note regarding priority of simultaneous store and non-blocking load bus errors ([](memory-map.md#imprecise-bus-error-non-maskable-interrupt))
    - fixed register name and added cross-reference (Footnote 20)
    - added footnote that load/store access crossing upper boundary of DCCM or PIC memory range report base address of access in mtval register (Footnote 22)
    - clarified that correctable error counter/threshold registers are always instantiated (sections [I-Cache Error Counter/Threshold Register (micect)](error-protection.md#i-cache-error-counter-threshold-register-micect), [Iccm Correctable Error Counter/Threshold Register (miccmect)](error-protection.md#iccm-correctable-error-counter-threshold-register-miccmect), and [Dccm Correctable Error Counter/Threshold Register (mdccmect)](error-protection.md#dccm-correctable-error-counter-threshold-register-mdccmect))
    - corrected PIC I/O power reduction feature description ([](interrupts.md#power-reduction))
    - incremented mimpid register value from '3' to '4' ({numref}`tab-veer-el2-core-specific-std-rv-machine-information-csrs`)
:::

## Reference Documents

:::{list-table} Reference Documents
:name: tab-reference-documents
:header-rows: 1

* - **Item #**
  - **Document**
  - **Revision Used**
  - **Comment**
* - <a name="ref-1"></a>1
  - The RISC-V Instruction Set Manual  Volume I: User-Level ISA
  - 20190608-Base-Ratified
  - Specification ratified
* - <a name="ref-2"></a>2
  - The RISC-V Instruction Set Manual  Volume II: Privileged Architecture
  - 20190608-Priv-MSU-Ratified
  - Specification ratified
* - <a name="ref-2-plic"></a>2 (PLIC)
  - The RISC-V Instruction Set Manual Volume II: Privileged Architecture
  - 1.11-draft

    December 1, 2018
  - Last specification version with PLIC chapter
* - <a name="ref-3"></a>3
  - RISC-V External Debug Support
  - 0.13.2
  - Specification ratified
* - <a name="ref-4"></a>4
  - RISC-V Bitmanip Extension
  - 0.94-draft (January 20, 2021)
  - Zba, Zbb, Zbc, and Zbs subextensions are "frozen"
* - <a name="ref-5"></a>5
  - The RISC-V Instruction Set Manual Volume II: Privileged Architecture
  - Document Version 20211203
  - Specification ratified
* - <a name="ref-6"></a>6
  - PMP Enhancements for memory access and execution prevention on Machine mode (Smepmp)
  - Version 1.0, 12/2021
  - Specification ratified

:::

## Abbreviations

:::{table} Abbreviations
:name: tab-abbreviations
:header-rows: 1

| Abbreviation   | Description                                            |
|----------------|--------------------------------------------------------|
| AHB            | Advanced High-performance Bus (by ARM)                |
| AMBA           | Advanced Microcontroller Bus Architecture (by ARM)     |
| ASIC           | Application Specific Integrated Circuit                |
| AXI            | Advanced eXtensible Interface (by ARM)                 |
| CCM            | Closely Coupled Memory (= TCM)                         |
| CPU            | Central Processing Unit                                |
| CSR            | Control and Status Register                            |
| DCCM           | Data Closely Coupled Memory (= DTCM)                   |
| DEC            | DECoder unit (part of core)                            |
| DMA            | Direct Memory Access                                   |
| DTCM           | Data Tightly Coupled Memory (= DCCM)                   |
| ECC            | Error Correcting Code                                  |
| EXU            | EXecution Unit (part of core)                          |
| ICCM           | Instruction Closely Coupled Memory (= ITCM)            |
| IFU            | Instruction Fetch Unit                                 |
| ITCM           | Instruction Tightly Coupled Memory (= ICCM)            |
| JTAG           | Joint Test Action Group                                |
| LSU            | Load/Store Unit (part of core)                         |
| MPC            | Multi-Processor Controller                             |
| MPU            | Memory Protection Unit                                 |
| NMI            | Non-Maskable Interrupt                                 |
| PIC            | Programmable Interrupt Controller                      |
| PLIC           | Platform-Level Interrupt Controller                    |
| POR            | Power-On Reset                                         |
| RAM            | Random Access Memory                                   |
| RAS            | Return Address Stack                                   |
| ROM            | Read-Only Memory                                       |
| SECDED         | Single-bit Error Correction/Double-bit Error Detection |
| SEDDED         | Single-bit Error Detection/Double-bit Error Detection  |
| SoC            | System on Chip                                         |
| TBD            | To Be Determined                                       |
| TCM            | Tightly Coupled Memory (= CCM)                         |
:::
