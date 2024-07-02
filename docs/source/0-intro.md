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

| Revision   | Date         | Contents                                                                                                                                                                                                                                                                                                                                                                                                                                             |
|------------|--------------|------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 1.0        | Jan 23, 2020 | Initial revision                                                                                                                                                                                                                                                                                                                                                                                                                                     |
| 1.1        | Mar 4, 2020  |- Added note that mscause values are subject to change (Section 2.8.5) <br> - Added note that uninitialized DCCM may cause loads to get incorrect data (Section  3.4) <br> - Added Debug Module reset description (Section 14.3.2) <br> - Updated port list (Table 15-1): <br> - Added dbg_rst_l signal <br> - Added footnote clarifying trace port signals <br> - Fixed width of trace_rv_i_interrupt_ip bus <br> - Added 'Compliance Test Suite Failures' chapter (Chapter 17) |
| 1.2        | Mar 29, 2020 |- Fixed note how writing illegal value to mrac register is handled by hardware  (Section 2.8.1) <br> - Removed note that mscause values are subject to change (Section 2.8.5) <br> - Updated mscause values (Table 2-10) <br> - Added Internal Timers chapter and references throughout document (Chapter 4) <br> - Incremented mimpid register value from '1' to '2' (Table 12-1)                                                                                   |
| 1.3        | Nov 16, 2020 |- Updated versions of RISC-V Base ISA [1] and Privileged [2] and link to RISC-V  Debug [3] specifications (Reference Documents) <br> - Added RISC-V Bit-manipulation sub-extensions (Reference Documents, Sections  1.1 and 1.4, and Table 7-1) <br> - Added footnote that misaligned accesses to side-effect regions trigger a misaligned  exception instead of the recommended access fault exception (Table 2-3) <br> - Added note to mdseac register description clarifying captured address (Section  2.8.3) <br> - Clarified that mscause value of '0' indicates no additional information available  (Section 2.8.5) <br> - Added description of SoC access expectation (Section 2.12) <br> - Added note that NMIs are fatal (Section 2.16) <br> - Added note that mitcnt0/1 register is not cleared if write to it coincides with  internal timer interrupt (Section 4.4.1) <br> - Clarified note that debug single-step action is delayed while MPC debug halted  (Section 5.3) <br> - Added cross-references to debug CSR descriptions (Table 5-2, Table 5-4, Table  12-2, and Sections 7.4 and 14.3.4) <br> - Added note that debug single-stepping stays pending while MPC debug halted  (Section 5.4.1.1) <br> - Removed note that PMU halt or run request may not be acknowledged if already in  requested activity state (Section 5.4.2.1) <br> - Amended debug_mode_status signal description (Table 5-4) <br> - Added note that mpc_debug_run_req is required to exit Debug Mode if entered  after reset using mpc_reset_run_req (Section 5.4.2.2) <br> - Added PIC I/O power reduction feature description (Sections 6.1, 6.9, and 6.12.3  and Table 10-2) <br> - Added note that spurious interrupts may be captured for disabled external interrupts  (Section 6.3.2) <br> - Added note that edge-triggered interrupt lines must be tied off to inactive state  (Section 6.3.2) <br> - Fixed gateway initialization macro example (Section 6.15.2) <br> - Added note that mtime and mtimecmp registers must be provided by SoC (Section  7.2.1) <br> - Changed value when writing unsupported event number to mhpmevent3-6 registers to '0' (Section 7.5) <br> - Added note that index field does not have WARL behavior (Table 8-1) <br> - Added Debug Support chapter (Chapter 9) <br> - Added 'trace disable' bit to mfdc register (Table 10-1) <br> - Clarified effect of sepd bit of mfdc register (Table 10-1) <br> - Added note regarding physical design considerations for rst_l signal (Section  14.3.1) <br> - Updated 'Reset to Debug-Mode' description (Section 14.3.4) <br> - Updated trace port interrupt/exception signaling to new optimized scheme (Table  15-1) <br> - Added erratum for abstract command register read capability (Section 18.2) <br> - Incremented mimpid register value from '2' to '3' (Table 12-1) |
| 1.4        | Apr 19, 2022 |- Updated version and link of RISC-V Bit-manipulation [4] specification (Reference  Documents) <br> - Updated list of sub-extension instructions to RISC-V Bitmanip Extension  specification version 0.94-draft (1/20/21) (Section 1.4) <br> - Updated note regarding priority of simultaneous store and non-blocking load bus  errors (Section 2.7.1) <br> - Fixed register name and added cross-reference (Footnote 20) <br> - Added footnote that load/store access crossing upper boundary of DCCM or PIC  memory range report base address of access in mtval register (Footnote 22) <br> - Clarified that correctable error counter/threshold registers are always instantiated  (Sections 3.5.1, 3.5.2, and 3.5.3) <br> - Corrected PIC I/O power reduction feature description (Section 6.9) <br> - Incremented mimpid register value from '3' to '4' (Table 12-1) |

## Reference Documents

| Item #           | Document                                                              | Revision Used                 | Comment                         |
|------------------|-----------------------------------------------------------------------|-------------------------------|---------------------------------|
| 1                | The RISC-V Instruction Set Manual  Volume I: User-Level ISA           | 20190608-Base-Ratified        | Specification ratified          |
| 2                | The RISC-V Instruction Set Manual  Volume II: Privileged Architecture | 20190608-Priv-MSU-Ratified    | Specification ratified          |
| 2  (PLIC)                | The RISC-V Instruction Set Manual Volume II: Privileged Architecture| 1.11-draft                    | Last specification version with December 1, 2018 | PLIC chapter                                                          |                               |                                 |
| 3                | RISC-V External Debug Support                                         | 0.13.2                        | Specification ratified          |
| 4                | RISC-V Bitmanip Extension                                             | 0.94-draft (January 20, 2021) | Zba, Zbb, Zbc, and Zbs subextensions are "frozen"                                 |

## Abbreviations

| Abbreviation   | Description                                            |
|----------------|--------------------------------------------------------|
| AHB            | Advanced High-performance Bus (by ARM®)                |
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


