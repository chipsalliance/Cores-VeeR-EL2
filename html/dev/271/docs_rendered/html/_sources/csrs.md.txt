# CSR Address Map

## Standard RISC-V CSRs

{numref}`tab-veer-el2-core-specific-std-rv-machine-information-csrs` lists the VeeR EL2 core-specific standard RISC-V Machine Information CSRs.

:::{list-table} VeeR EL2 Core-Specific Standard RISC-V Machine Information CSRs
:name: tab-veer-el2-core-specific-std-rv-machine-information-csrs

* - **Number**
  - **Privilege**
  - **Name**
  - **Description**
  - **Value**
* - 0x301
  - MRW
  - misa
  - ISA and extensions

    **Note**: writes ignored
  - 0x4000_1104
* - 0xF11
  - MRO
  - mvendorid
  - Vendor ID
  - 0x0000_0045
* - 0xF12
  - MRO
  - marchid
  - Architecture ID
  - 0x0000_0010
* - 0xF13
  - MRO
  - mimpid
  - Implementation ID
  - 0x0000_0004
* - 0xF14
  - MRO
  - mhartid
  - Hardware thread ID
  - see [](adaptations.md#machine-hardware-thread-id-register-mhartid)
:::

{numref}`tab-veer-el2-std-risc-v-csr-address-map` lists the VeeR EL2 standard RISC-V CSR address map.

:::{list-table} VeeR EL2 Standard RISC-V CSR Address Map
:name: tab-veer-el2-std-risc-v-csr-address-map

* - **Number**
  - **Privilege**
  - **Name**
  - **Description**
  - **Section**
* - 0x300
  - MRW
  - mstatus
  - Machine status
  - \-
* - 0x304
  - MRW
  - mie
  - Machine interrupt enable
  - [](adaptations.md#machine-interrupt-enable-mie-and-machine-interrupt-pending-mip-registers)
* - 0x305
  - MRW
  - mtvec
  - Machine trap-handler base address
  - \-
* - 0x320
  - MRW
  - mcountinhibit
  - Machine counter-inhibit register
  - [](performance.md#standard-risc-v-registers)
* - 0x323
  - MRW
  - mhpmevent3
  - Machine performance-monitoring event selector 3
  - [](performance.md#standard-risc-v-registers)
* - 0x324
  - MRW
  - mhpmevent4
  - Machine performance-monitoring event selector 4
  - [](performance.md#standard-risc-v-registers)
* - 0x325
  - MRW
  - mhpmevent5
  - Machine performance-monitoring event selector 5
  - [](performance.md#standard-risc-v-registers)
* - 0x326
  - MRW
  - mhpmevent6
  - Machine performance-monitoring event selector 6
  - [](performance.md#standard-risc-v-registers)
* - 0x340
  - MRW
  - mscratch
  - Scratch register for machine trap handlers
  - \-
* - 0x341
  - MRW
  - mepc
  - Machine exception program counter
  - \-
* - 0x342
  - MRW
  - mcause
  - Machine trap cause
  - [](adaptations.md#machine-cause-register-mcause)
* - 0x343
  - MRW
  - mtval
  - Machine bad address or instruction
  - \-
* - 0x344
  - MRW
  - mip
  - Machine interrupt pending
  - [](adaptations.md#machine-interrupt-enable-mie-and-machine-interrupt-pending-mip-registers)
* - 0x7A0
  - MRW
  - tselect
  - Debug/Trace trigger register select
  - [](debugging.md#trigger-select-register-tselect)
* - 0x7A1
  - MRW
  - tdata1
  - First Debug/Trace trigger data
  - [](debugging.md#trigger-data-1-register-tdata1)
* - 0x7A1
  - MRW
  - mcontrol
  - Match control
  - [](debugging.md#match-control-register-mcontrol)
* - 0x7A2
  - MRW
  - tdata2
  - Second Debug/Trace trigger data
  - [](debugging.md#trigger-data-2-register-tdata2)
* - 0x7B0
  - DRW
  - dcsr
  - Debug control and status register
  - [](debugging.md#debug-control-and-status-register-dcsr)
* - 0x7B1
  - DRW
  - dpc
  - Debug PC
  - [](debugging.md#debug-pc-register-dpc)
* - 0xB00
  - MRW
  - mcycle
  - Machine cycle counter
  - [](performance.md#standard-risc-v-registers)
* - 0xB02
  - MRW
  - minstret
  - Machine instructions-retired counter
  - [](performance.md#standard-risc-v-registers)
* - 0xB03
  - MRW
  - mhpmcounter3
  - Machine performance-monitoring counter 3
  - [](performance.md#standard-risc-v-registers)
* - 0xB04
  - MRW
  - mhpmcounter4
  - Machine performance-monitoring counter 4
  - [](performance.md#standard-risc-v-registers)
* - 0xB05
  - MRW
  - mhpmcounter5
  - Machine performance-monitoring counter 5
  - [](performance.md#standard-risc-v-registers)
* - 0xB06
  - MRW
  - mhpmcounter6
  - Machine performance-monitoring counter 6
  - [](performance.md#standard-risc-v-registers)
* - 0xB80
  - MRW
  - mcycleh
  - Upper 32 bits of mcycle, RV32I only
  - [](performance.md#standard-risc-v-registers)
* - 0xB82
  - MRW
  - minstreth
  - Upper 32 bits of minstret, RV32I only
  - [](performance.md#standard-risc-v-registers)
* - 0xB83
  - MRW
  - mhpmcounter3h
  - Upper 32 bits of mhpmcounter3, RV32I only
  - [](performance.md#standard-risc-v-registers)
* - 0xB84
  - MRW
  - mhpmcounter4h
  - Upper 32 bits of mhpmcounter4, RV32I only
  - [](performance.md#standard-risc-v-registers)
* - 0xB85
  - MRW
  - mhpmcounter5h
  - Upper 32 bits of mhpmcounter5, RV32I only
  - [](performance.md#standard-risc-v-registers)
* - 0xB86
  - MRW
  - mhpmcounter6h
  - Upper 32 bits of mhpmcounter6, RV32I only
  - [](performance.md#standard-risc-v-registers)
:::

## Non-Standard RISC-V CSRs

{numref}`tab-veer-el2-non-std-risc-v-csr-address-map` summarizes the VeeR EL2 non-standard RISC-V CSR address map.

:::{list-table} VeeR EL2 Non-Standard RISC-V CSR Address Map
:name: tab-veer-el2-non-std-risc-v-csr-address-map

* - **Number**
  - **Privilege**
  - **Name**
  - **Description**
  - **Section**
* - 0x7C0
  - MRW
  - mrac
  - Region access control
  - [](memory-map.md#region-access-control-register-mrac)
* - 0x7C2
  - MRW
  - mcpc
  - Core pause control
  - [](power.md#core-pause-control-register-mcpc)
* - 0x7C4
  - DRW
  - dmst
  - Memory synchronization trigger (Debug Mode only)
  - [](memory-map.md#memory-synchronization-trigger-register-dmst)
* - 0x7C6
  - MRW
  - mpmc
  - Power management control
  - [](power.md#power-management-control-register-mpmc)
* - 0x7C8
  - DRW
  - dicawics
  - I-cache array/way/index selection (Debug Mode only)
  - [](cache.md#i-cache-arraywayindex-selection-register-dicawics)
* - 0x7C9
  - DRW
  - dicad0
  - I-cache array data 0 (Debug Mode only)
  - [](cache.md#i-cache-array-data-0-register-dicad0)
* - 0x7CA
  - DRW
  - dicad1
  - I-cache array data 1 (Debug Mode only)
  - [](cache.md#i-cache-array-data-1-register-dicad1)
* - 0x7CB
  - DRW
  - dicago
  - I-cache array go (Debug Mode only)
  - [](cache.md#i-cache-array-go-register-dicago)
* - 0x7CC
  - DRW
  - dicad0h
  - I-cache array data 0 high (Debug Mode only)
  - [](cache.md#i-cache-array-data-0-high-register-dicad0h)
* - 0x7CE
  - MRW
  - mfdht
  - Force debug halt threshold
  - [](power.md#forced-debug-halt-threshold-register-mfdht)
* - 0x7CF
  - MRW
  - mfdhs
  - Force debug halt status
  - [](power.md#forced-debug-halt-status-register-mfdhs)
* - 0x7D2
  - MRW
  - mitcnt0
  - Internal timer counter 0
  - [](timers.md#internal-timer-counter-0--1-register-mitcnt01)
* - 0x7D3
  - MRW
  - mitb0
  - Internal timer bound 0
  - [](timers.md#internal-timer-bound-0--1-register-mitb01)
* - 0x7D4
  - MRW
  - mitctl0
  - Internal timer control 0
  - [](timers.md#internal-timer-control-0--1-register-mitctl01)
* - 0x7D5
  - MRW
  - mitcnt1
  - Internal timer counter 1
  - [](timers.md#internal-timer-counter-0--1-register-mitcnt01)
* - 0x7D6
  - MRW
  - mitb1
  - Internal timer bound 1
  - [](timers.md#internal-timer-bound-0--1-register-mitb01)
* - 0x7D7
  - MRW
  - mitctl1
  - Internal timer control 1
  - [](timers.md#internal-timer-control-0--1-register-mitctl01)
* - 0x7F0
  - MRW
  - micect
  - I-cache error counter/threshold
  - [](error-protection.md#i-cache-error-counterthreshold-register-micect)
* - 0x7F1
  - MRW
  - miccmect
  - ICCM correctable error counter/threshold
  - [](error-protection.md#iccm-correctable-error-counterthreshold-register-miccmect)
* - 0x7F2
  - MRW
  - mdccmect
  - DCCM correctable error counter/threshold
  - [](error-protection.md#dccm-correctable-error-counterthreshold-register-mdccmect)
* - 0x7F8
  - MRW
  - mcgc
  - Clock gating control
  - [](core-control.md#clock-gating-control-register-mcgc)
* - 0x7F9
  - MRW
  - mfdc
  - Feature disable control
  - [](core-control.md#feature-disable-control-register-mfdc)
* - 0x7FF
  - MRW
  - mscause
  - Machine secondary cause
  - [](memory-map.md#machine-secondary-cause-register-mscause)
* - 0xBC0
  - MRW
  - mdeau
  - D-Bus error address unlock
  - [](memory-map.md#d-bus-error-address-unlock-register-mdeau)
* - 0xBC8
  - MRW
  - meivt
  - External interrupt vector table
  - [](interrupts.md#external-interrupt-vector-table-register-meivt)
* - 0xBC9
  - MRW
  - meipt
  - External interrupt priority threshold
  - [](interrupts.md#external-interrupt-priority-threshold-register-meipt)
* - 0xBCA
  - MRW
  - meicpct
  - External interrupt claim ID / priority level capture trigger
  - [](interrupts.md#external-interrupt-claim-id--priority-level-capture-trigger-register-meicpct)
* - 0xBCB
  - MRW
  - meicidpl
  - External interrupt claim ID's priority level
  - [](interrupts.md#external-interrupt-claim-ids-priority-level-register-meicidpl)
* - 0xBCC
  - MRW
  - meicurpl
  - External interrupt current priority level
  - [](interrupts.md#external-interrupt-current-priority-level-register-meicurpl)
* - 0xFC0
  - MRO
  - mdseac
  - D-bus first error address capture
  - [](memory-map.md#d-bus-first-error-address-capture-register-mdseac)
* - 0xFC8
  - MRO
  - meihap
  - External interrupt handler address pointer
  - [](interrupts.md#external-interrupt-handler-address-pointer-register-meihap)
:::
