# Low-Level Core Control

This chapter describes some low-level core control registers.

## Control/Status Registers

A summary of platform-specific control/status registers in CSR space:

* Feature Disable Control Register (mfdc), see [](core-control.md#feature-disable-control-register-mfdc)
* Clock Gating Control Register (mcgc), see [](core-control.md#clock-gating-control-register-mcgc)

All reserved and unused bits in these control/status registers must be hardwired to '0'.
Unless otherwise noted, all read/write control/status registers must have WARL (Write Any value, Read Legal value) behavior.

### Feature Disable Control Register (mfdc)

The `mfdc` register hosts low-level core control bits to disable specific features.
This may be useful in case a feature intended to increase core performance should prove to have problems.

:::{note}
`fence.i` instructions are required before and after writes to the `mfdc` register.
:::

:::{note}
The default state of the controllable features is 'enabled'. Firmware may turn off a feature if needed.
:::

This register is mapped to the non-standard read/write CSR address space.

:::{list-table} Feature Disable Control Register (mfdc, at CSR 0x7F9). Field Bits Description
:name: tab-feature-disable-cr
:header-rows: 1

* - **Field**
  - **Bits**
  - **Description**
  - **Access**
  - **Reset**
* - Reserved
  - 31:19
  - Reserved
  - R
  - 0
* - dqc
  - 18:16
  - DMA QoS control, see [](memory-map.md#quality-of-service)
  - R/W
  - 7
* - Reserved
  - 15:13
  - Reserved
  - R
  - 0
* - td
  - 12
  - Trace disable:
    - 0: enable trace
    - 1: disable trace
  - R/W
  - 0
* - elfd
  - 11
  - External load-to-load forwarding disable:
    - 0: enable external load-to-load forwarding
    - 1: disable external load-to-load forwarding
  - R/W
  - 0
* - Reserved
  - 10:9
  - Reserved
  - R
  - 0
* - cecd
  - 8
  - Core ECC check disable:
    - 0: ICCM/DCCM ECC checking enabled
    - 1: ICCM/DCCM ECC checking disabled
  - R/W
  - 0
* - Reserved
  - 7
  - Reserved
  - R
  - 0
* - sepd
  - 6
  - Side effect pipelining disable:
    - 0: side effect loads/stores are pipelined
    - 1: side effect loads/stores block all subsequent bus transactions until load/store response with default value received.

      **Note**: Reset value depends on selected bus core build argument
  - R/W
  - 0 (*AHB-Lite*) / 1 (*AXI4*)
* - Reserved
  - 5:4
  - Reserved
  - R
  - 0
* - bpd
  - 3
  - Branch prediction disable:
    - 0: enable branch prediction and return address stack
    - 1: disable branch prediction and return address stack
  - R/W
  - 0
* - wbcd
  - 2
  - Write Buffer (WB) coalescing disable:
    - 0: enable Write Buffer coalescing
    - 1: disable Write Buffer coalescing
  - R/W
  - 0
* - Reserved
  - 1
  - Reserved
  - R
  - 0
* - pd
  - 0
  - Pipelining disable:
    - 0: pipelined execution
    - 1: single instruction execution
  - R/W
  - 0
:::

### Clock Gating Control Register (mcgc)

The `mcgc` register hosts low-level core control bits to override clock gating for specific units.
This may be useful in case a unit intended to be clock gated should prove to have problems when in lower power mode.

:::{note}
Except for PIC I/O, the default state of the clock gating overrides is 'disabled'.
Firmware may turn off clock gating (i.e., set the clock gating override bit) for a specific unit if needed.
:::

This register is mapped to the non-standard read/write CSR address space.

:::{list-table} Clock Gating Control Register (mcgc, at CSR 0x7F8). Field Bits Description
:name: tab-clock-gating-cr
:header-rows: 1

* - **Field**
  - **Bits**
  - **Description**
  - **Access**
  - **Reset**
* - Reserved
  - 31:10
  - Reserved
  - R
  - 0
* - picio
  - 9
  - PIC I/O clock gating override:
    - 0: enable clock gating
    - 1: clock gating override
  - R/W
  - 1
* - misc
  - 8
  - Miscellaneous clock gating override:
    - 0: enable clock gating
    - 1: clock gating override
  - R/W
  - 0
* - dec
  - 7
  - DEC clock gating override:
    - 0: enable clock gating
    - 1: clock gating override
  - R/W
  - 0
* - exu
  - 6
  - EXU clock gating override:
    - 0: enable clock gating
    - 1: clock gating override
  - R/W
  - 0
* - ifu
  - 5
  - IFU clock gating override:
    - 0: enable clock gating
    - 1: clock gating override
  - R/W
  - 0
* - lsu
  - 4
  - LSU clock gating override:
    - 0: enable clock gating
    - 1: clock gating override
  - R/W
  - 0
* - bus
  - 3
  - Bus clock gating override:
    - 0: enable clock gating
    - 1: clock gating override
  - R/W
  - 0
* - pic
  - 2
  - PIC clock gating override:
    - 0: enable clock gating
    - 1: clock gating override
  - R/W
  - 0
* - dccm
  - 1
  - DCCM clock gating override:
    - 0: enable clock gating
    - 1: clock gating override
  - R/W
  - 0
* - iccm
  - 0
  - ICCM clock gating override:
    - 0: enable clock gating
    - 1: clock gating override
  - R/W
  - 0
:::
