# Interrupt Priorities

{numref}`tab-veer-el2-platform-specific-and-std-risc-v-interrupt-priorities` summarizes the VeeR EL2 platform-specific (Local) and standard RISC-V (External, Software, and Timer) relative interrupt priorities.

:::{list-table} VeeR EL2 Platform-specific and Standard RISC-V Interrupt Priorities. Table is sorted from highest Interrupt priority to lowest Interrupt priority
:name: tab-veer-el2-platform-specific-and-std-risc-v-interrupt-priorities

* - **Interrupt**
  - **Section**
* - *Non-Maskable Interrupt (standard RISC-V)*
  - [](memory-map.md#non-maskable-interrupt-nmi-signal-and-vector)
* - *External interrupt (standard RISC-V)*
  - [](interrupts.md)
* - Correctable error (local interrupt)
  - [](memory-map.md#correctable-error-local-interrupt)
* - *Software interrupt (standard RISC-V)*
  - [](memory-map.md#software-interrupts)
* - *Timer interrupt (standard RISC-V)*
  - [](performance.md#standard-risc-v-registers)
* - Internal timer 0 (local interrupt)
  - [](timers.md#internal-timer-local-interrupts)
* - Internal timer 1 (local interrupt)
  - [](timers.md#internal-timer-local-interrupts)
:::
