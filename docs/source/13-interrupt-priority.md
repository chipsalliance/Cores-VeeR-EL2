# 13 Interrupt Priorities

Table 13-1 summarizes the VeeR EL2 platform-specific (Local) and standard RISC-V (External, Software, and Timer) relative interrupt priorities.

:::{table} Table 13-1 VeeR EL2 Platform-specific and Standard RISC-V Interrupt Priorities<br>Table is sorted from highest Interrupt priority to lowest Interrupt priority
|Interrupt|Section|
|---|---|
|Non-Maskable Interrupt (standard RISC-V)|2.16|
|External interrupt (standard RISC-V)|6|
|Correctable error (local interrupt)|2.7.2|
|Software interrupt (standard RISC-V)|2.17|
|Timer interrupt (standard RISC-V)|7.2.1|
|Internal timer 0 (local interrupt)|4.3|
:::
