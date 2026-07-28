# Triple Modular Redundancy (TMR)

This chapter describes the TMR feature of VeeR EL2 core.
When enabled, the top-level module instantiates 3 independent but synchronized VeeR cores along with majority voting, error detection and recovery logic.

```{note}
The following documentation describes planned TMR architecture and implementation which is subject to changes.
Also, at the moment the complete TMR functionality isn't implemented yet.
```

## Configuration

To enable the TMR feature pass the following options to the `veer.config` script:
```
-set=triple_modular_redundancy_enable=1
```

```{note}
Triple Modular Redundancy and Dual Core Lockstep configurations are mutually exclusive
```

## Architecture

Triple Modular Redundancy complex is a super set of the regular VeeR EL2 core.

:::{figure-md}
![tmr_mux.png](img/tmr_complex.png)

Block diagram of the TMR complex
:::

The TMR complex contains:
* 3 VeeR EL2 cores without integrated PIC
* PIC common for all the cores in the complex
* PIC TMR - interface voter that handles PIC and external interrupt buses
* IC TMR - interface voter that handles Instruction Cache bus
* Clock distribution module - gates and distributes clocks to the TMR complex logic and to the VeeR EL2 cores
* IO Adapter - handles selection between AXI and AHB external buses, it is not hardened
* AXI TMR - interface voter that handles IFU, LSU, SB and DMA AXI buses
* DCCM TMR - interface voter that handles DCCM bus
* ICCM TMR - interface voter that handles ICCM bus
* MISC TMR - interface voter which handles reset propagation, trace interface, timer/soft/NMI interrupts
* DMI/JTAG TMR - interface voter that handles JTAG bus, it also multiplexes between normal debug JTAG and failed core debug JTAG
* HATL/RUN TMR - interface voter that handles MPC and PMU buses, it is also used during recovery process
* Recovery FSM - handles system recovery in the TMR mode

## Boot configuration

VeeR in the TMR configuration allows for 3 modes of operation:
* no redundancy single core
* 0-delay dual core lockstep
* triple modular redundancy

To allow for boot time configuration special multiplexer are added before TMR voters.
:::{figure-md}
![tmr_mux.png](img/tmr_mux.png)

Block diagram of TMR multiplexing
:::

These modes can only be configured while the VeeR complex is in the reset.
This is achieved using external multi bit signals:
* `activate_core_0`
* `activate_core_1`
* `activate_core_2`

This signals control which core(s) will be brought from reset and have active clock tree.
They are internally latched in the TMR registers, and refreshed each cycle after reset is released.
TMR is used to guarantee that configuration bits are more resilient to the radiation and interference.
Following table describes which core, mode and mux configuration is active based on the `activate_core_x` signals.

:::{list-table} Execution Mode
* - **activate_core_0**
  - **activate_core_1**
  - **activate_core_2**
  - **MUX 0 source**
  - **MUX 1 source**
  - **MUX 2 source**
  - **Operating Mode**
  - **Active Core(s)**
* - True
  - True
  - True
  - core 0
  - core 1
  - core 2
  - TMR
  - 0, 1, 2
* - True
  - True
  - False
  - core 0
  - core 1
  - core 2
  - 0-delay DCLS
  - 0, 1
* - True
  - False
  - True
  - core 0
  - core 1
  - core 2
  - 0-delay DCLS
  - 0, 2
* - False
  - True
  - True
  - core 0
  - core 1
  - core 2
  - 0-delay DCLS
  - 1, 2
* - True
  - False
  - False
  - core 0
  - core 0
  - core 2
  - Single core
  - 0
* - False
  - True
  - False
  - core 0
  - core 1
  - core 1
  - Single core
  - 1
* - False
  - False
  - True
  - core 2
  - core 1
  - core 2
  - Single core
  - 2
* - False
  - False
  - False
  - core 0
  - core 1
  - core 2
  - Invalid
  - None
:::

### TMR Configuration
In the TMR mode all cores are active.
TMR muxes are configured to pass interface directly from the adjacent core.
TMR voter is actively monitoring all cores comparing their values
It is capable of reporting single (non-fatal errors) and all-core disagreement (fatal error).
Recovery module is configured to perform its duty when CPU context allows for it.
System is in the highest redundancy mode.

### DCLS Configuration
In the DCLS mode 2 out of 3 cores are active.
TMR muxes are configured to pass interface directly from the adjacent core.
TMR voter input from the inactive core is marked as if it had previously failed TMR voting.
It is only capable of reporting all-core disagreement (fatal error).
Recovery module is configured to remain inactive and not respond to error signals.
System is in the downgraded redundancy mode, any failures will result in the fatal error being raised.

### Single Core Configuration
In the single core mode only 1 out of 3 cores is active.
TMR muxes are configured so that active core(i) is routed to I(i) and I((i + 1) % 3) TMR inputs.
Rest of the complex is configured the same way as in the DCLS mode.
System has no redundancy and failures will not be caught.
