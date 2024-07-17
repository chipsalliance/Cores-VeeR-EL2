# 20 User Mode

By default VeeR EL2 Core is configured in machine mode only, so to enable user mode, set the *-set* option of [the config script](../../configs/veer.config):

```
veer.config -set=user_mode=1
```

When the flag is set, macro *RV_USER_MODE* is defined.
All user mode related code is guarded by the *ifdef RV_USER_MODE* / *endif* blocks.

## Machine ISA Register (misa)

Read-only register *misa* provides information about features and instruction sets supported by the core.
In user mode configuration, the U bit (20) is set.

## Machine Status Register (mstatus)

Register *mstatus* is extended with fields:
- *MPP* - 2-bit wide field - stores the previous core operating mode after entering an exception handler. It is implemented with a single FF (permissible if supervisor mode is not present in the design). The FF stores inverted value, so that upon core reset the field indicates machine mode (*2'b11*)
- *MPEV* - allows temporarily changing the effective privilege mode for load and store instructions

## Machine Environment Configuration Registers (menvcfg,menvcfgh)

Registers *menvcfg* and *menvcfgh* control the behavior of *FENCE* instruction flavors and contain bits relevant to the Sstc, Zicboz and Zicbom extensions.
None of these extensions are supported by the VeeR EL2 core and the core is in-order, so this register pair is read-only and all-zero.

## User Mode Performance Counters (cycle, cycleh, instret, instreth)

In order to enable performance monitoring in user mode, unprivileged shadow copies of *mcycle* and *minstret* registers are implemented: *cycle* and *instret*.
These are read-only registers accessible from the user mode.
Access to the shadow copies can be restricted by the *mcounteren* CSR.
Registers *cycleh* and *instreth* are upper 32-bits of the *cycle* and *instret* registers, respectively.

## Machine Counter-Enable Register (mcounteren)

Register *mcounteren* controls access to the user mode shadow copies of the performance counters.
Only software running in machine mode can change *mcounteren* register, so that it can grant/deny permission to specific counters for the user mode applications.

## Machine Security Configuration Register (mseccfg, mseccfgh)

Registers *mseccfg* and *mseccfgh* control PMP's behavior when Smepmp is enabled. The *RLB*, *MMWP* and *MML* bits are implemented, whereas others are read-only zero.

## Privilege Mode Transitions and Exception Handling

The VeeR EL2 core implements machine and user mode, so only 2 mode transitions are possible:
- When *mret* is executed, the operating mode is changed to the value of the *mstatus.MPP* field.
- When an exception is entered, core enters the machine mode.

When the core enters a trap, core immediately switches mode to machine and the pipeline is flushed.

The introduction of user mode adds 2 new *mcause* codes for a trap caused by the *ECALL* instruction:
- 11 (0xb) for *ECALL.M*, if ECALL is executed in machine mode
- 8 (0x8) for *ECALL.U*, if ECALL is executed in user mode

## PMP Enhancements for Memory Access and Execution Prevention on Machine Mode

The [PMP Enhancements for memory access and execution prevention on Machine mode (Smepmp)](https://github.com/riscvarchive/riscv-tee/blob/main/Smepmp/Smepmp.pdf) document defines an extension to PMP's behavior.

The Smepmp (extended PMP) support is enabled with the *-set=smepmp=1* option:

```
veer.config -set=user_mode=1 -set=smepmp=1
```

When the flag is set, macro *RV_SMEPMP* is defined.
Smepmp extension can only be used together with the user mode configuration.


