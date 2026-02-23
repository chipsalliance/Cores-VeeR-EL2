# Physical Memory Protection

The Physical Memory Protection unit implemented in the VeeR EL2 Core is compliant with "Section 3.7 Physical Memory Protection" of [[5]](intro.md#ref-5).

RISC-V introduces additional regulatory documents regarding memory protection:

- [Supervisor mode PMP (SPMP)](https://github.com/riscv/riscv-spmp/blob/main/rv-spmp-spec.pdf)
- [PMP enhancements (Smepmp)](https://github.com/riscv/riscv-tee/blob/main/Smepmp/Smepmp.pdf)

## Theory of Operation

The PMP module adds a set of CSRs which define memory regions and Read/Write/Execute (RWX) access permissions.
For each memory access, the PMP module checks if accessed memory is on the allowlist.
In case of impermissible memory access, a precise exception is thrown and execution flow is switched to the trap handler.
The PMP distinguishes 3 types of memory accesses: instruction fetch, data load and data store.

## Physical Memory Protection CSRs

The `pmpcfgX` and `pmpaddrX` CSRs are implemented in the [*el2_dec_tlu_ctl* module](../../design/dec/el2_dec_tlu_ctl.sv).
CSR address decoding is generated from either [*csrdecode_m*](../../design/dec/csrdecode_m) (Machine mode) or [*csrdecode_mu*](../../design/dec/csrdecode_mu) (Machine and User mode) description file.

The number of `pmpcfgX` registers is always 4 times smaller than the number of PMP entries, which are configurable using the `-set=pmp_entires=N` option, where *N* can be 0, 16 or 64.

:::{list-table} CSR configurations for RV-32
:name: tab-riscv-pmp-csr-configuration-table
:header-rows: 1
:align: left
* - Number of PMP entries
  - Number of *pmpcfgX* CSRs
  - Number of *pmpaddrX* CSRs
* - 0
  - 0
  - 0
* - 16
  - 4
  - 16
* - 64
  - 16
  - 64
:::

### Configuration Registers (pmpcfgX)

Each `pmpcfgX` register holds a configuration for four PMP entries, with a byte used for each entry.

:::{list-table} Decoding of the *pmpcfgX* register
:name: tab-riscv-pmpcfgx-register
:header-rows: 1
:align: left
* - **Bit**
  - 7
  - 6
  - 5
  - 4
  - 3
  - 2
  - 1
  - 0
* - **Flag**
  - *L*
  - *0*
  - *0*
  - *A[1]*
  - *A[0]*
  - *X*
  - *W*
  - *R*
:::

Meaning of bit flags:
 - *L* - lock bit; when set to *1*, given entry cannot be changed (both configuration and address) until hart reset
 - *0* - unused bits, always set to *0*
 - *A[1:0]* - encodes address matching mode (*OFF*, *TOR*, *NA4*, *NAPOT*)
 - *X* - execute permission; when set to *1*, allows instruction fetch from the corresponding address region; otherwise memory access will result in an instruction access-fault exception
 - *W* - write permission; when set to *1*, allows data store to the corresponding address region; otherwise memory access will result in a store access-fault exception
 - *R* - read permission; when set to *1*, allows data load from the corresponding address region; otherwise memory access will result in a load access-fault exception.

### Address Registers (pmpaddrX)

PMP address registers (`pmpaddrX`) encode bits 33 to 2 (`address[33:2]`) in physical memory.
This address defines protected memory region boundaries, further interpreted according to address matching values encoded by bits 4 and 3 of the `pmpcfgX` register:

- *00* OFF Null region (disabled)
- *01* TOR Top of range
- *10* NA4 Naturally aligned four-byte region
- *11* NAPOT Naturally aligned power-of-two region, >=8 bytes

## Exceptions

In case of impermissible memory access, an exception is raised and the exception code is stored in the `mcause` CSR register (*0x342*).

:::{list-table} PMP related exception codes
:name: tab-riscv-pmp-exceptions
:header-rows: 1
:widths: 14 14 36
* - **Interrupt flag (*mcause[MXLEN-1]*)**
  - **Exception Code (*mcause[MXLEN-2:0]*)**
  - **Exception description**
* - *0*
  - *1*
  - Instruction access fault (cannot read instruction from protected region)
* - *0*
  - *5*
  - Load access fault (cannot load data from protected region)
* - *0*
  - *7*
  - Store/Atomic Memory Operation access fault (cannot store data to protected region)
:::

Whenever a PMP access fault exception is raised, the machine secondary cause register (`mscause`) value is *0x03* indicating "access out of MPU range".

## PMP module

The PMP module is implemented in [el2_pmp.sv](../../design/el2_pmp.sv).
It is meant to be connected to the:

- CSR configuration table
- CSR addresses table
- configuration inputs for each channel (marking permissions to be checked on a given channel)
- address inputs for each channel (one for IFU, one for LSU)
- error outputs for each channel

The following functionality has been implemented:

- decoding address ranges (start address and mask) from address CSRs depending on the address matching mode for a given entry
- comparing addresses coming from a channel to defined ranges
- asserting error flags for given channels depending on permissions from the first matching range.

Error handling is performed using existing logic in IFU and LSU modules, reusing previously implemented mechanisms.

:::{figure-md} riscv_pmp_block_diagram
![riscv_pmp_block_diagram](img/19-riscv_pmp_block_diagram.png)

PMP integration with other modules of the VeeR EL2 core.
:::

## Verification

The PMP module is tested with:

* [RTL tests](../../verification/block/pmp/testbench.py)
* [software smoke tests](../../testbench/tests/pmp/main.c)
* [RISC-V DV tests](../../.github/workflows/test-riscv-dv.yml)

## PMP check example

In this example we enforce the following permissions:

- *0x00000000* - *0x00000FFF* - deny reads, writes, execution
- *0x00001000* - *0x00001FFF* - allow reads, writes, execution

First, let's configure the 2 address regions by writing 2 bytes to the lower 16 bits of the `pmpcfg0` register (each region configuration uses a byte)
PMP configuration registers should be set to:

- `pmpcfg0[7:0]` = *0b00001000* - non-locked entry, top-of-range address matching, all memory access denied.
- `pmpcfg0[15:8]` = *0b00001111* - non-locked entry, top-of-range address matching, all memory access permitted.

To select top-of-range matching, bits 3 and 4 of the configuration field are set to *0b01*, which creates a region starting with the address from the previous entry `pmpaddrX-1` and ending at an address in the `pmpaddrX` register, decremented by one.
In case of the first entry on the list, the *0x00000000* address is used as boundary.

After selecting the addressing mode, we can calculate values of `pmpaddr0` and `pmpaddr1` registers, which will define boundaries of regions.
Addresses stored in `pmpaddrX` CSRs contain bits *[33:2]* of the memory address.
Thus to select a specific address, it must be shifted by 2 bits to the right before writing the value to the register:

* `pmpaddr0` should be `(0x00001000 >> 2) = 0x00000400`, so that it matches the memory region from *0x00000000* to *0x00000FFF*.
* `pmpaddr1` should be `(0x00002000 >> 2) = 0x00000800`, so that it matches the memory region from *0x00001000* (which is the top address of the previous entry) to *0x00001FFF*.

With this configuration, all memory accesses to the first region (*0x00000000* - *0x00000FFF*) will fail and trigger an exception.
The exception code can be read to determine the type of the failed operation (instruction fetch, data load or data store).
On the other hand, all memory accesses to the second region (*0x00001000* - *0x00001FFF*) will be executed without errors.
