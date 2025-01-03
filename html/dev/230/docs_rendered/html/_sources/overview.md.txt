# Core Overview

This chapter provides a high-level overview of the VeeR EL2 core and core complex. VeeR EL2 is a machinemode (M-mode) only, 32-bit CPU small core which supports RISC-V's integer (I), compressed instruction (C), multiplication and division (M), and instruction-fetch fence, CSR, and subset of bit manipulation instructions (Z) extensions. The core contains a 4-stage, scalar, in-order pipeline.

## Features

The VeeR EL2 core complex's feature set includes:
- RV32IMC-compliant RISC-V core with branch predictor
- Optional instruction and data closely-coupled memories with ECC protection (load-to-use latency of 1 cycle for smaller and 2 cycles for larger memories)
- Optional 2- or 4-way set-associative instruction cache with parity or ECC protection (32- or 64-byte line size)
- Optional programmable interrupt controller supporting up to 255 external interrupts
- Four system bus interfaces for instruction fetch, data accesses, debug accesses, and external DMA accesses to closely-coupled memories (configurable as 64-bit AXI4 or AHB-Lite)
- Core debug unit compliant with the RISC-V Debug specification [[3]](intro.md#ref-3)
- 600MHz target frequency (for 16nm technology node)

## Core Complex

{numref}`fig-core-complex` depicts the core complex and its functional blocks which are described further in section [](overview.md#functional-blocks).

:::{figure-md} fig-core-complex
![VeeR Core Complex](img/core_complex.png)

VeeR Core Complex
:::

## Functional Blocks

The VeeR EL2 core complex's functional blocks are described in the following sections in more detail.

### Core

{numref}`fig-core-pipeline` depicts the scalar 4-stage core with one execution pipeline, one load/store pipeline, one multiplier pipeline, and one out-of-pipeline divider. There are two stall points in the pipeline: 'Fetch' and 'Decode'. The diagram also shows how VeeR EH1's logic stages have been shifted up and merged into 4 stages named Fetch (F), Decode (D), Execute/Memory (X/M), and Retire (R). Also shown is additional logic such as a new branch adder in the D stage. The branch mispredict penalty is either 1 or 2 cycles in VeeR EL2.

The merged F stage performs the program counter calculation and the I-cache/ICCM memory access in parallel. The load pipeline has been moved up so that the DC1 memory address generation (AGU) logic is now combined with align and decode logic to enable a DCCM memory access to start at the beginning of the M stage. The design supports a load-to-use of 1 cycle for smaller memories and a load-to-use of 2 cycles for larger memories. For 1-cycle load-to-use, the memory is accessed and the load data aligned and formatted for the register file and forwarding paths, all in the single-cycle M stage. For 2-cycle load-to-use, almost the entire M stage is allocated to the memory access, and the DC3/DC4 logic combined into the R stage is used to perform the load align and formatting for the register file and forwarding paths. EX3 and EX4/WB are combined into the R stage and primarily used for commit and writeback to update the architectural registers.

:::{figure-md} fig-core-pipeline
![VeeR EL2 Core Pipeline](img/core_pipeline.png)

VeeR EL2 Core Pipeline
:::

## Standard Extensions

The VeeR EL2 core implements the following RISC-V standard extensions:

:::{list-table} VeeR EL2's RISC-V Standard Extensions
:name: tab-riscv-std-ext
:header-rows: 1

* - Extension
  - Description
  - References
* - M
  - Integer multiplication and division
  - Chapter 7 in [[1]](intro.md#ref-1)
* - C
  - Compressed instructions
  - Chapter 16 in [[1]](intro.md#ref-1)
* - Zicsr
  - Control and status register (CSR) instructions
  - Chapter 9 in [[1]](intro.md#ref-1)
* - Zifencei
  - Instruction-fetch fence
  - Chapter 3 in [[1]](intro.md#ref-1)
* - Zba [^fn-standard-extensions-1] (address calculation) (frozen)
  - Bit manipulation instructions
  - Chapter 2 in [[4]](intro.md#ref-4)
* - Zbb [^fn-standard-extensions-2] (base) (frozen)
  - Bit manipulation instructions
  - Chapter 2 in [[4]](intro.md#ref-4)
* - Zbc [^fn-standard-extensions-3] (carry-less multiply) (frozen)
  - Bit manipulation instructions
  - Chapter 2 in [[4]](intro.md#ref-4)
* - Zbs [^fn-standard-extensions-4] (single-bit) (frozen)
  - Bit manipulation instructions
  - Chapter 2 in [[4]](intro.md#ref-4)
* - Zbe [^fn-standard-extensions-5] (bit compress/ decompress) (stable)
  - Bit manipulation instructions
  - Chapter 2 in [[4]](intro.md#ref-4)
* - Zbf [^fn-standard-extensions-6] (bit-field place) (stable)
  - Bit manipulation instructions
  - Chapter 2 in [[4]](intro.md#ref-4)
* - Zbp [^fn-standard-extensions-7] (bit permutation) (stable)
  - Bit manipulation instructions
  - Chapter 2 in [[4]](intro.md#ref-4)
* - Zbr [^fn-standard-extensions-8] (CRC) (stable)
  - Bit manipulation instructions
  - Chapter 2 in [[4]](intro.md#ref-4)
:::

* `frozen` specified means that the extensions are not expected to change.
* `stable` mean that the marked extension may still change.

[^fn-standard-extensions-1]: List of Zba instructions (as of 1/20/21, "frozen"): sh1add, sh2add, sh3add
[^fn-standard-extensions-2]: List of Zbb instructions (as of 1/20/21, "frozen"): clz, ctz, cpop, min, minu, max, maxu, sext.b, sext.h, zext.h, andn, orn, xnor, rol, ror, rori, rev8, orc.b
[^fn-standard-extensions-3]: List of Zbc instructions (as of 1/20/21, "frozen"): clmul, clmulh, clmulr
[^fn-standard-extensions-4]: List of Zbs instructions (as of 1/20/21, "frozen"): bset, bseti, bclr, bclri, binv, binvi, bext, bexti
[^fn-standard-extensions-5]: List of Zbe instructions (as of 1/20/21, "stable"): bcompress, bdecompress, pack, packh
[^fn-standard-extensions-6]: List of Zbf instructions (as of 1/20/21, "stable"): bfp, pack, packh
[^fn-standard-extensions-7]: List of Zbp instructions (as of 1/20/21, "stable"): andn, orn, xnor, pack, packu, packh, rol, ror, rori, grev, grevi, gorc, gorci, shfl, shfli, unshfl, unshfli, xperm.n, xperm.b, xperm.h
[^fn-standard-extensions-8]: List of Zbr instructions (as of 1/20/21, "stable"): crc32.b, crc32c.b, crc32.h, crc32c.h, crc32.w, crc32c.w
