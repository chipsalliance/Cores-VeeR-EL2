# 1 VeeR EL2 Core Overview

This chapter provides a high-level overview of the VeeR EL2 core and core complex. VeeR EL2 is a machinemode (M-mode) only, 32-bit CPU small core which supports RISC-V's integer (I), compressed instruction \(C\), multiplication and division (M), and instruction-fetch fence, CSR, and subset of bit manipulation instructions (Z) extensions. The core contains a 4-stage, scalar, in-order pipeline.

## 1.1 Features

The VeeR EL2 core complex's feature set includes:

- RV32IMC-compliant RISC-V core with branch predictor

- Optional instruction and data closely-coupled memories with ECC protection (load-to-use latency of 1 cycle for smaller and 2 cycles for larger memories)

- Optional 2- or 4-way set-associative instruction cache with parity or ECC protection (32- or 64-byte line size)

- Optional programmable interrupt controller supporting up to 255 external interrupts

- Four system bus interfaces for instruction fetch, data accesses, debug accesses, and external DMA accesses to closely-coupled memories (configurable as 64-bit AXI4 or AHB-Lite)

- Core debug unit compliant with the RISC-V Debug specification [3]

- 600MHz target frequency (for 16nm technology node)

## 1.2 Core Complex

Figure 1-1 depicts the core complex and its functional blocks which are described further in Section 1.3.

:::{figure-md}
![VeeR Core Complex](img/core_complex.png)

Figure 1-1 VeeR Core Complex
:::

## 1.3 Functional Blocks

The VeeR EL2 core complex's functional blocks are described in the following sections in more detail.

### 1.3.1 Core

Figure 1-2 depicts the scalar 4-stage core with one execution pipeline, one load/store pipeline, one multiplier pipeline, and one out-of-pipeline divider. There are two stall points in the pipeline: 'Fetch' and 'Decode'. The diagram also shows how VeeR EH1's logic stages have been shifted up and merged into 4 stages named Fetch (F), Decode (D), Execute/Memory (X/M), and Retire (R). Also shown is additional logic such as a new branch adder in the D stage. The branch mispredict penalty is either 1 or 2 cycles in VeeR EL2.

The merged F stage performs the program counter calculation and the I-cache/ICCM memory access in parallel. The load pipeline has been moved up so that the DC1 memory address generation (AGU) logic is now combined with align and decode logic to enable a DCCM memory access to start at the beginning of the M stage. The design supports a load-to-use of 1 cycle for smaller memories and a load-to-use of 2 cycles for larger memories. For 1-cycle load-to-use, the memory is accessed and the load data aligned and formatted for the register file and forwarding paths, all in the single-cycle M stage. For 2-cycle load-to-use, almost the entire M stage is allocated to the memory access, and the DC3/DC4 logic combined into the R stage is used to perform the load align and formatting for the register file and forwarding paths. EX3 and EX4/WB are combined into the R stage and primarily used for commit and writeback to update the architectural registers.

:::{figure-md}
![VeeR EL2 Core Pipeline](img/core_pipeline.png)

Figure 1-2 VeeR EL2 Core Pipeline
:::

## 1.4 Standard Extensions

The VeeR EL2 core implements the following RISC-V standard extensions:

:::{table} Table 1-1 VeeR EL2's RISC-V Standard Extensions

| Extension Description                                                                                                                                                                                          | References                                     |                   |
|-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|------------------------------------------------|-------------------|
|M                                                                                                                                                                                                                                                               | Integer multiplication and division            | Chapter 7 in [1]  |
| C                                                                                                                                                                                                                                                               | Compressed instructions                        | Chapter 16 in [1] |
| Zicsr                                                                                                                                                                                                                                                           | Control and status register (CSR) instructions | Chapter 9 in [1]  |
| Zifencei                                                                                                                                                                                                                                                        | Instruction-fetch fence                        | Chapter 3 in [1]  |
| - Zba1 (address  calculation) (frozen) | Bit manipulation instructions                  | Chapter 2 in [4]  |
| - Zbb2 (base) (frozen) | Bit manipulation instructions                  | Chapter 2 in [4]  |
| - Zbc3 (carry-less  multiply) (frozen) | Bit manipulation instructions                  | Chapter 2 in [4]  |
| - Zbs4 (single-bit) (frozen) | Bit manipulation instructions                  | Chapter 2 in [4]  |
| - Zbe5 (bit  compress/  decompress) (stable) | Bit manipulation instructions                  | Chapter 2 in [4]  |
| - Zbf6 (bit-field  place) (stable) | Bit manipulation instructions                  | Chapter 2 in [4]  |
| - Zbp7 (bit  permutation) (stable) | Bit manipulation instructions                  | Chapter 2 in [4]  |
| - Zbr8 (CRC)  (stable) | Bit manipulation instructions                  | Chapter 2 in [4]  |
:::

* `frozen` specified means that the extensions are not expected to change.
* `stable` mean that the marked extension may still change.

1. List of Zba instructions (as of 1/20/21, "frozen"): sh1add, sh2add, sh3add
2. List of Zbb instructions (as of 1/20/21, "frozen"): clz, ctz, cpop, min, minu, max, maxu, sext.b, sext.h, zext.h, andn, orn, xnor, rol, ror, rori, rev8, orc.b
3. List of Zbc instructions (as of 1/20/21, "frozen"): clmul, clmulh, clmulr
4. List of Zbs instructions (as of 1/20/21, "frozen"): bset, bseti, bclr, bclri, binv, binvi, bext, bexti
5. List of Zbe instructions (as of 1/20/21, "stable"): bcompress, bdecompress, pack, packh
6. List of Zbf instructions (as of 1/20/21, "stable"): bfp, pack, packh
7. List of Zbp instructions (as of 1/20/21, "stable"): andn, orn, xnor, pack, packu, packh, rol, ror, rori, grev, grevi, gorc, gorci, shfl, shfli, unshfl, unshfli, xperm.n, xperm.b, xperm.h
8. List of Zbr instructions (as of 1/20/21, "stable"): crc32.b, crc32c.b, crc32.h, crc32c.h, crc32.w, crc32c.w
