// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// 32-bit DMA write + read-back of ICCM.
//
// The LSU accesses below target RV_ICCM_SADR. They leave the core on the
// system bus and the testbench bridge (axi_lsu_dma_bridge.sv /
// ahb_lsu_dma_bridge.sv) loops them back into the DMA port, so both the store
// and the load are DMA accesses to ICCM.
//
// Each word is written with a 32-bit DMA store and read back with a 32-bit DMA
// load; the test fails if the read data differs or the load traps. An even and
// an odd word are checked, as they are held in different ICCM banks.

#include "defines.h"

#define STDOUT 0xd0580000

    .set    mfdc, 0x7f9

.section .text
.align 4
.global _start
_start:

    // Set trap handler. A DMA ECC error can come back as a load access fault.
    la   x1, _trap
    csrw mtvec, x1

    // Same region setup as hello_world_iccm.
    li   x1, 0x5f555555
    csrw 0x7c0, x1
    li   x3, 4
    csrw mfdc, x3           // disable store merging: keep accesses 32-bit

    li   x3, RV_ICCM_SADR

    // Even word.
    li   x6, 0xCAFEBACA
    sw   x6, 0(x3)          // 32-bit DMA write
    lw   x7, 0(x3)          // 32-bit DMA read
    bne  x6, x7, _fail

    // Odd word.
    li   x6, 0xDEADBEEF
    sw   x6, 4(x3)
    lw   x7, 4(x3)
    bne  x6, x7, _fail

    li   a0, 0xff           // success
    j    _finish

_fail:
    li   a0, 1              // failure

// Write return value (a0) to STDOUT for TB to terminate test.
_finish:
    li   x3, STDOUT
    sb   a0, 0(x3)
    beq  x0, x0, _finish
.rept 100
    nop
.endr

.align 4
_trap:
    li   a0, 1              // failure
    j    _finish
