// SPDX-License-Identifier: Apache-2.0
// Copyright 2024 Antmicro <www.antmicro.com>
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

#include "defines.h"

#define STDOUT 0xd0580000

    .set    mfdc, 0x7f9
    .set    mrac, 0x7c0
// Code to execute
.section .text
.global _start
_start:
    // Enable Caches in MRAC
    li x1, 0x5f555555
    csrw    mrac, x1
    li  x3, 4
    csrw    mfdc, x3        // disable store merging

    li      t3,  0   // counter for the outer loop
    li      t5,  100 // limit the outer loop to 100 iterations
outer:
    beq t3, t5, report_success
    addi    t3, t3, 1
    li      t4, 123
inner:
    addi    t4, t4, -1
    bne     t4, zero, inner
    jal     x0, outer
report_success:
    // write 0xff to STDOUT to report success
    li      x3, STDOUT
    li      x2, 0xff
    sw      x2, 0(x3)
end:
    nop
    j end
.long   0,1,2,3,4
