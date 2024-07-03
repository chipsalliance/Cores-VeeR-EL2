// SPDX-License-Identifier: Apache-2.0
// Copyright 2019 Western Digital Corporation or its affiliates.
// Copyright (c) 2024 Antmicro <www.antmicro.com>
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

// Assembly code for testing instruction access faults


#include "defines.h"
#include "tb.h"


// Code to execute
.section .text
.global _start
_start:
    // Clear minstret
    csrw minstret, zero
    csrw minstreth, zero

    // Enable Caches in MRAC
    li x1, 0x5f555555
    csrw 0x7c0, x1

    // Set up MTVEC at _handler address
    la x1, _handler
    csrw mtvec, x1

    // Set up NMI handler at _handler address
    li x2, TEST_CMD
    ori x1, x1, LOAD_NMI_ADDR
    sw x1, 0(x2)

trigger_exc:
    # li x1, 0xe0000000
    # jalr x0, x1, 0

    # li x1, 0xfffffffc
    # lw x3, 0(x1)

    // trigger bus fault at next load
    li x1, TRIGGER_BUS_FAULT
    li x2, TEST_CMD
    sw x1, 0(x2)
    la x2, trigger_exc
    // bus fault is triggered on this instruction
    lw x1, 0(x2)
.rept 10
    nop
.endr
    // fail if we didn't service the interrupt
    j fail

// Write 0xff to STDOUT for TB to termiate test.
_finish:
    li x3, STDOUT
    addi x5, x0, 0xff
    sb x5, 0(x3)
    beq x0, x0, _finish
.rept 100
    nop
.endr

// NMI handler must be aligned to 256 bytes since it has to fit
// in the upper 24 bits of nmi handler address set command
.balign 256
_handler:
    csrr x7, mcause
    li x8, 0xF0000001
    bne x7, x8, fail
    csrr x7, 0x7FF // mscause
    bne x7, zero, fail
    j _finish

fail:
    li x3, STDOUT
    addi x5, x0, 0x01
    sb x5, 0(x3)
    j fail

.data
testdata:
    .word 0xdeadbeef