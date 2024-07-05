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
    li x2, 0x5f555555
    csrw 0x7c0, x2

    // Set up MTVEC at _handler address
    la x2, _handler
    csrw mtvec, x2

    // Set up NMI handler at _handler address
    li x3, TEST_CMD
    ori x2, x2, LOAD_NMI_ADDR
    sw x2, 0(x3)

    j main


dbus_store_error:
    # li x1, 0xe0000000
    # jalr x0, x1, 0

    # li x1, 0xfffffffc
    # lw x3, 0(x1)

    la x31, fail
    // load expected mcause and mscause values for exception handler
    li x4, 0xF0000000   // mcause
    li x5, 0x0          // mscause
    // address of some data that resides in memory (and not in iccm/dccm)
    lw x6, _start
    // trigger bus fault at next store
    li x2, TRIGGER_BUS_FAULT
    li x3, TEST_CMD
    sw x2, 0(x3)
    // bus fault is triggered on this instruction
    sw x2, 0(x6)
    j fail_if_not_serviced

dbus_nonblocking_load_error:
    la x31, fail
    // load expected mcause and mscause values for exception handler
    li x4, 0xF0000001   // mcause
    li x5, 0x0          // mscause
    // trigger bus fault at next load
    li x2, TRIGGER_BUS_FAULT
    li x3, TEST_CMD
    sw x2, 0(x3)
    // bus fault is triggered on this instruction
    lw x2, 0(zero)
    j fail_if_not_serviced

main:
    call dbus_store_error
    call dbus_nonblocking_load_error

// Write 0xff to STDOUT for TB to terminate test.
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
    // reenable signaling of NMIs for subsequent NMIs
    csrw 0xBC0, x0 // mdeau
    csrr x2, mcause
    bne x2, x4, fail
    csrr x2, 0x7FF // mscause
    bne x2, x5, fail
    la x31, ok
    mret

// used for making sure we fail if we didn't jump to the exception/NMI handler
fail_if_not_serviced:
.rept 10
    nop
.endr
    // control flow goes to 'fail' if interrupt wasn't serviced (x31 set by the handler)
    // or goes to 'ok' and returns to the calling function
    jr x31

fail:
    // write 0x01 to STDOUT for TB to fail the test
    li x3, STDOUT
    addi x5, x0, 0x01
    sb x5, 0(x3)
    j fail

ok:
    ret
