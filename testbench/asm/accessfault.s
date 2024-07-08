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

    j main


dbus_store_error:
    la x31, fail
    // load expected mcause and mscause values for exception handler
    li x4, 0xF0000000   // mcause
    li x5, 0x0          // mscause
    // address of some data that resides in memory (and not in iccm/dccm)
    lw x6, _start
    // trigger bus fault at next store
    li x2, TRIGGER_DBUS_FAULT
    li x3, STDOUT
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
    li x2, TRIGGER_DBUS_FAULT
    li x3, STDOUT
    sw x2, 0(x3)
    // bus fault is triggered on this instruction
    lw x2, 0(zero)
    j fail_if_not_serviced

iside_fetch_precise_bus_error:
    la x31, fail
    li x4, 0x1
    li x5, 0x9
    li x2, TRIGGER_IBUS_FAULT
    li x3, STDOUT
    sw x2, 0(x3)
    // ibus fault is triggered on this instruction
    fence.i
    j fail_if_not_serviced

iside_core_local_unmapped_address_error:
    la x31, fail
    li x4, 0x1
    li x5, 0x2
    // jump to address that's only halfway inside ICCM
    li x2, 0xee000000-2
    jalr x2, 0(x2)
    j fail_if_not_serviced

main:
    // fetch can only trigger regular exceptions so it suffices to set up mtvec
    la x2, ibus_exc_handler
    csrw mtvec, x2

    call iside_core_local_unmapped_address_error
    call iside_fetch_precise_bus_error
    
    // dbus can trigger both NMIs and regular exceptions so we set up both mtvec and
    // set NMI handler address via testbench

    // set up mtvec
    la x2, dbus_exc_handler
    csrw mtvec, x2

    // Set up NMI handler address
    li x3, STDOUT
    ori x2, x2, LOAD_NMI_ADDR
    sw x2, 0(x3)

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

// exception handler must be aligned to 4-byte boundary
.balign 4
ibus_exc_handler:
    // fetch exceptions trigger functions would return back to the faulting
    // instruction on mret so we override the address to go to the nop sled instead
    la x2, ok
    csrw mepc, x2
    j handler_compare_csrs

// test whether the values in relevant csrs are as expected
handler_compare_csrs:
    csrr x2, mcause
    bne x2, x4, fail
    csrr x2, 0x7FF // mscause
    bne x2, x5, fail
    la x31, ok
    mret

// NMI handler must be aligned to 256 bytes since it has to fit
// in the upper 24 bits of nmi handler address set testbench command
.balign 256
dbus_exc_handler:
    // reenable signaling of NMIs for subsequent NMIs
    csrw 0xBC0, x0 // mdeau
    j handler_compare_csrs

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
