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

// Tested exceptions as per the table 2-10 in VeeR programmer's manual:
// - I-side fetch precise bus error
// - I-side core-local unmapped address error
// - Illegal instruction
// - ebreak (not to Debug Mode)
// - Trigger hit (not to Debug Mode)
// - D-side load across region boundary
// - D-side size-misaligned load to non-idempotent address
// - D-side core-local load unmapped address error
// - D-side load region prediction error
// - D-side PIC load access error
// - D-side store across region boundary
// - D-side size-misaligned store to non-idempotent address
// - D-side core-local store unmapped address error
// - D-side store region prediction error
// - D-side PIC store access error
// - Environment call from M-mode
// 
// Tested interrupts:
// - Machine software interrupt
// - Machine timer interrupt
// - Machine external interrupt
// - Machine internal timer 1 local interrupt
// - Machine internal timer 0 local interrupt
// - NMI pin assertion
// - D-bus store error
// - D-bus non-blocking load error
// - Fast Interrupt DCCM region access error
// - Fast Interrupt non-DCCM region

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
    // ibus fault is triggered on subsequent instruction - force refetch from memory
    // since testbench relies on bus transaction happening to trigger bus error
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

dside_load_across_region_boundary:
    la x31, fail
    li x4, 0x4
    li x5, 0x2
    // load from across region boundary
    li x2, 0xe0000000-2
    lw x2, 0(x2)
    j fail_if_not_serviced

dside_size_misaligned_load_to_non_idempotent_address:
    la x31, fail
    li x4, 0x4
    li x5, 0x1
    // load from across non-idempotent address (with side effects)
    // we take advantage of the fact that STDOUT is such an address
    li x2, STDOUT-2
    lw x2, 0(x2)
    j fail_if_not_serviced

dside_store_across_region_boundary:
    la x31, fail
    li x4, 0x6
    li x5, 0x2
    // store across region boundary
    li x2, 0xe0000000-2
    sw x2, 0(x2)
    j fail_if_not_serviced

dside_size_misaligned_store_to_non_idempotent_address:
    la x31, fail
    li x4, 0x6
    li x5, 0x1
    // store to across non-idempotent address (with side effect)
    // we take advantage of the fact that STDOUT is such an address
    li x2, STDOUT-2
    sw x2, 0(x2)
    j fail_if_not_serviced

dside_core_local_store_unmapped_address_error:
    la x31, fail
    li x4, 0x7
    li x5, 0x2
    // store to DCCM upper boundary (this also triggers unmapped address error)
    li x2, RV_DCCM_EADR - 1
    sw x2, 0(x2)
    j fail_if_not_serviced

dside_core_local_load_unmapped_address_error:
    la x31, fail
    li x4, 0x5
    li x5, 0x2
    // load from DCCM upper boundary (this also triggers unmapped address error)
    li x2, RV_DCCM_EADR - 1
    lw x2, 0(x2)
    j fail_if_not_serviced

dside_pic_load_access_error:
    la x31, fail
    li x4, 0x5
    li x5, 0x6
    // perform not word-sized load from PIC
    li x2, RV_PIC_BASE_ADDR
    lb x2, 0(x2)
    j fail_if_not_serviced

dside_pic_store_access_error:
    la x31, fail
    li x4, 0x7
    li x5, 0x6
    // perform not word-sized store to PIC
    li x2, RV_PIC_BASE_ADDR
    sb x2, 0(x2)
    j fail_if_not_serviced

dside_load_region_prediction_error:
    la x31, fail
    li x4, 0x5
    li x5, 0x5
    // this assumes that RV_PIC_BASE_ADDR is as high in the region
    // as realistically allowed, e.g. 0xffff8000, this allows us
    // to construct an address that will overflow to another region
    // when offset is used in an 'lw' instruction: 0xfffffffc + 0x4
    li x2, RV_PIC_BASE_ADDR + 0x7ffc
    lw x2, 0x4(x2)
    j fail_if_not_serviced

dside_store_region_prediction_error:
    la x31, fail
    li x4, 0x7
    li x5, 0x5
    // same as in load region prediction error
    li x2, RV_PIC_BASE_ADDR + 0x7ffc
    sw x2, 0x4(x2)
    j fail_if_not_serviced

machine_internal_timer0_local_interrupt:
    la x31, fail
    li x4, 0x8000001d
    li x5, 0x0
    csrw 0x7D4, 0x0 // disable incrementing timer0
    csrw 0x7D2, 0x0 // reset timer0 count value
    csrw 0x7D3, 0x8 // set timer0 threshold to 8
    li x2, 0x20000000
    csrw mie, x2    // enable timer0 local interrupt
    csrw 0x7D4, 0x1 // reenable incrementing timer0
    j fail_if_not_serviced

machine_internal_timer1_local_interrupt:
    la x31, fail
    li x4, 0x8000001c
    li x5, 0x0
    csrw 0x7D7, 0x0 // disable incrementing timer0
    csrw 0x7D5, 0x0 // reset timer0 count value
    csrw 0x7D6, 0x8 // set timer0 threshold to 8
    li x2, 0x10000000
    csrw mie, x2    // enable timer0 local interrupt
    csrw 0x7D7, 0x1 // reenable incrementing timer0
    j fail_if_not_serviced

illegal_instruction:
    la x31, fail
    li x4, 0x2
    li x5, 0x0
    .word 0
    j fail_if_not_serviced

breakpoint_ebreak:
    la x31, fail
    li x4, 0x3
    li x5, 0x2
    ebreak
    j fail_if_not_serviced

environment_call_from_m_mode:
    la x31, fail
    li x4, 0xB
    li x5, 0x0
    ecall
    j fail_if_not_serviced

nmi_pin_assertion:
    la x31, fail
    li x4, 0x0
    li x5, 0x0 
    // trigger NMI
    li x2, TRIGGER_NMI
    li x3, STDOUT
    sw x2, 0(x3)
    j fail_if_not_serviced

machine_software_interrupt:
    la x31, fail
    la x4, 0x80000003
    li x5, 0x0
    // enable software interrupt
    li x2, 0x8
    csrw mie, x2
    // trigger soft interrupt
    li x2, TRIGGER_SOFT_INT
    li x3, STDOUT
    sw x2, 0(x3)
    j fail_if_not_serviced

machine_timer_interrupt:
    la x31, fail
    la x4, 0x80000007
    li x5, 0x0
    // enable machine timer interrupt
    li x2, 0x80
    csrw mie, x2
    // trigger timer interrupt
    li x2, TRIGGER_TIMER_INT
    li x3, STDOUT
    sw x2, 0(x3)
    j fail_if_not_serviced

enable_ext_int1:
    // set up gateway configuration - level triggered active high
    li x2, 0x0
    li x3, (RV_PIC_BASE_ADDR + 0x4004)  // meigwctrl1
    sw x2, 0(x3)
    // clear interrupt bit for gateway
    li x3, (RV_PIC_BASE_ADDR + 0x5004)  // meigwclr1
    sw zero, 0(x3)
    // set up priority level
    li x3, (RV_PIC_BASE_ADDR + 0x4) // meipl1
    li x2, 0x1
    sw x2, 0(x3)

    // interrupt priority threshold and priority nesting are
    // already initialized at correct value and we're only
    // testing one interrupt so we don't bother setting them explicitly

    // enable external interrupt 1
    li x3, (RV_PIC_BASE_ADDR + 0x2004)
    li x2, 0x1
    sw x2, 0(x3)
    // enable external interrupts
    li x2, 0x800
    csrw mie, x2
    ret

machine_external_interrupt:
    la x31, fail
    la x4, 0x8000000b
    la x5, 0x0
    // Set up external interrupt vector table at the beginning of DCCM
    la x2, dbus_exc_handler
    li x3, RV_DCCM_SADR
    sw x2, 0(x3)
    // set up base interrupt vector table address
    csrw 0xBC8, x3  // meivt

    mv x6, x1 // save return address
    call enable_ext_int1
    mv x1, x6 // restore return address

    li x2, TRIGGER_EXT_INT1
    li x3, STDOUT
    sw x2, 0(x3)
    j fail_if_not_serviced

fast_interrupt_dccm_region_access_error:
    la x31, fail
    la x4, 0xF0001001
    la x5, 0x0
    // set up base interrupt vector table address at some address
    // *not* in DCCM but in DCCM region
    // assume somewhat optimistically that DCCM isn't allocated
    // at the end of its region so RV_DCCM_EADR + 1 is still in DCCM region
    li x2, RV_DCCM_EADR + 1
    csrw 0xBC8, x2  // meivt

    mv x6, x1 // save return address
    call enable_ext_int1
    mv x1, x6 // restore return address

    // trigger external interrupt 1
    li x2, TRIGGER_EXT_INT1
    li x3, STDOUT
    sw x2, 0(x3)
    j fail_if_not_serviced

fast_interrupt_non_dccm_region:
    la x31, fail
    la x4, 0xF0001002
    la x5, 0x0
    // set up interrupt vector table address at an address that's
    // not in DCCM region
    li x2, ((RV_DCCM_REGION + 1) % 0x10) << 28
    csrw 0xBC8, x2  // meivt

    mv x6, x1 // save return address
    call enable_ext_int1
    mv x1, x6 // restore return address

    // trigger external interrupt 1
    li x2, TRIGGER_EXT_INT1
    li x3, STDOUT
    sw x2, 0(x3)
    j fail_if_not_serviced

trigger_hit:
    la x31, fail
    la x4, 0x3
    la x5, 0x1
    // set up address to trigger on
    li x2, 0xdeadbeef
    csrw tdata2, x2
    // enable trigger in M-mode, fire on address of a load
    li x3, 0x41
    csrw mcontrol, x3
    // load from that address
    lw x2, 0(x2)
    j fail_if_not_serviced

main:
    // global interrupt enable
    csrr x2, mstatus
    ori x2, x2, 0x8
    csrw mstatus, x2

    // fetch can only trigger regular exceptions so it suffices to set up mtvec
    la x2, ibus_exc_handler
    csrw mtvec, x2

    call iside_core_local_unmapped_address_error
    call iside_fetch_precise_bus_error
    call illegal_instruction
    call breakpoint_ebreak
    call environment_call_from_m_mode

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
    call dside_size_misaligned_load_to_non_idempotent_address
    call dside_store_across_region_boundary
    call dside_size_misaligned_store_to_non_idempotent_address
    call dside_core_local_store_unmapped_address_error
    call dside_core_local_load_unmapped_address_error
    call dside_pic_load_access_error
    call dside_pic_store_access_error
    call dside_load_region_prediction_error
    call dside_store_region_prediction_error
    call machine_internal_timer0_local_interrupt
    call machine_internal_timer1_local_interrupt
    call nmi_pin_assertion
    call machine_software_interrupt
    call machine_timer_interrupt
    call machine_external_interrupt
    call fast_interrupt_dccm_region_access_error
    call fast_interrupt_non_dccm_region
    call trigger_hit

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
    // instruction/fetch related exceptions would return back to the faulting
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
    // disable all interrupt sources
    csrw mie, zero
    // reenable signaling of NMIs for subsequent NMIs
    csrw 0xBC0, zero // mdeau
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
