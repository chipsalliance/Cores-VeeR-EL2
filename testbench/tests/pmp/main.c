/* SPDX-License-Identifier: Apache-2.0
 * Copyright 2023 Antmicro, Ltd. <www.antmicro.com>
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <stdio.h>
#include <stdlib.h>
#include "veer.h"
#include "fault.h"
#include "pmp.h"

#define CSR_MSTATUS 0x300
#define CSR_MISA    0x301
#define CSR_MEPC    0x341

extern uint32_t _text;
extern uint32_t _text_end;
extern uint32_t _data;
extern uint32_t _data_end;
extern uint32_t _stack_lo;
extern uint32_t _stack_hi;
extern uint32_t tohost;

extern int ucall (void* ptr, ...);

// ============================================================================

volatile uint32_t test_area_1 [16] __attribute__((section(".area1")));
volatile uint32_t test_area_2 [16] __attribute__((section(".area2")));

void test_hello () {
    printf("hello\n");
}

void test_read () {
    printf("reading from area1...\n");

    volatile uint32_t arr[16];
    for (size_t i=0; i<16; ++i) {
        arr[i] = test_area_1[i];
    }
}

void test_write () {
    printf("writing to area1...\n");

    volatile uint32_t arr[16] = {0};
    for (size_t i=0; i<16; ++i) {
        test_area_1[i] = arr[i];
    }
}

void __attribute__((section(".area3"))) test_exec () {
    printf("hello from .area3\n");
}

// ============================================================================

volatile unsigned long trap_count = 0;

int trap_handler (const struct fault* fault) {
    printf("Trap! mcause=0x%08x, mepc=0x%08X\n", fault->mcause, fault->mepc);

    // Terminate the simulation if too many traps got triggered
    if (++trap_count > 50) {
        printf("Too many traps, aborting...\n");
        _exit(-1);
    }

    // If setjmp-based try-catch was used return to the program
    fault_return(fault);
    return 0;
}

// ============================================================================

int main () {
    printf("Hello VeeR (M mode)\n");

    struct pmp_entry_s entry;
    int res = 0;
    int tid = 0;

    // .......................................................................
    // Check if user mode has access to everything by default when PMP is not
    // configured. Just call a simple function.
    printf("%02d - User mode RWX in default state\n", tid++);

    pmp_clear();

    printf(" testing...\n");
    TRY {
        ucall(test_hello);
        printf(" pass\n");
    }
    CATCH {
        printf(" fail\n");
        res = -1;
    }
    END_TRY;

    // .......................................................................
    // Configure a single region in PMP and call user mode function. It shoud
    // not have access to code and stack hence it should not execute
    printf("%02d - User mode RWX with one (any) PMP region enabled\n", tid++);

    // Allow area1 user access
    entry.addr = (uint32_t)(&test_area_1) >> 2;
    entry.addr = (entry.addr & 0xFFFFFF00) | 0x0000007F; // NAPOT, 2^11
    entry.cfg  = PMP_NAPOT | PMP_R | PMP_W | PMP_X;
    pmp_entry_write(6, &entry);

    printf("testing...\n");
    TRY {
        ucall(test_hello);
        printf(" fail\n");
        res = -1;
    }
    CATCH {
        printf(" pass\n");
    }
    END_TRY;

    // .......................................................................
    // Configure PMP to allow user mode access to code and stack
    printf("%02d - User mode RWX with code, data and stack access allowed\n", tid++);

    // Allow user access to "tohost"
    entry.addr = (uint32_t)(&tohost) >> 2;
    entry.cfg  = PMP_NA4 | PMP_R | PMP_W | PMP_X;
    pmp_entry_write(0, &entry);

    // Allow user access to code
    entry.addr = (uint32_t)(&_text) >> 2;
    entry.cfg  = 0;
    pmp_entry_write(1, &entry);
    entry.addr = (uint32_t)(&_text_end) >> 2;
    entry.cfg  = PMP_TOR | PMP_R | PMP_X;
    pmp_entry_write(2, &entry);

    // Allow user access to data
    entry.addr = (uint32_t)(&_data) >> 2;
    entry.cfg  = 0;
    pmp_entry_write(3, &entry);
    entry.addr = (uint32_t)(&_data_end) >> 2;
    entry.cfg  = PMP_TOR | PMP_R | PMP_W;
    pmp_entry_write(4, &entry);

    // Allow user access to stack
    entry.addr = (uint32_t)(&STACK) >> 2;
    entry.addr = (entry.addr & 0xFFFFFF00) | 0x0000007F; // NAPOT, 2^11
    entry.cfg  = PMP_NAPOT | PMP_R | PMP_W;
    pmp_entry_write(5, &entry);

    printf("testing...\n");
    TRY {
        ucall(test_hello);
        printf(" pass\n");
    }
    CATCH {
        printf(" fail\n");
        res = -1;
    }
    END_TRY;

    // .......................................................................
    // 

    for (size_t i=0; i<8; ++i) {
        uint32_t r = (i & 1) ? PMP_R : 0;
        uint32_t w = (i & 2) ? PMP_W : 0;
        uint32_t x = (i & 4) ? PMP_X : 0;

        char pstr[4] = {
            r ? 'R' : '-',
            w ? 'W' : '-',
            x ? 'X' : '-',
            0x00
        };

        printf("%02d - User mode %s from designated areas\n", tid++, pstr);

        // Configure .area1 access
        entry.addr = (uint32_t)(&test_area_1) >> 2;
        entry.addr = (entry.addr & 0xFFFFFF00) | 0x0000007F; // NAPOT, 2^11
        entry.cfg  = PMP_NAPOT | r | w;
        pmp_entry_write(6, &entry);

        // Configure .area3 access
        entry.addr = (uint32_t)(&test_exec) >> 2;
        entry.addr = (entry.addr & 0xFFFFFF00) | 0x0000007F; // NAPOT, 2^11
        entry.cfg  = PMP_NAPOT | PMP_R | x;
        pmp_entry_write(7, &entry);

        printf("testing R...\n");
        TRY {
            ucall(test_read);
            if (r) {
                printf(" pass\n");
            } else {
                printf(" fail\n");
                res = -1;
            }
        }
        CATCH {
            if (r) {
                printf(" fail\n");
                res = -1;
            } else {
                printf(" pass\n");
            }
        }
        END_TRY;

        printf("testing W...\n");
        TRY {
            ucall(test_write);
            if (w) {
                printf(" pass\n");
            } else {
                printf(" fail\n");
                res = -1;
            }
        }
        CATCH {
            if (w) {
                printf(" fail\n");
                res = -1;
            } else {
                printf(" pass\n");
            }
        }
        END_TRY;

        printf("testing X...\n");
        TRY {
            ucall(test_exec);
            if (x) {
                printf(" pass\n");
            } else {
                printf(" fail\n");
                res = -1;
            }
        }
        CATCH {
            if (x) {
                printf(" fail\n");
                res = -1;
            } else {
                printf(" pass\n");
            }
        }
        END_TRY;
    }

    printf("Goodbye VeeR (M mode)\n");
    return res;
}

