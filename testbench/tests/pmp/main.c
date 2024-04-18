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

extern int ucall (void* ptr, ...);

// ============================================================================

volatile uint32_t test_area_1 [16] __attribute__((section(".area1")));
volatile uint32_t test_area_2 [16] __attribute__((section(".area2")));

void test_hello () {
    printf(" hello\n");
}

// ============================================================================

int trap_handler (const struct fault* fault) {
    printf("Trap! mcause=0x%08x\n", fault->mcause);

    // If setjmp-based try-catch was used return to the program
    fault_return(fault);
    return 0;
}

// ============================================================================

int main () {
    printf("Hello VeeR (M mode)\n");

    struct pmp_entry_s entry;
    int res = 0;

    // .......................................................................
    // Check if user mode has access to everything by default when PMP is not
    // configured. Just call a simple function.

    TRY {
        ucall(test_hello);
        printf(" pass\n");
    }
    CATCH {
        printf(" fail\n");
        res = 1;
    }
    END_TRY;

    // .......................................................................
    // Configure a single region in PMP and call user mode function. It shoud
    // not have access to code and stack hence it should not execute

    // Allow area1 user access
    entry.addr = (uint32_t)(&test_area_1);
    entry.addr = (entry.addr & 0xFFFFFF00) | 0x0000007F; // NAPOT, 2^11
    entry.cfg  = PMP_NAPOT | PMP_R | PMP_W | PMP_X;
    pmp_entry_write(0, &entry);

    TRY {
        ucall(test_hello);
        printf(" fail\n");
        res = 1;
    }
    CATCH {
        printf(" pass\n");
    }
    END_TRY;

    printf("Goodbye VeeR (M mode)\n");
    return res;
}

