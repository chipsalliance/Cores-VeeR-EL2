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
#include "trap.h"
#include "fault.h"
#include "pmp.h"

#define TEST_NUMBER 3

int test_load(int);
int test_store(int);
int test_exec(int);

int (*tests[TEST_NUMBER]) (int) = {test_load, test_store, test_exec};
const char *const test_names[TEST_NUMBER] = {"test_load", "test_store", "test_exec"};

volatile int temp_load;
volatile int temp_store;

#define PATTERN_A 0xaaaaaaaa
#define PATTERN_B 0x55555555

int test_load(int id)
{
    int temp = PATTERN_B;
    struct fault ret;

    TRY {
        struct pmp_entry_s entry = {
            .addr = ((uintptr_t)(&temp_load)) >> 2,
            .cfg = PMP_LOCK | PMP_NA4 | PMP_X | PMP_W
        };
        pmp_entry_write(id, &entry);
        temp_load = PATTERN_A;
        temp = temp_load;
    }
    CATCH {
        if ((temp != PATTERN_B) && (temp == PATTERN_A)) return 3;
        ret = fault_last_get();
        return (ret.mcause == EXC_LOAD_ACC_FAULT) ? 0 : 1;
    }
    END_TRY;
    return 2;
}

int test_store(int id)
{
    struct fault ret;

    TRY {
        temp_store = PATTERN_A;
        struct pmp_entry_s entry = {
            .addr = ((uintptr_t)(&temp_store)) >> 2,
            .cfg = PMP_LOCK | PMP_NA4 | PMP_X | PMP_R
        };
        pmp_entry_write(id, &entry);
        temp_store = PATTERN_B;
    }
    CATCH {
        if (temp_store == PATTERN_B) return 3;
        ret = fault_last_get();
        return (ret.mcause == EXC_STORE_ACC_FAULT) ? 0 : 1;
    }
    END_TRY;
    return 2;
}

void __attribute__ ((noinline)) test_exec_1(void)
{
    puts(__func__);
    return;
}

int test_exec(int id)
{
    struct fault ret;

    TRY {
        struct pmp_entry_s entry = {
            .addr = ((uintptr_t)(test_exec_1)) >> 2,
            .cfg = PMP_LOCK | PMP_NA4 | PMP_W | PMP_R
        };
        pmp_entry_write(id, &entry);
        test_exec_1();
    }
    CATCH {
        ret = fault_last_get();
        return (ret.mcause == EXC_INSTRUCTION_ACC_FAULT) ? 0 : 1;
    }
    END_TRY;
    return 2;
}

void main(void)
{
    int results[TEST_NUMBER];
    int sum = 0;

    puts("PMP/exception test program");
    fault_install();

    for (int i = 0; i < TEST_NUMBER; i++) {
        printf(":: %s\n", test_names[i]);
        results[i] = tests[i](i);
        printf(":: %s: %s (%d)\n", test_names[i], (results[i] ? "failed" : "passed"), results[i]);
        sum += results[i];
    }

    exit(sum);
}
