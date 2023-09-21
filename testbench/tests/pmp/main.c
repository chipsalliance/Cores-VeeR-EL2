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

int test_load(void);
int test_store(void);
int test_exec(void);

int (*tests[TEST_NUMBER]) (void) = {test_load, test_store, test_exec};
const char *const test_names[TEST_NUMBER] = {"test_load", "test_store", "test_exec"};

int test_load(void)
{
    char b;
    volatile char *a;
    struct fault ret;

    TRY {
        a = (char *)0xf0f0f0f0;
        b = *a;
    }
    CATCH {
        ret = fault_last_get();
        return (ret.mcause == 5) ? 0 : 1;
    }
    END_TRY;
    return 2;
}

int test_store(void)
{
    volatile char *a;
    struct fault ret;

    TRY {
        a = (char *)0xf0f0f0f0;
        *a = 0xff;
    }
    CATCH {
        ret = fault_last_get();
        return (ret.mcause == 7) ? 0 : 1;
    }
    END_TRY;
    return 2;
}

int test_exec(void)
{
    typedef void (*func)();
    func a;
    struct fault ret;

    TRY {
        a = (func)0xf0f0f0f0;
        (*a)();
    }
    CATCH {
        ret = fault_last_get();
        return (ret.mcause == 2) ? 0 : 1;
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
        results[i] = tests[i]();
        printf(":: %s: %s (%d)\n", test_names[i], (results[i] ? "failed" : "passed"), results[i]);
        sum += results[i];
    }

    exit(sum);
}
