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
#include "trap.h"
#include "fault.h"

#define TEST_NUMBER 1

int test_store(void)
{
    char *a = 0xf0000000;
    struct fault ret;
    TRY {
        *a = 0xff;
        return 2;
    }
    CATCH {
        ret = fault_last_get();
        return (ret.mcause == 7) ? 0 : 1;
    }
    END_TRY;
    return 3;
}

void main(void)
{
    int results[TEST_NUMBER];
    int sum = 0;

    puts("PMP test program");
    fault_install();

    puts(":: test_store");
    results[0] = test_store();
    printf(":: test_store: ");
    if (!results[0]) puts("passed\n");
    else printf("failed (%d)\n", results[0]);

    for (int i = 0; i < TEST_NUMBER; i++)
        sum += results[i];

    exit(sum);
}
