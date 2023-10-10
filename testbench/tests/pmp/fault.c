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

#include <stdlib.h>
#include <string.h>
#include <setjmp.h>
#include "trap.h"
#include "fault.h"

int fault_jmp_env_set = 0;
jmp_buf fault_jmp_env;
struct fault fault_last;

void fault_install(void)
{
    __asm__("la t0, _trap");
    __asm__("csrw mtvec, t0");
}

void fault_setjmp(jmp_buf env)
{
    memcpy(fault_jmp_env, env, sizeof(fault_jmp_env));
    fault_jmp_env_set = 1;
}

struct fault fault_last_get(void)
{
    return fault_last;
}

void fault_return(struct fault *fault)
{
    // Save register state for later usage
    memcpy(&fault_last, fault, sizeof(fault_last));

    // Return to program if setjmp-based try-catch was used
    if (fault_jmp_env_set) {
        fault_jmp_env_set = 0;
        longjmp(fault_jmp_env, 1);
    }
    else {
        exit(1);
    }
}
