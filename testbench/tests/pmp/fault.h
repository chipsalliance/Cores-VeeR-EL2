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

#ifndef _FAULT_H
#define _FAULT_H

#include <setjmp.h>
#include "trap.h"

#define EXC_INSTRUCTION_ACC_FAULT 1
#define EXC_LOAD_ACC_FAULT 5
#define EXC_STORE_ACC_FAULT 7

void fault_install(void);
void fault_setjmp(jmp_buf env);
struct fault fault_last_get(void);
void fault_return(struct fault *fault);

#endif
