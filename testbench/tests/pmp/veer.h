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

#ifndef __VEER_H
#define __VEER_H

// Set to 1 if using HTIF interface eg. in Spike
#define USE_HTIF 0

#include <stdint.h>

struct rv_jmp_buf {
    long            pc;
    unsigned long   regs[31];
    long            exitcode;
};

// RISC-V specific setjmp() variant. Must be called from M-mode
extern long rv_setjmp_m   (struct rv_jmp_buf*);
// RISC-V specific longjmp() variant. Must be called from M-mode
extern void rv_longjmp_m  (struct rv_jmp_buf*, long exitcode);

#define TRY do { struct rv_jmp_buf try_buf = {0}; if(!rv_setjmp_m(&try_buf)) { fault_setjmp(&try_buf);
#define CATCH } else {
#define END_TRY } } while(0)

__attribute__((__noreturn__)) void _exit (int status);

#if USE_HTIF
#define HTIF_SYSCALL_WRITE  64
#define HTIF_SYSCALL_EXIT   93

int64_t veer_syscall (int64_t a0, int64_t a1, int64_t a2, int64_t a3);
#endif

#endif
