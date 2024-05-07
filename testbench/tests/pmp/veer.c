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

#if USE_HTIF

extern volatile uint64_t tohost;
extern volatile uint64_t fromhost;

int64_t veer_syscall (int64_t a0, int64_t a1, int64_t a2, int64_t a3) {

    // HTIF syscall command. It uses 8 args but for most cases 4 is enough.
    volatile int64_t cmd[8] = {
        a0, a1, a2, a3,
        0,  0,  0,  0
    };

    // Write a pointer to the command buffer to "tohost"
    tohost = (uint64_t)(uintptr_t)cmd;

    // Wait for response in "fromhost"
    while (1) {
        volatile uint64_t fh = fromhost;
        if (fh != 0) {
            fromhost = 0; // reply
            break;
        }
    }

    return cmd[0];
}
#else

extern volatile char  tohost;

#endif

__attribute__((__noreturn__)) void _exit (int status)
{
#if USE_HTIF
    veer_syscall (HTIF_SYSCALL_EXIT, status, 0, 0);
#else
    if (!status) tohost = 0xff;
    else tohost = 0x01;
#endif
    while (1);
}

int veer_tb_putc(char c, FILE *stream)
{
    (void) stream;

#if USE_HTIF
    // Do putc() via htif "bcd" device in Spike
    tohost = (1LL << 56) | (1LL << 48) | c;
    while (tohost != 0); // wait for reply
#else
    tohost = c;
#endif

    return c;
}

static FILE __stdio = FDEV_SETUP_STREAM(veer_tb_putc, NULL, NULL, _FDEV_SETUP_WRITE);
FILE *const stdin = &__stdio;
__strong_reference(stdin, stdout);
__strong_reference(stdin, stderr);
