/* SPDX-License-Identifier: Apache-2.0
 * Copyright 2024 Antmicro <www.antmicro.com>
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
#include <stdint.h>

#define STDOUT 0xd0580000
volatile char* stdout = (char *)STDOUT;

#define MFDC_DISABLE_ECC_MASK 0x100
#define INJECT_ICCM_SINGLE_BIT 0xe0
#define INJECT_ICCM_DOUBLE_BIT 0xe1
#define INJECT_DCCM_SINGLE_BIT 0xe2
#define INJECT_DCCM_DOUBLE_BIT 0xe3
#define DISABLE_ERROR_INJECTION 0xe4
#define TEST_PASSED 0xff
#define TEST_FAILED 0x01


#define ICCM_SADDR 0xee000000
#define DCCM_SADDR 0xf0040000

void execute_from_iccm (void) __attribute__ ((aligned(4),section(".iccm_data0")));
volatile uint32_t boot_count __attribute__((section(".dccm.persistent"))) = 0;
uint32_t dccm_test, iccm_test;
extern const int ICCM_ADDR, DCCM_ADDR;
extern uintptr_t iccm_start, iccm_end;
extern int printf(const char* format, ...);
extern int putchar(int c);


void sleep(uint32_t count) {
    for (uint32_t slp = 0; slp < count; slp++) {
        __asm__ volatile ("nop"); // Sleep loop as "nop"
    }
}

int read_mcause(void) {
    uint32_t mcause;

    __asm__ volatile ("csrr %0, %1"
                      : "=r" (mcause) /* output: variable */
                      : "i" (0x342) /* input : immediate */
                      : /* clobbers: none */);

    return mcause;
}

int read_mscause(void) {
    uint32_t mscause;

    __asm__ volatile ("csrr %0, %1"
                      : "=r" (mscause) /* output: variable */
                      : "i" (0x7FF) /* input : immediate */
                      : /* clobbers: none */);

    return mscause;
}

int read_mfdc(void) {
    uint32_t mfdc;

    __asm__ volatile ("csrr %0, %1"
                      : "=r" (mfdc) /* output: variable */
                      : "i" (0x7F9) /* input : immediate */
                      : /* clobbers: none */);

    return mfdc;
}

int read_mdccmect(void) {
    uint32_t mdccmect;

    __asm__ volatile ("csrr %0, %1"
                      : "=r" (mdccmect) /* output: variable */
                      : "i" (0x7F2) /* input : immediate */
                      : /* clobbers: none */);

    return mdccmect;
}

int read_miccmect(void) {
    uint32_t miccmect;

    __asm__ volatile ("csrr %0, %1"
                      : "=r" (miccmect) /* output: variable */
                      : "i" (0x7F1) /* input : immediate */
                      : /* clobbers: none */);

    return miccmect;
}

void clear_causes(void) {
    __asm__ volatile ("csrw %0, %1"
                      : /* output: none */
                      : "i" (0x342), "i" (0)  /* input : immediate */
                      : /* clobbers: none */);
    __asm__ volatile ("csrw %0, %1"
                      : /* output: none */
                      : "i" (0x7FF), "i" (0) /* input : immediate */
                      : /* clobbers: none */);
}

void disable_ecc_check(void) {
    uint32_t mfdc_disable_ecc_mask = MFDC_DISABLE_ECC_MASK;

    __asm__ volatile ("csrs %0, %1"
                    : /* output: none */
                    : "i" (0x7F9), "r" (mfdc_disable_ecc_mask) /* input : immediate */
                    : /* clobbers: none */);
}

void enable_ecc_check(void) {
    uint32_t mfdc_disable_ecc_mask = MFDC_DISABLE_ECC_MASK;

    __asm__ volatile ("csrc %0, %1"
                    : /* output: none */
                    : "i" (0x7F9), "r" (mfdc_disable_ecc_mask) /* input : immediate */
                    : /* clobbers: none */);
}

void trap_handler(void) {
    uint32_t mcause, mscause, mfdc;

    mfdc = read_mfdc();

    if (mfdc & MFDC_DISABLE_ECC_MASK) {
        printf("Trap hit while ECC check is disabled!\n");
        putchar(TEST_FAILED);
    }

    mcause = read_mcause();
    mscause = read_mscause();
    clear_causes();

    if (((mcause == 0x5 && mscause == 0x1) ||
        (mcause == 0x7 && mscause == 0x1)) &&
        dccm_test == 1) {
        printf("DCCM double bit error\n");
        putchar(DISABLE_ERROR_INJECTION);
    } else if (mcause == 0x1 && mscause == 0x1 && iccm_test == 1) {
        printf("ICCM double bit error\n");
        putchar(DISABLE_ERROR_INJECTION);
    } else {
        printf("Error unrelated to ECC\n");
        putchar(TEST_FAILED);
    }
}

void run_iccm_err_test(int execute) {
    uint32_t *iccm_data = (uint32_t *)ICCM_SADDR;
    uint32_t *iccm = iccm_data;
    void (* iccm_fn) (void) = (void*)iccm_data;
    uint32_t *code_word = 0;
    uint32_t *actual_iccm_code_end = 0;
    uint32_t mfdc, miccmect;

    // Inject single bit ICCM error
    putchar(INJECT_ICCM_SINGLE_BIT);

    code_word = (uint32_t *) &iccm_start;
    printf("Copy code from %x [thru %x] to %x\n", (uintptr_t) code_word, &iccm_end, (uintptr_t) iccm);
    while (code_word < (uint32_t *) &iccm_end) {
        printf("at %x: %x\n", (uintptr_t) code_word, *code_word);
        *iccm++ = *code_word++;
    }
    putchar(DISABLE_ERROR_INJECTION);
    if (execute) {
        iccm_fn();
    }

    mfdc = read_mfdc();
    miccmect = read_miccmect();

    if ((mfdc & MFDC_DISABLE_ECC_MASK) && (miccmect != 0)) {
        printf("Unexpected ECC single-bit error detected!\n");
        putchar(TEST_FAILED);
    } else if (!(mfdc & MFDC_DISABLE_ECC_MASK) && (miccmect == 0)) {
        printf("Did not register expected ECC single-bit error!\n");
        putchar(TEST_FAILED);
    }

    // Inject double bit ICCM error
    putchar(INJECT_ICCM_DOUBLE_BIT);

    code_word = (uint32_t *) &iccm_start;
    iccm = iccm_data;
    printf("Copy code from %x [thru %x] to %x\n", (uintptr_t) code_word, &iccm_end, (uintptr_t) iccm);
    while (code_word < (uint32_t *) &iccm_end) {
        printf("at %x: %x\n", (uintptr_t) code_word, *code_word);
        *iccm++ = *code_word++;
    }
    putchar(DISABLE_ERROR_INJECTION);
    if (execute) {
        iccm_fn();
    }
}

void run_dccm_err_test(void) {
    uint32_t *dccm_data = (uint32_t *)DCCM_SADDR;
    uint32_t *dccm = dccm_data;
    uint32_t mfdc, mdccmect;

    // Inject single bit DCCM error
    putchar(INJECT_DCCM_SINGLE_BIT);
    *dccm = 0x12345678;
    putchar(DISABLE_ERROR_INJECTION);
    printf("DCCM value: 0x%x\n", *dccm);

    mfdc = read_mfdc();
    mdccmect = read_mdccmect();

    if ((mfdc & MFDC_DISABLE_ECC_MASK) && (mdccmect != 0)) {
        printf("Unexpected ECC single-bit error detected!\n");
        putchar(TEST_FAILED);
    } else if (!(mfdc & MFDC_DISABLE_ECC_MASK) && (mdccmect == 0)) {
        printf("Did not register expected ECC single-bit error!\n");
        putchar(TEST_FAILED);
    }

    // Inject double bit DCCM error
    putchar(INJECT_DCCM_DOUBLE_BIT);
    *dccm = 0xDEADBEEF;
    putchar(DISABLE_ERROR_INJECTION);
    printf("DCCM value: 0x%x\n", *dccm);
}

void execute_from_iccm (void) {
    printf("Executed from ICCM!\n");
}

void main(void)
{
    boot_count++;

    printf("------------------------\n");
    printf("Test ECC error injection\n");
    printf("------------------------\n\n");

    printf("Boot count: %d\n", boot_count);

    if (boot_count == 1) {
        iccm_test = 0;
        dccm_test = 1;

        printf("Disable ECC checks\n\n");
        disable_ecc_check();

        run_dccm_err_test();

        printf("\nEnable ECC checks\n\n");
        enable_ecc_check();

        run_dccm_err_test();

        // Should not reach here if ECC error is triggerred correctly

        printf("Did not hit ECC error when expected!\n");
        putchar(TEST_FAILED);
    } else if (boot_count == 2) {
        iccm_test = 1;
        dccm_test = 0;

        printf("Disable ECC checks\n\n");
        disable_ecc_check();

        // Inject errors without executing due to disabled error correction
        run_iccm_err_test(0);

        printf("\nEnable ECC checks\n\n");
        enable_ecc_check();

        run_iccm_err_test(1);

        // Should not reach here if ECC error is triggerred correctly

        printf("Did not hit ECC error when expected!\n");
        putchar(TEST_FAILED);
    } else if (boot_count == 3) {
        printf("Finished\n");
    } else {
        printf("Unexpected reset\n");
        putchar(TEST_FAILED);
    }
}
