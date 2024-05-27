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
#include <string.h>
#include <defines.h>
#include "veer.h"
#include "fault.h"
#include "pmp.h"

#ifndef RV_SMEPMP
#define RV_SMEPMP 0
#endif

#define CSR_MSTATUS 0x300
#define CSR_MISA    0x301
#define CSR_MEPC    0x341

#define MISA_U      (1 << 20)

extern uint32_t _text;
extern uint32_t _text_end;
extern uint32_t _data;
extern uint32_t _data_end;
extern uint32_t _stack_lo;
extern uint32_t _stack_hi;
extern uint32_t _area;
extern uint32_t tohost;

extern int ucall (void* ptr, ...);

// ============================================================================

volatile uint32_t test_area [16] __attribute__((section(".area.bufr")));

const uint32_t test_pattern_a [] = {
    0xE8C50A2E,
    0x017F84CA,
    0xFB8A3138,
    0xFDF0F930,
    0xA5F12034,
    0x4A67B7B6,
    0xD03C9377,
    0xD124A11C,
    0xAB319961,
    0xF94AF557,
    0xDD743AE6,
    0xAAB99BC3,
    0xE992D7FA,
    0x5C6A76FA,
    0xD8D63FE2,
    0x8616CFC6
};

const uint32_t test_pattern_b [] = {
    0x2B0B56F2,
    0x6B78B6FF,
    0xE7B61C7A,
    0x66FB04DB,
    0xC2F2BE9D,
    0x2D569A89,
    0x905BF8E6,
    0x2798E7CE,
    0x509BA997,
    0xBF0147EB,
    0x09065BEF,
    0x04146267,
    0xC421C6E3,
    0xD6C76040,
    0x773AA931,
    0x01C01BDE
};

volatile unsigned long did_execute = 0;

void __attribute__((noinline)) test_hello () {
    did_execute = 1;
    printf("  hello\n");
}

int __attribute__((noinline)) test_read (const uint32_t* pattern) {
    did_execute = 1;
    printf("  reading from .area...\n");

    uint32_t arr[16];
    for (size_t i=0; i<16; ++i) {
        arr[i] = test_area[i];
    }

    if (memcmp(arr, pattern, sizeof(arr))) {
        printf("  data mismatch\n");
        return -1;
    }
    else {
        printf("  data match\n");
    }

    return 0;
}

void __attribute__((noinline)) test_write (const uint32_t* pattern) {
    did_execute = 1;
    printf("  writing to .area...\n");

    for (size_t i=0; i<16; ++i) {
        test_area[i] = pattern[i];
    }
}

void __attribute__((noinline, section(".area.code"))) test_exec () {
    printf("  hello from .area\n");
}

// ============================================================================

volatile unsigned long trap_count = 0;

int trap_handler (const struct fault* fault) {
    printf(" Trap! mcause=0x%08x, mepc=0x%08X, sp=0x%08X\n", fault->mcause, fault->mepc, fault->r[2]);

    // Terminate the simulation if too many traps got triggered
    if (++trap_count > 100) {
        printf("Too many traps, aborting...\n");
        _exit(-1);
    }

    // If setjmp-based try-catch was used return to the program
    fault_return(fault);
    return 0;
}

// ============================================================================

// Convert byte address for PMP. Effectively does "ceil(x / 4)"
#define ADDR2PMP(x) ((((uint32_t)(x)) & 3) ? ((((uint32_t)(x)) >> 2) + 1) : \
                                              (((uint32_t)(x)) >> 2))

// Set mstatus MPRV
#define set_mprv(x) {                   \
    uint32_t mstatus;                   \
    CSRR_READ(mstatus, CSR_MSTATUS);    \
    if (x) mstatus |=  (1 << 17);       \
    else   mstatus &= ~(1 << 17);       \
    CSRR_WRITE(mstatus, CSR_MSTATUS);   \
}

// Set mstatus MPP to 00 or 11
#define set_mpp(x)  {                   \
    uint32_t mstatus;                   \
    CSRR_READ(mstatus, CSR_MSTATUS);    \
    if (x) mstatus |=  (3 << 11);       \
    else   mstatus &= ~(3 << 11);       \
    CSRR_WRITE(mstatus, CSR_MSTATUS);   \
}

#define TST_R       1
#define TST_W       2
#define TST_X       4
#define TST_M       16
#define TST_MPRV    32
#define TST_MPP     64

// ============================================================================

int main () {
    printf("Hello VeeR (M mode)\n");

#if RV_SMEPMP
    printf("VeeR has Smepmp\n");
#else
    printf("VeeR does not have Smepmp\n");
#endif

    // Check if we have user mode support
    uint32_t misa = 0;
    CSRR_READ(misa, CSR_MISA);
    int have_user_mode = (misa & MISA_U) != 0;

#if RV_SMEPMP
    // Set MSECCFG
    uint32_t mseccfg = 0;
    CSRR_WRITE(mseccfg, 0x747);
#endif

    // .......................................................................
    // Determine PMP granularity
    uintptr_t tmp = 0;
    pmp_write_pmpcfg (0, &tmp);
    tmp = 0xFFFFFFFF;
    pmp_write_pmpaddr(0, &tmp);
    pmp_read_pmpaddr (0, &tmp);

    int g = 0;
    for (; g < 32; ++g) {
        if (tmp & 1) break;
        tmp >>= 1;
    }

    printf("PMP G=%d, granularity is %d\n", g, 1 << (g + 2));

    // .......................................................................
    struct pmp_entry_s entry;
    int tid = 0;
    int failed = 0;

    pmp_clear();

    // .......................................................................
    // Check if user mode has access to everything by default when PMP is not
    // configured. Just call a simple function.
    if (have_user_mode) {
        printf("%02d - User mode RWX in default state\n", tid++);

        printf(" testing...\n");
#if RV_SMEPMP
        TRY {
            ucall(test_hello);
            printf(" fail\n");
            failed++;
        }
        CATCH {
            printf(" pass\n");
        }
        END_TRY;
#else
        TRY {
            ucall(test_hello);
            printf(" pass\n");
        }
        CATCH {
            printf(" fail\n");
            failed++;
        }
        END_TRY;
#endif
    }

    // .......................................................................
    // Configure a single region in PMP and call user mode function. It should
    // not have access to code and stack hence it should not execute
    if (have_user_mode) {
        printf("%02d - User mode RWX with one (any) PMP region enabled\n", tid++);

        // Allow area1 user access
        entry.addr = ADDR2PMP(&_area);
        entry.addr = (entry.addr & 0xFFFFFC00) | 0x000001FF; // NAPOT, 2^12
        entry.cfg  = PMP_NAPOT | PMP_R | PMP_W | PMP_X;
        pmp_entry_write(5, &entry);

        printf(" testing...\n");
        TRY {
            ucall(test_hello);
            printf(" fail\n");
            failed++;
        }
        CATCH {
            printf(" pass\n");
        }
        END_TRY;
    }

    // .......................................................................
    // Configure PMP to allow user mode access to code and stack
    if (have_user_mode) {
        printf("%02d - User mode RWX with code, data and stack access allowed\n", tid++);

        // Allow user access to "tohost" and "fromhost"
        entry.addr = ADDR2PMP(&tohost);
        entry.addr = (entry.addr & 0xFFFFFFFC) | 1; // NAPOT 2^4
        entry.cfg  = PMP_NAPOT | PMP_R | PMP_W;
        pmp_entry_write(0, &entry);

        // Allow user access to code
        entry.addr = ADDR2PMP(&_text);
        entry.cfg  = 0;
        pmp_entry_write(1, &entry);
        entry.addr = ADDR2PMP(&_text_end) + 1; // upper bound is not inclusive
        entry.cfg  = PMP_TOR | PMP_R | PMP_X;
        pmp_entry_write(2, &entry);

        // Allow user access to data
        entry.addr = ADDR2PMP(&_data);
        entry.addr = (entry.addr & 0xFFFFFC00) | 0x000001FF; // NAPOT, 2^12
        entry.cfg  = PMP_NAPOT | PMP_R | PMP_W;
        pmp_entry_write(3, &entry);
        entry.addr = ADDR2PMP(&_data);

        // Allow user access to stack
        entry.addr = ADDR2PMP(&_stack_lo);
        entry.addr = (entry.addr & 0xFFFFF800) | 0x000003FF; // NAPOT, 2^13
        entry.cfg  = PMP_NAPOT | PMP_R | PMP_W;
        pmp_entry_write(4, &entry);

        printf(" testing...\n");
        TRY {
            ucall(test_hello);
            printf(" pass\n");
        }
        CATCH {
            printf(" fail\n");
            failed++;
        }
        END_TRY;
    }

    // .......................................................................
    // Test PMP operation for all possible RWX combinations in U and M mode.

    // Generate test cases. A test case is encoded on a byte:
    // bit 0: R
    // bit 1: W
    // bit 2: X
    // bit 4: 0-user, 1-machine
    // bit 5: mstatus.MPRV
    // bit 6: mstatus.MPP (0 for 00, 1 for 11)
    uint8_t  test_cases [32];
    uint32_t test_count = 0;

    // Test cases for all RWX combinations in user mode
    if (have_user_mode) {
        for (size_t i=0; i<8; ++i) {
            uint32_t r = (i & 1) ? PMP_R : 0;
            uint32_t w = (i & 2) ? PMP_W : 0;
            uint32_t x = (i & 4) ? PMP_X : 0;

#if RV_SMEPMP
            // Skip -W- and -WX combinations
            if (!r &&  w && !x) continue;
            if (!r &&  w &&  x) continue;
#endif
            test_cases[test_count++] = i;
        }
    }

    // Test cases for all RWX combinations in machine mode
    for (size_t i=0; i<8; ++i) {
        uint32_t r = (i & 1) ? PMP_R : 0;
        uint32_t w = (i & 2) ? PMP_W : 0;
        uint32_t x = (i & 4) ? PMP_X : 0;

#if RV_SMEPMP
        // Skip -W- and -WX combinations
        if (!r &&  w && !x) continue;
        if (!r &&  w &&  x) continue;
#endif
        test_cases[test_count++] = TST_M | i;
    }

    // Test cases for all RWX combinations in machine mode with MPRV set
    if (have_user_mode) {
        for (size_t i=0; i<16; ++i) {
            uint32_t r = (i & 1) ? PMP_R : 0;
            uint32_t w = (i & 2) ? PMP_W : 0;
            uint32_t x = (i & 4) ? PMP_X : 0;
            uint32_t mpp = (i & 8) != 0;

#if RV_SMEPMP
            // Skip -W- and -WX combinations
            if (!r &&  w && !x) continue;
            if (!r &&  w &&  x) continue;
#endif
            test_cases[test_count++] = (TST_MPP * mpp) | TST_MPRV | TST_M | i;
        }
    }

    // ................................
    // Do the tests

    for (size_t i=0; i<test_count; ++i) {
        uint32_t bits = test_cases[i];

        uint32_t r = (bits & TST_R) ? PMP_R : 0;
        uint32_t w = (bits & TST_W) ? PMP_W : 0;
        uint32_t x = (bits & TST_X) ? PMP_X : 0;
        uint32_t m = (bits & TST_M) != 0;
        uint32_t mprv = (bits & TST_MPRV) != 0;
        uint32_t mpp  = (bits & TST_MPP ) != 0;

        // Effective mode
        uint32_t r_eff = (m && !(mprv && !mpp)) ? 1 : r;
        uint32_t w_eff = (m && !(mprv && !mpp)) ? 1 : w;
        uint32_t x_eff = (m)                    ? 1 : x; // MPRV affects load/store only

        char pstr[4] = {
            r ? 'R' : '-',
            w ? 'W' : '-',
            x ? 'X' : '-',
            0x00
        };

        const char* mstr = m ? "Machine" : "User";
        printf("%02d - %s mode (MPRV=%d, MPP=%d) %s from designated areas\n", tid++, mstr, mprv, mpp, pstr);

        // Prepare data
        const uint32_t* pattern = (i & 1) ? test_pattern_b : test_pattern_a;
        const uint32_t* other   = (i & 1) ? test_pattern_a : test_pattern_b;

        memcpy((void*)test_area, other, sizeof(test_area));

        // Configure .area1 access
        printf(" configuring PMP...\n");
        entry.addr = ADDR2PMP(&_area);
        entry.addr = (entry.addr & 0xFFFFFC00) | 0x000001FF; // NAPOT, 2^12
        entry.cfg  = PMP_NAPOT | r | w | x;
        pmp_entry_write(5, &entry);

        // Check
        struct pmp_entry_s readback;
        pmp_entry_read(5, &readback);

        // An illegal PMP region configuration has been written and readback
        // this is an error
        //
        // -W- and -WX combinations are reserved except for when Smepmp is
        // present and mseccfg.MML=1. This test does not enable the latter
        // so the combinations are not legal.
        if (!pmp_is_cfg_legal(readback.cfg)) {
            printf("  error, an illegal PMP configuration accepted by the core\n", readback.cfg);
            failed++;
            continue;
        }

        // R,W and X fields are WARL which means that the readback does not
        // need to match what was written. In such a case skip the test but
        // not mark it as an error.
        if (readback.cfg != entry.cfg) {
            continue;
        }

        int exc;
        int cmp;
        int any_fail = 0;

        // Test writing. Write pattern from user mode and check if it was
        // successfully written.
        printf(" testing W...\n");
        did_execute = 0;
        exc = 0;
        set_mpp(mpp);
        set_mprv(mprv);
        TRY { if (m) test_write(pattern); else ucall(test_write, pattern); }
        CATCH { exc = 1; }
        END_TRY;
        set_mprv(0);

        cmp = memcmp((void*)test_area, pattern, sizeof(test_area));
        if (cmp) {
            printf("  data mismatch\n");
        } else {
            printf("  data match\n");
        }

        if (did_execute && ((!w_eff && exc && cmp) || (w_eff && !exc && !cmp))) {
            printf(" pass\n");
        } else {
            printf(" fail\n");
            any_fail = 1;
        }

        // Test reading. Read area from user mode and compare against the
        // pattern
        printf(" testing R...\n");

        // Write pattern
        if (!w_eff) {
            memcpy((void*)test_area, pattern, sizeof(test_area));
        }

        did_execute = 0;
        exc = 0;
        set_mpp(mpp);
        set_mprv(mprv);
        TRY { if (m) cmp = test_read(pattern); else cmp = ucall(test_read, pattern); }
        CATCH { exc = 1; }
        END_TRY;
        set_mprv(0);

        if (did_execute && ((!r_eff && exc) || (r_eff && !exc && !cmp))) {
            printf(" pass\n");
        } else {
            printf(" fail\n");
            any_fail = 1;
        }

        // Call a function placed in the designated area
        printf(" testing X...\n");
        TRY {
            if (m) test_exec(); else ucall(test_exec);
            if (x_eff) {
                printf(" pass\n");
            } else {
                printf(" fail\n");
                any_fail = 1;
            }
        }
        CATCH {
            if (x_eff) {
                printf(" fail\n");
                any_fail = 1;
            } else {
                printf(" pass\n");
            }
        }
        END_TRY;

        // Count fails
        failed += any_fail;
    }

    // .......................................................................
    // Test PMP region lock feature.

    // Since unlocking a region requires core reset this test does only X
    // permission check. Testing different possibilities would require either
    // a set of tests of a form of persistent storage in the testbench / SoC
    // RTL.

    printf("%02d - Testing execution from a locked region in U and M mode\n", tid++);

    // Prevent both U and M modes form executing from .area1
    entry.addr = ADDR2PMP(&_area);
    entry.addr = (entry.addr & 0xFFFFFC00) | 0x000001FF; // NAPOT, 2^12
    entry.cfg  = PMP_NAPOT | PMP_R | PMP_W | PMP_LOCK;
    pmp_entry_write(5, &entry);

    // Execute from U
    if (have_user_mode) {
        printf(" testing from U mode...\n");
        TRY {
            ucall(test_exec);
            printf(" fail\n");
            failed++;
        }
        CATCH {
            printf(" pass\n");
        }
        END_TRY;
    }

    // Execute from M
    printf(" testing from M mode...\n");
    TRY {
        test_exec();
        printf(" fail\n");
        failed++;
    }
    CATCH {
        printf(" pass\n");
    }
    END_TRY;

    // Check if the region can be un-locked
    printf(" attempting to unlock region...\n");

    entry.addr = ADDR2PMP(&_area);
    entry.addr = (entry.addr & 0xFFFFFC00) | 0x000001FF; // NAPOT, 2^12
    entry.cfg  = PMP_NAPOT | PMP_R | PMP_W | PMP_X;
    pmp_entry_write(5, &entry);

    // Execute from U
    if (have_user_mode) {
        printf(" testing from U mode...\n");
        TRY {
            ucall(test_exec);
            printf(" fail\n");
            failed++;
        }
        CATCH {
            printf(" pass\n");
        }
        END_TRY;
    }

    // Execute from M
    printf(" testing from M mode...\n");
    TRY {
        test_exec();
        printf(" fail\n");
        failed++;
    }
    CATCH {
        printf(" pass\n");
    }
    END_TRY;

    // .......................................................................

    printf(" %d/%d passed\n", tid - failed, tid);
    int res = (failed == 0) ? 0 : -1;

    if (!res) printf("*** PASSED ***\n");
    else      printf("*** FAILED ***\n");

    printf("Goodbye VeeR (M mode)\n");

    _exit(res);
    return res;
}

