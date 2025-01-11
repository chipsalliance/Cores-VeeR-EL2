/* SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Antmicro, Ltd. <www.antmicro.com>
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
#include "random_data.h"

#define mailbox_addr 0xd0580000

extern uint32_t _text;
extern uint32_t _text_end;
extern uint32_t _data;
extern uint32_t _data_end;
extern uint32_t _stack_lo;
extern uint32_t _stack_hi;
extern uint32_t _area;
extern uint32_t tohost;

// ============================================================================

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

int __attribute__((noinline)) test_read (const uint32_t* pattern, uint32_t* source, size_t size) {
    did_execute = 1;
    printf("  reading from 0x%x...\n", source);

    if (memcmp(source, pattern, size)) {
        printf("  data mismatch\n");
        return -1;
    }
    else {
        printf("  data match\n");
    }

    return 0;
}

void __attribute__((noinline)) test_write (const uint32_t* pattern, uint32_t* target, size_t size) {
    did_execute = 1;
    printf("  writing to 0x%x...\n", target);

    memcpy((void*)target, pattern, size);
}

void __attribute__((noinline, naked, optimize("O0"), section(".area.code"))) test_exec () {
    asm volatile ("ret");
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

enum RegionType {
    OFF = 0,
    TOR = 1,
    NA4 = 2,
    NAPOT = 3
};

uint32_t reconcile_address(uint32_t address) {
    uint32_t area_end = ((uint32_t)&_area) + 0x40;
    address &= 0x7fffffff; // do not use 0xf region
    while (((address < (uint32_t)&_stack_hi && address >= (uint32_t)&_stack_lo)
           ||(address >= (uint32_t)&_text && address < (uint32_t)&_text_end)
           ||(address >= (uint32_t)&_data && address < (uint32_t)&_data_end)
           ||(address >= (uint32_t)&_area && address < area_end)
           ||(address >= 0x10000000 && address < 0x20000000) // csrs
           ||(address >= 0x00000 && address < 0x40000) // reserved
           ||(address >= 0x60000 && address < 0x80000) // reserved
           ||(address >= 0x60000 && address < 0x80000) // reserved
           ||(address >= 0xa0000 && address < 0x10000000) // reserved
           ||(address == mailbox_addr))
        && (address != 0)
    ) {
        address >>= 1;
    }
    if (address == 0) {
        // 0 is reserved, fallback
        address = 0x76543210;
    }

    return address;
}

uint32_t legalize_address(uintptr_t address, enum RegionType region_type) {
    switch (region_type) {
    case OFF:
        return 0;
    case TOR:
        return 0;
    case NA4:
        // Do not use two most significant bits, VeeR ties them to 0 anyway.
        address &= 0x3fffffff;
        break;
    case NAPOT:
        // Do not use regions smaller than 32-bytes
        address |= 3;
        // Do not use large regions.
        if ((address & 0x3ff) == 0x3ff) address &= ~(1<<7);
        // Do not use two most significant bits, VeeR ties them to 0 anyway.
        address &= 0x3fffffff;
        break;
    default:
        break;
    }

    return address;
}

uint8_t legalize_config(uint32_t config) {
    uint32_t tmp_config = config;
    // if not enabled, shift right until it's a valid enabled region.
    // if it's 0, give up.
    while ((((config & PMP_MODE_MASK) == PMP_OFF) || ((config & PMP_MODE_MASK) == PMP_TOR))
           && (tmp_config>>3) !=0) {
        config &= ~PMP_MODE_MASK;
        config |= tmp_config & PMP_MODE_MASK;
        tmp_config >>= 1;
    }

    // if no valid mode was found in the random data, fallback to NAPOT
    if (((config & PMP_MODE_MASK) == PMP_OFF)
        ||(config & PMP_MODE_MASK) == PMP_TOR) {
        config &= ~PMP_MODE_MASK;
        config |= PMP_NAPOT;
    }

    tmp_config = config;
    while ((((config & PMP_RWX_MASK) == PMP_W) || ((config & PMP_RWX_MASK) == (PMP_W | PMP_X)))
           & (tmp_config != 0)) {
        // -W- is illegal, -WX is illegal, find another config
        config &= ~PMP_RWX_MASK;
        config |= tmp_config & PMP_RWX_MASK;
        tmp_config >>= 1;
    }

    // This test assumes Lock is 0
    config &= ~PMP_LOCK;

    // config registers are 8bit
    config &= 0xff;
    return (uint8_t)config;
}

#define TST_R       1
#define TST_W       2
#define TST_X       4
#define TST_M       16

#define trailing_ones(x) __builtin_ctz(~x & (x + 1))

uint32_t generate_napot_mask(uint32_t value) {
    // Find the position of the first zero
    uint32_t pos = trailing_ones(value);
    // Create a mask with 'pos' number of ones
    uint32_t mask = (1U << pos) - 1;
    return mask;
}

int get_effective_range(uintptr_t * const address, enum RegionType region_type, uintptr_t * const addr_hi, uintptr_t * const addr_lo) {
    *address = legalize_address(*address, region_type);

    // address is the value to be written to address register
    // addr_hi and addr_lo should hold actual addresses
    uint32_t mask = generate_napot_mask(*address);
    uintptr_t new_address = 0;
    switch (region_type) {
    case OFF:
        *addr_lo = 0;
        *addr_hi = 0;
        break;
    case TOR:
        *addr_lo = 0;
        *addr_hi = *address << 2;
        break;
    case NA4:
        *addr_lo = *address << 2;
        new_address = reconcile_address(*addr_lo);
        if (new_address != (*addr_lo)) {
            *addr_lo = new_address;
            // need to update the address to be written to register as well
            *address = *addr_lo >> 2;
        }
        *addr_hi = *addr_lo + 3;
        break;
    case NAPOT:
        *addr_lo = ((uint32_t)*address & ~mask) << 2;
        new_address = reconcile_address(*addr_lo);
        if (new_address != (*addr_lo)) {
            *addr_lo = new_address;
            // need to update the address to be written to register as well
            *address &= ~mask;
            *address |= ((new_address >> 2) & ~mask);
        }
        *addr_hi = *addr_lo + (1 << (trailing_ones(*address)+3)) - 1;
        break;
    default:
        break;
    }
    return 0;
}

int main () {
    printf("Hello VeeR (M mode)\n");
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
    struct pmp_entry_s random_entry;
    int tid = 0;
    int failed = 0;

    pmp_clear();
    // ................................
    // Do the tests

    // This test iterates over random data (see random_data.h)
    // which contains values for address and configuration.
    // Random data needs to be adjusted to represent legal configurations. 
    // Currently each iteration configures only one region and the others remain OFF.
    // TOR regions are not used.

    // use regions 6..15 for random data
    int region_for_rand_data = 6;

    for (int rand_test_i = 0; rand_test_i<RANDOM_ITERATIONS; ++rand_test_i) {
        printf("test %d/%d\n", rand_test_i, RANDOM_ITERATIONS);
        size_t i = rand_test_i;

        printf(" using random data (%d)\n", rand_test_i);
        // hold the value to be written to cfg register
        uint8_t config = legalize_config(rand_config[i]);
        // hold the value to be written to addr register
        uintptr_t address = rand_address[i];

        enum RegionType region_type = (config >> 3) & 3;
        uintptr_t addr_hi = 0;
        uintptr_t addr_lo = 0;
        uint32_t region_size = 0;

        // Get access rights from `config`.
        uint32_t r = ((config & PMP_R) == PMP_R) ? 1 : 0;
        uint32_t w = ((config & PMP_W) == PMP_W) ? 1 : 0;
        uint32_t x = ((config & PMP_X) == PMP_X) ? 1 : 0;

        /* Calculate effective range using type and addr. */
        get_effective_range(&address, region_type, &addr_hi, &addr_lo);
        region_size = addr_hi - addr_lo + 1;

        // Effective mode
        uint32_t r_eff = 1; // not using user mode or Lock
        uint32_t w_eff = 1; // not using user mode or Lock
        uint32_t x_eff = x;

        char pstr[4] = {
            r ? 'R' : '-',
            w ? 'W' : '-',
            x ? 'X' : '-',
            0x00
        };

        printf("%02d - Machine mode: test %s in region(%d): 0x%x - 0x%x, size:0x%x\n",
               tid++, pstr, region_type, addr_lo, addr_hi, region_size);

        // Write data to the tested region before configuring PMP.
        const uint32_t* pattern = (i & 1) ? test_pattern_b : test_pattern_a;
        const uint32_t* other   = (i & 1) ? test_pattern_a : test_pattern_b;

        size_t test_size = (region_size > sizeof(other)) ? sizeof(other) : region_size;

        memcpy((void*)addr_lo, other, test_size);

        // Disable the region previously used for random data.
        random_entry.cfg = PMP_OFF;
        random_entry.addr = 0;
        pmp_entry_write(region_for_rand_data, &random_entry);

        // Use the next region for random data (from the range 6..15)
        region_for_rand_data = (region_for_rand_data < 15) ? region_for_rand_data+1 : 6;

        random_entry.cfg = config;
        random_entry.addr = address;
        pmp_entry_write(region_for_rand_data, &random_entry);

        // Check
        struct pmp_entry_s readback;
        pmp_entry_read(region_for_rand_data, &readback);

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

        int exc;
        int cmp;
        int any_fail = 0;

        // Test writing. Write pattern from user mode and check if it was
        // successfully written.
        printf(" testing W...\n");
        did_execute = 0;
        exc = 0;
        TRY { test_write(pattern, (uint32_t *)addr_lo, test_size); }
        CATCH { exc = 1; }
        END_TRY;

        cmp = memcmp((void*)addr_lo, pattern, test_size);
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
            memcpy((void*)addr_lo, pattern, test_size);
        }

        did_execute = 0;
        exc = 0;
        TRY { cmp = test_read(pattern, (uint32_t *)addr_lo, test_size); }
        CATCH { exc = 1; }
        END_TRY;

        if (did_execute && ((!r_eff && exc) || (r_eff && !exc && !cmp))) {
            printf(" pass\n");
        } else {
            printf(" fail\n");
            any_fail = 1;
        }

#ifdef TEST_X // TODO test execution rights

        void (*copied_test_exec)();

        random_entry.cfg = PMP_OFF;
        pmp_entry_write(region_for_rand_data, &random_entry);

        // Copy `test_exec` into the region
        // test_exec contains only 'ret' and any region is at least 4 bytes in size
        memcpy((void*)addr_lo, &test_exec, 4);

        random_entry.cfg = config;
        pmp_entry_write(region_for_rand_data, &random_entry);

        copied_test_exec = (void(*)())addr_lo;
        // Call a function placed in the designated area
        printf(" testing X...\n");
        TRY {
            copied_test_exec();
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
#endif // TEST_X

        if (any_fail)
            printf(" random data used:\n   addr: 0x%x,\n   cfg: 0x%x\n", rand_address[rand_test_i], rand_config[rand_test_i]);
        // Count fails
        failed += any_fail;
    }

    // .......................................................................

    printf(" %d/%d passed\n", tid - failed, tid);
    int res = (failed == 0) ? 0 : -1;

    if (!res) printf("*** PASSED ***\n");
    else      printf("*** FAILED ***\n");

    printf("Goodbye VeeR (M mode)\n");

    _exit(res);
    return res;
}

