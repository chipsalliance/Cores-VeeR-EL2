/* SPDX-License-Identifier: Apache-2.0
 *
 * Verifies that ordinary DCCM stores/loads still work correctly with the
 * DCCM write-readback check (RV_DCCM_WR_READBACK) both disabled and enabled
 * at runtime via the "dwrd" bit (MFDC bit 7). The check is expected to be
 * transparent to normal, non-faulty operation in either state.
 */

#include <stdint.h>

#define MFDC_CSR 0x7f9
#define MFDC_DCCM_WR_READBACK_DISABLE_MASK 0x80 /* bit 7, "dwrd" */

#define TEST_PASSED 0xff
#define TEST_FAILED 0x01

#define DCCM_SADDR 0xf0040000

extern int printf(const char *format, ...);
extern int putchar(int c);

static uint32_t read_mfdc(void)
{
    uint32_t mfdc;

    __asm__ volatile ("csrr %0, %1"
                      : "=r" (mfdc)
                      : "i" (MFDC_CSR)
                      : );

    return mfdc;
}

static void disable_dccm_wr_readback(void)
{
    uint32_t mask = MFDC_DCCM_WR_READBACK_DISABLE_MASK;

    __asm__ volatile ("csrs %0, %1"
                    :
                    : "i" (MFDC_CSR), "r" (mask)
                    : );

    if (!(read_mfdc() & MFDC_DCCM_WR_READBACK_DISABLE_MASK)) {
        printf("dwrd bit did not read back as set after disable!\n");
        putchar(TEST_FAILED);
    }
}

static void enable_dccm_wr_readback(void)
{
    uint32_t mask = MFDC_DCCM_WR_READBACK_DISABLE_MASK;

    __asm__ volatile ("csrc %0, %1"
                    :
                    : "i" (MFDC_CSR), "r" (mask)
                    : );

    if (read_mfdc() & MFDC_DCCM_WR_READBACK_DISABLE_MASK) {
        printf("dwrd bit did not read back as clear after enable!\n");
        putchar(TEST_FAILED);
    }
}

/* Word-aligned offsets spanning multiple DCCM banks (default DCCM_NUM_BANKS=4,
 * selected by address bits [3:2]), plus a spread of distinct bit patterns. */
static const uint32_t offsets[] = {0x0, 0x4, 0x8, 0xc, 0x100, 0x104, 0x108, 0x10c};
static const uint32_t patterns[] = {
    0x12345678, 0xdeadbeef, 0x00000000, 0xffffffff,
    0xa5a5a5a5, 0x5a5a5a5a, 0x00000001, 0x80000000
};

static void check_dccm_writes(const char *phase)
{
    volatile uint32_t *dccm;
    volatile uint8_t  *dccm_b;
    volatile uint16_t *dccm_h;
    uint32_t val;
    int i;

    printf("Checking DCCM writes (%s)\n", phase);

    for (i = 0; i < 8; i++) {
        dccm = (volatile uint32_t *)(DCCM_SADDR + offsets[i]);
        *dccm = patterns[i];
    }

    for (i = 0; i < 8; i++) {
        dccm = (volatile uint32_t *)(DCCM_SADDR + offsets[i]);
        val = *dccm;
        if (val != patterns[i]) {
            printf("Word mismatch at offset 0x%x (%s): wrote 0x%x, read 0x%x\n",
                   offsets[i], phase, patterns[i], val);
            putchar(TEST_FAILED);
        }
    }

    /* Also exercise the byte/half-word read-modify-write store path,
     * distinct from the aligned word stores above. */
    dccm_b = (volatile uint8_t *)(DCCM_SADDR + 0x200);
    dccm_h = (volatile uint16_t *)(DCCM_SADDR + 0x204);

    *dccm_b = 0x5a;
    *dccm_h = 0xbeef;

    if (*dccm_b != 0x5a) {
        printf("Byte mismatch (%s)\n", phase);
        putchar(TEST_FAILED);
    }
    if (*dccm_h != 0xbeef) {
        printf("Half-word mismatch (%s)\n", phase);
        putchar(TEST_FAILED);
    }

    printf("DCCM writes OK (%s)\n\n", phase);
}

void trap_handler(void)
{
    printf("Unexpected trap!\n");
    putchar(TEST_FAILED);
}

void main(void)
{
    printf("----------------------------------------\n");
    printf("Test DCCM write-readback enable/disable\n");
    printf("----------------------------------------\n\n");

    printf("Disabling DCCM write-readback check (dwrd=1)\n");
    disable_dccm_wr_readback();
    check_dccm_writes("readback disabled");

    printf("Enabling DCCM write-readback check (dwrd=0)\n");
    enable_dccm_wr_readback();
    check_dccm_writes("readback enabled");

    printf("Finished\n");
}
