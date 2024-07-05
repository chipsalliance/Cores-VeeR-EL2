#include <stdint.h>
#include "pmp.h"

int pmp_clear ()
{
    const int pmp_entries = 16; // FIXME: Parametrize that

    uintptr_t zero = 0;
    int res = 0;

    for (int i=0; i<(pmp_entries + 3)/4; ++i) {
        if (pmp_write_pmpcfg(i, &zero)) {
            res = -1;
        }
    }
    for (int i=0; i<pmp_entries; ++i) {
        if (pmp_write_pmpaddr(i, &zero)) {
            res = -1;
        }
    }

    return res;
}

int pmp_read_pmpcfg(unsigned int offset, uintptr_t * dest)
{
    uintptr_t csr_value;

    if (!dest) return 1;

    switch (offset) {
        case 0x0: CSRR_READ(csr_value, CSR_PMPCFG_BASE + 0x0); break;
        case 0x1: CSRR_READ(csr_value, CSR_PMPCFG_BASE + 0x1); break;
        case 0x2: CSRR_READ(csr_value, CSR_PMPCFG_BASE + 0x2); break;
        case 0x3: CSRR_READ(csr_value, CSR_PMPCFG_BASE + 0x3); break;
        case 0x4: CSRR_READ(csr_value, CSR_PMPCFG_BASE + 0x4); break;
        case 0x5: CSRR_READ(csr_value, CSR_PMPCFG_BASE + 0x5); break;
        case 0x6: CSRR_READ(csr_value, CSR_PMPCFG_BASE + 0x6); break;
        case 0x7: CSRR_READ(csr_value, CSR_PMPCFG_BASE + 0x7); break;
        case 0x8: CSRR_READ(csr_value, CSR_PMPCFG_BASE + 0x8); break;
        case 0x9: CSRR_READ(csr_value, CSR_PMPCFG_BASE + 0x9); break;
        case 0xA: CSRR_READ(csr_value, CSR_PMPCFG_BASE + 0xA); break;
        case 0xB: CSRR_READ(csr_value, CSR_PMPCFG_BASE + 0xB); break;
        case 0xC: CSRR_READ(csr_value, CSR_PMPCFG_BASE + 0xC); break;
        case 0xD: CSRR_READ(csr_value, CSR_PMPCFG_BASE + 0xD); break;
        case 0xE: CSRR_READ(csr_value, CSR_PMPCFG_BASE + 0xE); break;
        case 0xF: CSRR_READ(csr_value, CSR_PMPCFG_BASE + 0xF); break;
        default: return 2; break;
    }

    (*dest) = csr_value;

    return 0;
}

int pmp_read_pmpaddr(unsigned int offset, uintptr_t * dest)
{
    uintptr_t csr_value;

    if (!dest) return 1;

    switch (offset) {
        case 0x00: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x00); break;
        case 0x01: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x01); break;
        case 0x02: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x02); break;
        case 0x03: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x03); break;
        case 0x04: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x04); break;
        case 0x05: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x05); break;
        case 0x06: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x06); break;
        case 0x07: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x07); break;
        case 0x08: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x08); break;
        case 0x09: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x09); break;
        case 0x0A: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x0A); break;
        case 0x0B: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x0B); break;
        case 0x0C: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x0C); break;
        case 0x0D: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x0D); break;
        case 0x0E: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x0E); break;
        case 0x0F: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x0F); break;

        case 0x10: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x10); break;
        case 0x11: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x11); break;
        case 0x12: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x12); break;
        case 0x13: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x13); break;
        case 0x14: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x14); break;
        case 0x15: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x15); break;
        case 0x16: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x16); break;
        case 0x17: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x17); break;
        case 0x18: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x18); break;
        case 0x19: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x19); break;
        case 0x1A: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x1A); break;
        case 0x1B: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x1B); break;
        case 0x1C: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x1C); break;
        case 0x1D: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x1D); break;
        case 0x1E: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x1E); break;
        case 0x1F: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x1F); break;

        case 0x20: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x20); break;
        case 0x21: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x21); break;
        case 0x22: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x22); break;
        case 0x23: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x23); break;
        case 0x24: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x24); break;
        case 0x25: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x25); break;
        case 0x26: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x26); break;
        case 0x27: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x27); break;
        case 0x28: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x28); break;
        case 0x29: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x29); break;
        case 0x2A: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x2A); break;
        case 0x2B: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x2B); break;
        case 0x2C: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x2C); break;
        case 0x2D: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x2D); break;
        case 0x2E: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x2E); break;
        case 0x2F: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x2F); break;

        case 0x30: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x30); break;
        case 0x31: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x31); break;
        case 0x32: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x32); break;
        case 0x33: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x33); break;
        case 0x34: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x34); break;
        case 0x35: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x35); break;
        case 0x36: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x36); break;
        case 0x37: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x37); break;
        case 0x38: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x38); break;
        case 0x39: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x39); break;
        case 0x3A: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x3A); break;
        case 0x3B: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x3B); break;
        case 0x3C: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x3C); break;
        case 0x3D: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x3D); break;
        case 0x3E: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x3E); break;
        case 0x3F: CSRR_READ(csr_value, CSR_PMPADDR_BASE + 0x3F); break;

        default: return 2; break;
    }

    (*dest) = csr_value;

    return 0;
}

int pmp_write_pmpcfg(unsigned int offset, uintptr_t * src)
{
    uintptr_t csr_value;

    if (!src) return 1;

    csr_value = (*src);

    switch (offset) {
        case 0x0: CSRR_WRITE(csr_value, CSR_PMPCFG_BASE + 0x0); break;
        case 0x1: CSRR_WRITE(csr_value, CSR_PMPCFG_BASE + 0x1); break;
        case 0x2: CSRR_WRITE(csr_value, CSR_PMPCFG_BASE + 0x2); break;
        case 0x3: CSRR_WRITE(csr_value, CSR_PMPCFG_BASE + 0x3); break;
        case 0x4: CSRR_WRITE(csr_value, CSR_PMPCFG_BASE + 0x4); break;
        case 0x5: CSRR_WRITE(csr_value, CSR_PMPCFG_BASE + 0x5); break;
        case 0x6: CSRR_WRITE(csr_value, CSR_PMPCFG_BASE + 0x6); break;
        case 0x7: CSRR_WRITE(csr_value, CSR_PMPCFG_BASE + 0x7); break;
        case 0x8: CSRR_WRITE(csr_value, CSR_PMPCFG_BASE + 0x8); break;
        case 0x9: CSRR_WRITE(csr_value, CSR_PMPCFG_BASE + 0x9); break;
        case 0xA: CSRR_WRITE(csr_value, CSR_PMPCFG_BASE + 0xA); break;
        case 0xB: CSRR_WRITE(csr_value, CSR_PMPCFG_BASE + 0xB); break;
        case 0xC: CSRR_WRITE(csr_value, CSR_PMPCFG_BASE + 0xC); break;
        case 0xD: CSRR_WRITE(csr_value, CSR_PMPCFG_BASE + 0xD); break;
        case 0xE: CSRR_WRITE(csr_value, CSR_PMPCFG_BASE + 0xE); break;
        case 0xF: CSRR_WRITE(csr_value, CSR_PMPCFG_BASE + 0xF); break;

        default: return 2; break;
    }

    return 0;
}

int pmp_write_pmpaddr(unsigned int offset, uintptr_t * src)
{
    uintptr_t csr_value;

    if (!src) return 1;

    csr_value = (*src);

    switch (offset) {
        case 0x00: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x00); break;
        case 0x01: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x01); break;
        case 0x02: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x02); break;
        case 0x03: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x03); break;
        case 0x04: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x04); break;
        case 0x05: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x05); break;
        case 0x06: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x06); break;
        case 0x07: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x07); break;
        case 0x08: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x08); break;
        case 0x09: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x09); break;
        case 0x0A: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x0A); break;
        case 0x0B: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x0B); break;
        case 0x0C: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x0C); break;
        case 0x0D: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x0D); break;
        case 0x0E: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x0E); break;
        case 0x0F: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x0F); break;

        case 0x10: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x10); break;
        case 0x11: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x11); break;
        case 0x12: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x12); break;
        case 0x13: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x13); break;
        case 0x14: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x14); break;
        case 0x15: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x15); break;
        case 0x16: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x16); break;
        case 0x17: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x17); break;
        case 0x18: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x18); break;
        case 0x19: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x19); break;
        case 0x1A: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x1A); break;
        case 0x1B: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x1B); break;
        case 0x1C: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x1C); break;
        case 0x1D: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x1D); break;
        case 0x1E: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x1E); break;
        case 0x1F: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x1F); break;

        case 0x20: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x20); break;
        case 0x21: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x21); break;
        case 0x22: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x22); break;
        case 0x23: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x23); break;
        case 0x24: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x24); break;
        case 0x25: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x25); break;
        case 0x26: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x26); break;
        case 0x27: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x27); break;
        case 0x28: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x28); break;
        case 0x29: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x29); break;
        case 0x2A: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x2A); break;
        case 0x2B: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x2B); break;
        case 0x2C: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x2C); break;
        case 0x2D: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x2D); break;
        case 0x2E: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x2E); break;
        case 0x2F: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x2F); break;

        case 0x30: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x30); break;
        case 0x31: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x31); break;
        case 0x32: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x32); break;
        case 0x33: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x33); break;
        case 0x34: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x34); break;
        case 0x35: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x35); break;
        case 0x36: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x36); break;
        case 0x37: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x37); break;
        case 0x38: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x38); break;
        case 0x39: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x39); break;
        case 0x3A: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x3A); break;
        case 0x3B: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x3B); break;
        case 0x3C: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x3C); break;
        case 0x3D: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x3D); break;
        case 0x3E: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x3E); break;
        case 0x3F: CSRR_WRITE(csr_value, CSR_PMPADDR_BASE + 0x3F); break;

        default: return 2; break;
    }

    return 0;
}

int pmp_entry_read(unsigned int id, struct pmp_entry_s * entry)
{
    unsigned int pmpcfg_id_coarse = (id >> 2) & ((__riscv_xlen == 32) ? (~0) : (~1));
    unsigned int pmpcfg_id_fine = id & ((__riscv_xlen == 32) ? 3 : 7);

    uintptr_t pmpcfg_csr;
    uintptr_t pmpaddr_csr;

    /* One PMPCFGx register contains configuration
     * for 4 entries (RV32) or 8 entries (RV64).
     */

    if (!entry) return 1;
    if (id > 64) return 2;

    /* Read PMPADDRx CSR */
    if (pmp_read_pmpaddr(id, &pmpaddr_csr) != 0) return 3;

    /* Read PMPCFGx CSR */
    if (pmp_read_pmpcfg(pmpcfg_id_coarse, &pmpcfg_csr) != 0) return 4;

    entry->addr = pmpaddr_csr;
    entry->cfg = (pmpcfg_csr >> (8 * pmpcfg_id_fine)) & 0xff;

    return 0;
}

int pmp_entry_write(unsigned int id, struct pmp_entry_s * entry)
{
    unsigned int pmpcfg_id_coarse = (id >> 2) & ((__riscv_xlen == 32) ? (~0) : (~1));
    unsigned int pmpcfg_id_fine = id & ((__riscv_xlen == 32) ? 3 : 7);

    unsigned int pmpcfg_csr;
    unsigned int pmpaddr_csr;

    /* One PMPCFGx register contains configuration
     * for 4 entries (RV32) or 8 entries (RV64).
     */

    if (!entry) return 1;
    if (id > 64) return 2;

    /* Write entry to PMPADDRx CSR */
    pmpaddr_csr = entry->addr;
    if (pmp_write_pmpaddr(id, &pmpaddr_csr) != 0) return 3;

    /* Write entry to PMPCFGx CSR. Other entries in the same CSR are left intact */
    if (pmp_read_pmpcfg(pmpcfg_id_coarse, &pmpcfg_csr) != 0) return 4;
    pmpcfg_csr = pmpcfg_csr & (~(0xff << (pmpcfg_id_fine * 8))) | (entry->cfg << (pmpcfg_id_fine * 8));
    if (pmp_write_pmpcfg(pmpcfg_id_coarse, &pmpcfg_csr) != 0) return 5;

    return 0;
}

int pmp_is_cfg_legal (unsigned int cfg) {
    // Check if RWX combination is legal according to
    // RISC-V privilege spec v1.12 chapter 3.7.1

    cfg &= (PMP_R | PMP_W | PMP_X);

    if (cfg == (PMP_W))
        return 0;
    if (cfg == (PMP_W | PMP_X))
        return 0;

    return 1;
}
