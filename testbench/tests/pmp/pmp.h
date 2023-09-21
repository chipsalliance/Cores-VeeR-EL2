#include <stdint.h>

#define PMP_LOCK  (1<<7)
#define PMP_OFF   (0<<3)
#define PMP_TOR   (1<<3)
#define PMP_NA4   (2<<3)
#define PMP_NAPOT (3<<3)
#define PMP_X     (1<<2)
#define PMP_W     (1<<1)
#define PMP_R     (1<<0)

#define CSR_PMPCFG_BASE 0x3A0
#define CSR_PMPADDR_BASE 0x3B0

#define CSRR_READ(v, csr)                       \
/* CSRR_READ(v, csr): \
 * csr: MUST be a compile time integer 12-bit constant (0-4095) \
 */                                             \
__asm__ __volatile__ ("csrr %0, %1"             \
              : "=r" (v)                        \
              : "n" (csr)                       \
              : /* clobbers: none */ )

#define CSRR_WRITE(v, csr)                      \
/* CSRR_WRITE(v, csr): \
 * csr: MUST be a compile time integer 12-bit constant (0-4095) \
 */                                             \
__asm__ __volatile__ ("csrw %0, %1"             \
              :                                 \
              : "n" (csr), "rK" (v)             \
              : /* clobbers: none */ )

struct pmp_entry_s {
    uintptr_t addr;
    uint8_t cfg;
};

int pmp_read_pmpcfg(unsigned int offset, uintptr_t * dest);
int pmp_read_pmpaddr(unsigned int offset, uintptr_t * dest);
int pmp_write_pmpcfg(unsigned int offset, uintptr_t * src);
int pmp_write_pmpaddr(unsigned int offset, uintptr_t * src);
int pmp_entry_read(unsigned int id, struct pmp_entry_s * entry);
int pmp_entry_write(unsigned int id, struct pmp_entry_s * entry);
