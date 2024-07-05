#include <stdio.h>
#include <stdint.h>
#include <string.h>

#define _read_csr(csr) ({ \
    unsigned long res; \
    asm volatile ("csrr %0, " #csr : "=r"(res)); \
    res; \
})

#define _write_csr(csr, val) { \
    asm volatile ("csrw " #csr ", %0" : : "r"(val)); \
}

#define MISA_U (1 << 20)

#define MAGIC 0xDEADBEEF

struct csr_t {
    uint32_t    addr;
    const char* name;
};

static const struct csr_t g_read_csrs[] = {

    {0xF11, "mvendorid"},
    {0xF12, "marchid"},
    {0xF13, "mimpid"},
    {0xF14, "mhartid"},

    {0x300, "mstatus"},
    {0x301, "misa"},
    {0x304, "mie"},
    {0x305, "mtvec"},

    {0x306, "mcounteren"},
    {0x320, "mcountinhibit"},

    {0x340, "mscratch"},
    {0x341, "mepc"},
    {0x342, "mcause"},
    {0x343, "mtval"},
    {0x344, "mip"},

    {0xB00, "mcycle"},
    {0xB02, "minstret"},
    {0xB80, "mcycleh"},
    {0xB82, "minstreth"},

    {0x30A, "menvcfg"},
    {0x31A, "menvcfgh"},

    {0x747, "mseccfg"},
    {0x757, "mseccfgh"},

    // PMP
    {0x3A0, "pmpcfg0"},
    {0x3B0, "pmpaddr0"},
    {0x3C0, "pmpaddr16"},
    {0x3D0, "pmpaddr32"},
    {0x3E0, "pmpaddr48"},

    {0xC00, "cycle"},
    {0xC80, "cycleh"},
    {0xC02, "instret"},
    {0xC82, "instreth"},

    // VeeR specific CSRs
    {0x7FF, "mscause"},
    {0xBC0, "mdeau"},
    {0xFC0, "mdseac"},
    {0xBC8, "meivt"},
    {0xFC8, "meihap"},
    {0xBC9, "meipt"},
//    {0xBCA, "meicpct"}, // This one seems to be readable only when an interrupt is pending
    {0xBCC, "meicurpl"},
    {0xBCB, "meicidpl"},
//    {0x7B0, "dcsr"},  // These are accessible only when the core is halted
//    {0x7B1, "dpc"},
//    {0x7C4, "dmst"},
//    {0x7C8, "dicawics"},
//    {0x7CC, "dicad0h"},
//    {0x7C9, "dicad0"},
//    {0x7CA, "dicad1"},
//    {0x7CB, "dicago"},
    {0x7A0, "mtsel"},
    {0x7A1, "mtdata1"},
    {0x7A2, "mtdata2"},
    {0x7C0, "mrac"},
    {0xB03, "mhpmc3"},
    {0xB04, "mhpmc4"},
    {0xB05, "mhpmc5"},
    {0xB06, "mhpmc6"},
    {0xB83, "mhpmc3h"},
    {0xB84, "mhpmc4h"},
    {0xB85, "mhpmc5h"},
    {0xB86, "mhpmc6h"},
    {0x323, "mhpme3"},
    {0x324, "mhpme4"},
    {0x325, "mhpme5"},
    {0x326, "mhpme6"},
    {0x7F0, "micect"},
    {0x7F1, "miccmect"},
    {0x7F2, "mdccmect"},
    {0x7C6, "mpmc"},
    {0x7F8, "mcgc"},
    {0x7C2, "mcpc"},
    {0x7F9, "mfdc"},
    {0x7D4, "mitctl0"},
    {0x7D7, "mitctl1"},
    {0x7D3, "mitb0"},
    {0x7D6, "mitb1"},
    {0x7D2, "mitcnt0"},
    {0x7D5, "mitcnt1"},
    {0xB07, "perfva"},
    {0xB08, "perfvb"},
    {0xB10, "perfvc"},
    {0xB87, "perfvd"},
    {0xB88, "perfve"},
    {0xB90, "perfvf"},
    {0x327, "perfvg"},
    {0x328, "perfvh"},
    {0x330, "perfvi"},
    {0x7CE, "mfdht"},
    {0x7CF, "mfdhs"}
};

static const struct csr_t g_write_csrs[] = {

    // Test write only for a few CSRs not to cause unwanted effects
    {0x304, "mie"},
    {0x340, "mscratch"},
    {0x30A, "menvcfg"},
    {0x31A, "menvcfgh"},
};

unsigned long read_csr (uint32_t addr) {

    // Define the result to be explicitly in register a0 - the return value
    // by the calling convention. Preset it to a magic value so that when
    // a CSR access fails the value stays there.
    volatile register uint32_t val asm("a0") = MAGIC;

    // Since RISC-V does not allow indirect CSR addressing there's a big
    // 'switch' to handle that.
    switch (addr) {

        case 0xF11: val = _read_csr(0xF11); break;
        case 0xF12: val = _read_csr(0xF12); break;
        case 0xF13: val = _read_csr(0xF13); break;
        case 0xF14: val = _read_csr(0xF14); break;

        case 0x300: val = _read_csr(0x300); break;
        case 0x301: val = _read_csr(0x301); break;
        case 0x304: val = _read_csr(0x304); break;
        case 0x305: val = _read_csr(0x305); break;
        case 0x306: val = _read_csr(0x306); break;

        case 0x30A: val = _read_csr(0x30A); break;
        case 0x31A: val = _read_csr(0x31A); break;

        case 0x320: val = _read_csr(0x320); break;

        case 0x340: val = _read_csr(0x340); break;
        case 0x341: val = _read_csr(0x341); break;
        case 0x342: val = _read_csr(0x342); break;
        case 0x343: val = _read_csr(0x343); break;
        case 0x344: val = _read_csr(0x344); break;

        case 0xB00: val = _read_csr(0xB00); break;
        case 0xB02: val = _read_csr(0xB02); break;
        case 0xB80: val = _read_csr(0xB80); break;
        case 0xB82: val = _read_csr(0xB82); break;

        case 0xC00: val = _read_csr(0xC00); break;
        case 0xC80: val = _read_csr(0xC80); break;
        case 0xC02: val = _read_csr(0xC02); break;
        case 0xC82: val = _read_csr(0xC82); break;

        case 0x3A0: val = _read_csr(0x3A0); break;
        case 0x3B0: val = _read_csr(0x3B0); break;
        case 0x3C0: val = _read_csr(0x3C0); break;
        case 0x3D0: val = _read_csr(0x3D0); break;
        case 0x3E0: val = _read_csr(0x3E0); break;

        case 0x747: val = _read_csr(0x747); break;
        case 0x757: val = _read_csr(0x757); break;

        case 0x7FF: val = _read_csr(0x7FF); break;
        case 0x7C0: val = _read_csr(0x7C0); break;
        case 0x7C4: val = _read_csr(0x7C4); break;
        case 0xBC0: val = _read_csr(0xBC0); break;
        case 0xFC0: val = _read_csr(0xFC0); break;
        case 0xBC8: val = _read_csr(0xBC8); break;
        case 0xFC8: val = _read_csr(0xFC8); break;
        case 0xBC9: val = _read_csr(0xBC9); break;
        case 0xBCA: val = _read_csr(0xBCA); break;
        case 0xBCC: val = _read_csr(0xBCC); break;
        case 0xBCB: val = _read_csr(0xBCB); break;
        case 0x7B0: val = _read_csr(0x7B0); break;
        case 0x7B1: val = _read_csr(0x7B1); break;
        case 0x7C8: val = _read_csr(0x7C8); break;
        case 0x7CC: val = _read_csr(0x7CC); break;
        case 0x7C9: val = _read_csr(0x7C9); break;
        case 0x7CA: val = _read_csr(0x7CA); break;
        case 0x7CB: val = _read_csr(0x7CB); break;
        case 0x7A0: val = _read_csr(0x7A0); break;
        case 0x7A1: val = _read_csr(0x7A1); break;
        case 0x7A2: val = _read_csr(0x7A2); break;
        case 0xB03: val = _read_csr(0xB03); break;
        case 0xB04: val = _read_csr(0xB04); break;
        case 0xB05: val = _read_csr(0xB05); break;
        case 0xB06: val = _read_csr(0xB06); break;
        case 0xB83: val = _read_csr(0xB83); break;
        case 0xB84: val = _read_csr(0xB84); break;
        case 0xB85: val = _read_csr(0xB85); break;
        case 0xB86: val = _read_csr(0xB86); break;
        case 0x323: val = _read_csr(0x323); break;
        case 0x324: val = _read_csr(0x324); break;
        case 0x325: val = _read_csr(0x325); break;
        case 0x326: val = _read_csr(0x326); break;
        case 0x7F0: val = _read_csr(0x7F0); break;
        case 0x7F1: val = _read_csr(0x7F1); break;
        case 0x7F2: val = _read_csr(0x7F2); break;
        case 0x7C6: val = _read_csr(0x7C6); break;
        case 0x7F8: val = _read_csr(0x7F8); break;
        case 0x7C2: val = _read_csr(0x7C2); break;
        case 0x7F9: val = _read_csr(0x7F9); break;
        case 0x7D4: val = _read_csr(0x7D4); break;
        case 0x7D7: val = _read_csr(0x7D7); break;
        case 0x7D3: val = _read_csr(0x7D3); break;
        case 0x7D6: val = _read_csr(0x7D6); break;
        case 0x7D2: val = _read_csr(0x7D2); break;
        case 0x7D5: val = _read_csr(0x7D5); break;
        case 0xB07: val = _read_csr(0xB07); break;
        case 0xB08: val = _read_csr(0xB08); break;
        case 0xB10: val = _read_csr(0xB10); break;
        case 0xB87: val = _read_csr(0xB87); break;
        case 0xB88: val = _read_csr(0xB88); break;
        case 0xB90: val = _read_csr(0xB90); break;
        case 0x327: val = _read_csr(0x327); break;
        case 0x328: val = _read_csr(0x328); break;
        case 0x330: val = _read_csr(0x330); break;
        case 0x7CE: val = _read_csr(0x7CE); break;
        case 0x7CF: val = _read_csr(0x7CF); break;
    }

    return val;
}

void write_csr (uint32_t addr, uint32_t val) {

    // Since RISC-V does not allow indirect CSR addressing there's a big
    // 'switch' to handle that.

    switch (addr) {
        case 0x304: _write_csr(0x304, val); return;
        case 0x306: _write_csr(0x306, val); return;

        case 0x30A: _write_csr(0x30A, val); return;
        case 0x31A: _write_csr(0x31A, val); return;

        case 0x340: _write_csr(0x340, val); return;

        // The test verifies writes to just a handful of CSRs so not all of
        // them are mentioned here
    }

    // Unknown address
    _write_csr(0xFFF, 0);
}

volatile unsigned long last_trap  = 0xFFFFFFFF;
volatile unsigned long fail_count = 0;

void test_csr_read_access (uint8_t user_mode) {

    int  ok;

    // Loop over all implemented CSRs and try reading them.
    for (size_t i=0; i < sizeof(g_read_csrs) / sizeof(g_read_csrs[0]); ++i) {
        const struct csr_t* csr = &g_read_csrs[i];

        // Attempt CSR read
        last_trap = 0xFFFFFFFF;
        volatile unsigned long val = read_csr(csr->addr);

        // In user mode only unprivileged / user CSRs should be readable.
        // Accessing others should yield in illegal instruction exception
        if (user_mode) {
            if ((csr->addr & 0x300) == 0) { // Unprivileged / user
                ok = (last_trap == 0xFFFFFFFF);
            } else {
                ok = (last_trap == 0x2);

                // If the access failed check if the read was actually terminated
                if (ok && val != MAGIC) {
                    printf("0x%08X\n", val);
                    ok = 0;
                }
            }
        }
        // In machine mode all CSRs should be readable
        else {
            ok = (last_trap == 0xFFFFFFFF);
        }

        // Count fails
        fail_count += !ok;
        printf("%s 0x%03X '%s'\n", ok ? "[  OK  ]" : "[ FAIL ]", csr->addr, csr->name);
    }

}

void test_csr_write_access (uint8_t user_mode) {

    int  ok = 1;

    // Loop over all implemented CSRs and try writing them.
    for (size_t i=0; i < sizeof(g_write_csrs) / sizeof(g_write_csrs[0]); ++i) {
        const struct csr_t* csr = &g_write_csrs[i];

        // Attempt CSR write
        last_trap = 0xFFFFFFFF;
        write_csr(csr->addr, 0);

        // In user mode only unprivileged / user CSRs should be writable.
        // Accessing others should yield in illegal instruction exception
        if (user_mode) {
            if ((csr->addr & 0x300) == 0) { // Unprivileged / user
                ok = (last_trap == 0xFFFFFFFF);
            } else {
                ok = (last_trap == 0x2);
            }
        }
        // In machine mode all CSRs should be readable
        else {
            ok = (last_trap == 0xFFFFFFFF);
        }

        // Count fails
        fail_count += !ok;
        printf("%s 0x%03X '%s'\n", ok ? "[  OK  ]" : "[ FAIL ]", csr->addr, csr->name);
    }
}

void user_main ();
void machine_main ();

void trap_handler () {

    unsigned long mstatus = _read_csr(mstatus);
    unsigned long mcause  = _read_csr(mcause);
    printf("trap! mstatus=0x%08X, mcause=0x%08X\n", mstatus, mcause);

    // Store trap cause
    last_trap = mcause;

    // If the trap cause is ECALL.U return to machine_main()
    if (mcause == 0x08) {
        void* ptr = (void*)machine_main;
        _write_csr(mepc, (unsigned long)ptr - 4); // -4 as the trap handler advances mepc
        _write_csr(mstatus, mstatus | (3 << 11)); // MPP=11 (M-mode)
    }
}

int main () {
    printf("\nHello VeeR\n");

    // The test requires user mode support
    if ((_read_csr(misa) & MISA_U) == 0) {
        printf("ERROR: The test requires user mode support. Aborting.\n");
        return -1;
    }
 
    // Test CSR access assuming machine mode
    printf("Testing CSR read...\n");
    test_csr_read_access(0);
    printf("Testing CSR write...\n");
    test_csr_write_access(0);

    // Write mcounteren.CY and mcounteren.IR to allow access cycle and instret
    // from user mode
    _write_csr(0x306, 0x5);

    // Clear mscratch
    _write_csr(mscratch, 0);

    // Go to user mode
    unsigned long mstatus = _read_csr(mstatus);
    mstatus &= ~(3 << 11);  // MPP  = 00 (user)
    mstatus &= ~(1 << 17);  // MPRV = 0
    _write_csr(mstatus, mstatus);

    void* ptr = (void*)user_main;
    _write_csr(mepc, (unsigned long)ptr);
    asm volatile ("mret");

    return 0;
}

__attribute__((noreturn)) void user_main () {
    printf("\nHello from user_main()\n");

    // Test CSR access assuming user mode
    printf("Testing CSR read...\n");
    test_csr_read_access(1);
    printf("Testing CSR write...\n");
    test_csr_write_access(1);

    // Try writing something to mscratch. Ignore exception, later the CSR is
    // to be read back from machine mode
    printf("Attempting to write mscratch...\n");
    _write_csr(mscratch, MAGIC);

    // Trigger an ECALL to go to machine mode again
    asm volatile ("ecall");

    while (1); // Make compiler not complain
}

__attribute__((noreturn)) void machine_main () {
    printf("\nHello from machine_main()\n");

    // Check mscratch. It should not contain the pattern written from user mode
    printf("Reading mscratch...\n");
    unsigned long mscratch = _read_csr(mscratch);
    if (mscratch == MAGIC) {
        fail_count++;
        printf("[ FAIL ] previous write succeeded while it shouldn't\n");
    } else {
        printf("[  OK  ]\n");
    }
    printf("\n");

    // Terminate the simulation
    // set the exit code to 0xFF / 0x01 and jump to _finish.
    unsigned long res = (fail_count == 0) ? 0xFF : 0x01;
    asm volatile (
        "mv a0, %0\n"
        "j  _finish\n"
        : : "r"(res)
    );

    while (1); // Make compiler not complain
}
