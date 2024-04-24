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

    // PMP
    {0x3A0, "pmpcfg0"},
    {0x3B0, "pmpaddr0"},
    {0x3C0, "pmpaddr16"},
    {0x3D0, "pmpaddr32"},
    {0x3E0, "pmpaddr48"},

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
    {0x340, "mscratch"}
};

unsigned long read_csr (uint32_t addr) {

    // Since RISC-V does not allow indirect CSR addressing there's a big
    // 'switch' to handle that.

    switch (addr) {

        case 0xF11: return _read_csr(0xF11);
        case 0xF12: return _read_csr(0xF12);
        case 0xF13: return _read_csr(0xF13);
        case 0xF14: return _read_csr(0xF14);

        case 0x300: return _read_csr(0x300);
        case 0x301: return _read_csr(0x301);
        case 0x304: return _read_csr(0x304);
        case 0x305: return _read_csr(0x305);

        case 0x320: return _read_csr(0x320);

        case 0x340: return _read_csr(0x340);
        case 0x341: return _read_csr(0x341);
        case 0x342: return _read_csr(0x342);
        case 0x343: return _read_csr(0x343);
        case 0x344: return _read_csr(0x344);

        case 0xB00: return _read_csr(0xB00);
        case 0xB02: return _read_csr(0xB02);
        case 0xB80: return _read_csr(0xB80);
        case 0xB82: return _read_csr(0xB82);

        case 0x3A0: return _read_csr(0x3A0);
        case 0x3B0: return _read_csr(0x3B0);
        case 0x3C0: return _read_csr(0x3C0);
        case 0x3D0: return _read_csr(0x3D0);
        case 0x3E0: return _read_csr(0x3E0);

        case 0x7FF: return _read_csr(0x7FF);
        case 0x7C0: return _read_csr(0x7C0);
        case 0x7C4: return _read_csr(0x7C4);
        case 0xBC0: return _read_csr(0xBC0);
        case 0xFC0: return _read_csr(0xFC0);
        case 0xBC8: return _read_csr(0xBC8);
        case 0xFC8: return _read_csr(0xFC8);
        case 0xBC9: return _read_csr(0xBC9);
        case 0xBCA: return _read_csr(0xBCA);
        case 0xBCC: return _read_csr(0xBCC);
        case 0xBCB: return _read_csr(0xBCB);
        case 0x7B0: return _read_csr(0x7B0);
        case 0x7B1: return _read_csr(0x7B1);
        case 0x7C8: return _read_csr(0x7C8);
        case 0x7CC: return _read_csr(0x7CC);
        case 0x7C9: return _read_csr(0x7C9);
        case 0x7CA: return _read_csr(0x7CA);
        case 0x7CB: return _read_csr(0x7CB);
        case 0x7A0: return _read_csr(0x7A0);
        case 0x7A1: return _read_csr(0x7A1);
        case 0x7A2: return _read_csr(0x7A2);
        case 0xB03: return _read_csr(0xB03);
        case 0xB04: return _read_csr(0xB04);
        case 0xB05: return _read_csr(0xB05);
        case 0xB06: return _read_csr(0xB06);
        case 0xB83: return _read_csr(0xB83);
        case 0xB84: return _read_csr(0xB84);
        case 0xB85: return _read_csr(0xB85);
        case 0xB86: return _read_csr(0xB86);
        case 0x323: return _read_csr(0x323);
        case 0x324: return _read_csr(0x324);
        case 0x325: return _read_csr(0x325);
        case 0x326: return _read_csr(0x326);
        case 0x7F0: return _read_csr(0x7F0);
        case 0x7F1: return _read_csr(0x7F1);
        case 0x7F2: return _read_csr(0x7F2);
        case 0x7C6: return _read_csr(0x7C6);
        case 0x7F8: return _read_csr(0x7F8);
        case 0x7C2: return _read_csr(0x7C2);
        case 0x7F9: return _read_csr(0x7F9);
        case 0x7D4: return _read_csr(0x7D4);
        case 0x7D7: return _read_csr(0x7D7);
        case 0x7D3: return _read_csr(0x7D3);
        case 0x7D6: return _read_csr(0x7D6);
        case 0x7D2: return _read_csr(0x7D2);
        case 0x7D5: return _read_csr(0x7D5);
        case 0xB07: return _read_csr(0xB07);
        case 0xB08: return _read_csr(0xB08);
        case 0xB10: return _read_csr(0xB10);
        case 0xB87: return _read_csr(0xB87);
        case 0xB88: return _read_csr(0xB88);
        case 0xB90: return _read_csr(0xB90);
        case 0x327: return _read_csr(0x327);
        case 0x328: return _read_csr(0x328);
        case 0x330: return _read_csr(0x330);
        case 0x7CE: return _read_csr(0x7CE);
        case 0x7CF: return _read_csr(0x7CF);
    }

    // Unknown address
    return _read_csr(0xFFF);
}

void write_csr (uint32_t addr, uint32_t val) {

    // Since RISC-V does not allow indirect CSR addressing there's a big
    // 'switch' to handle that.

    switch (addr) {
        case 0x304: _write_csr(0x304, val); return;
        case 0x306: _write_csr(0x306, val); return;

        case 0x340: _write_csr(0x340, val); return;
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
        unsigned long val = read_csr(csr->addr);

        // In user mode only unprivileged / user CSRs should be readable.
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

void test_csr_write_access (uint8_t user_mode) {

    int  ok = 1;

    // Loop over all implemented CSRs and try reading them.
    for (size_t i=0; i < sizeof(g_write_csrs) / sizeof(g_write_csrs[0]); ++i) {
        const struct csr_t* csr = &g_write_csrs[i];

        // Attempt CSR write
        last_trap = 0xFFFFFFFF;
        write_csr(csr->addr, 0);

        // In user mode only unprivileged / user CSRs should be readable.
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

void trap_handler () {

    unsigned long mstatus = _read_csr(mstatus);
    unsigned long mcause  = _read_csr(mcause);
    printf("trap! mstatus=0x%08X, mcause=0x%08X\n", mstatus, mcause);

    // Store trap cause
    last_trap = mcause;
}

void user_main ();

__attribute__((noreturn)) void main () {
    printf("\nHello VeeR\n");
 
    // Test CSR access assuming machine mode
    printf("Testing CSR read...\n");
    test_csr_read_access(0);
    printf("Testing CSR write...\n");
    test_csr_write_access(0);

    // Go to user mode
    unsigned long mstatus = _read_csr(mstatus);
    mstatus &= ~(3 << 11);  // MPP  = 00 (user)
    mstatus &= ~(1 << 17);  // MPRV = 0
    _write_csr(mstatus, mstatus);

    void* ptr = (void*)user_main;
    _write_csr(mepc, (unsigned long)ptr);
    asm volatile ("mret");
}

__attribute__((noreturn)) void user_main () {
    printf("\nHello from user_main()\n");

    // Test CSR access assuming user mode
    printf("Testing CSR read...\n");
    test_csr_read_access(1);
    printf("Testing CSR write...\n");
    test_csr_write_access(1);
    printf("\n");

    // Terminate the simulation
    // set the exit code to 0xFF / 0x01 and jump to _finish.
    unsigned long res = (fail_count == 0) ? 0xFF : 0x01;
    asm volatile (
        "mv a0, %0\n"
        "j  _finish\n"
        : : "r"(res)
    );
}
