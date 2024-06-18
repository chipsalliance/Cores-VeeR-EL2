//-----------------------------------------------------------------------------
// Processor feature configuration
//-----------------------------------------------------------------------------
//
parameter int XLEN = 32;
parameter satp_mode_t SATP_MODE = BARE;
privileged_mode_t supported_privileged_mode[] = {MACHINE_MODE, USER_MODE};

// NOTE: To get supported and unsupported instructions compare
// riscv-dv/src/riscv_instr_pkg.sv and Cores-VeeR-EL2/design/dec/decode files

// Unsupported instructions
riscv_instr_name_t unsupported_instr[] = {
    NOP, // RV32I
    CLZ, // RV32ZBB
    SROI, CMIX, FSRI, FSR, CMOV, SRO, SLO, FSL, SLOI, // RV32B
    // FIXME: As of date, the decision on which bitmanip extensions should go
    // into the `B` collection is not yet ratified.
    //
    // To stay on the safe side, let's assume here that *all of them* are
    // enabled by the `B` extension collection.
    CRC32C_B, CRC32C_H, CRC32C_W, CRC32_B, CRC32_H, CRC32_W, // RV32ZBR
    GORC, GORCI, GREV, GREVI, SHFL, SHFLI, UNSHFL, UNSHFLI, // RV32ZBP
    BCOMPRESS, BDECOMPRESS, // RV32ZBE
    BFP, // RV32ZBF
    XPERM_B, XPERM_H, XPERM_N // RV32ZBP
};

// ISA supported by the processor
riscv_instr_group_t supported_isa[$] = {
    RV32I,
    RV32M,
    RV32C,
    RV32B,
    RV32ZBA,
    RV32ZBB,
    RV32ZBC,
    RV32ZBS
};

// Interrupt mode support
mtvec_mode_t supported_interrupt_mode[$] = {DIRECT, VECTORED};

// The number of interrupt vectors to be generated, only used if VECTORED interrupt mode is supported
int max_interrupt_vector_num = 16;

// Physical memory protection support
bit support_pmp = 1;

// Enhanced physical memory protection support
// NOTE: Not supported by VeeR, described in:
// https://raw.githubusercontent.com/riscv/riscv-tee/main/Smepmp/Smepmp.pdf
bit support_epmp = 0;

// Debug mode support
bit support_debug_mode = 0;

// Support delegate trap to user mode
// When implementing UCAUSE, UTVEC, UTVAL, UEPC, USCRATCH, USTATUS, UIE, UIP
bit support_umode_trap = 0;

// Support sfence.vma instruction
bit support_sfence = 0;

// Support unaligned load/store
bit support_unaligned_load_store = 1'b1;

// GPR setting
parameter int NUM_FLOAT_GPR = 32;
parameter int NUM_GPR = 32;
parameter int NUM_VEC_GPR = 32;

// ----------------------------------------------------------------------------
// Vector extension configuration
// ----------------------------------------------------------------------------
// Parameter for vector extension
parameter int VECTOR_EXTENSION_ENABLE = 0;

parameter int VLEN = 512;

// Maximum size of a single vector element
parameter int ELEN = 32;

// Minimum size of a sub-element, which must be at most 8-bits.
parameter int SELEN = 8;

// Maximum size of a single vector element (encoded in vsew format)
parameter int VELEN = int'($ln(ELEN)/$ln(2)) - 3;

// Maxium LMUL supported by the core
parameter int MAX_LMUL = 8;
// ----------------------------------------------------------------------------
// Multi-harts configuration
// ----------------------------------------------------------------------------

// Number of harts
parameter int NUM_HARTS = 1;

// ----------------------------------------------------------------------------
// Previleged CSR implementation
// ----------------------------------------------------------------------------

// Implemented previlieged CSR list
`ifdef DSIM
privileged_reg_t implemented_csr[] = {
`else
const privileged_reg_t implemented_csr[] = {
`endif
    MARCHID,
    MIMPID,
    MHARTID,
    MSTATUS,
    MTVEC,
    MIP,
    MIE,
    MCYCLE,
    MCYCLEH,
    MINSTRET,
    MINSTRETH,
    MSCRATCH,
    MEPC,
    MCAUSE,
    MTVAL,
    DCSR,
    DPC,
    TSELECT,
    TDATA1,
    TDATA2,
    MHPMCOUNTER3,
    MHPMCOUNTER4,
    MHPMCOUNTER5,
    MHPMCOUNTER6,
    MHPMCOUNTER3H,
    MHPMCOUNTER4H,
    MHPMCOUNTER5H,
    MHPMCOUNTER6H,
    MHPMEVENT3,
    MHPMEVENT4,
    MHPMEVENT5,
    MHPMEVENT6,
    MHPMCOUNTER7,
    MHPMCOUNTER8,
    MHPMCOUNTER16,
    MHPMCOUNTER7H,
    MHPMCOUNTER8H,
    MHPMCOUNTER16H,
    MHPMEVENT7,
    MHPMEVENT8,
    MHPMEVENT16,
    MCOUNTINHIBIT,
    MSECCFG,
    PMPCFG0,
    PMPCFG1,
    PMPCFG2,
    PMPCFG3,
    PMPADDR0,
    PMPADDR1,
    PMPADDR2,
    PMPADDR3,
    PMPADDR4,
    PMPADDR5,
    PMPADDR6,
    PMPADDR7,
    PMPADDR8,
    PMPADDR9,
    PMPADDR10,
    PMPADDR11,
    PMPADDR12,
    PMPADDR13,
    PMPADDR14,
    PMPADDR15
};

// Implementation-specific custom CSRs
// By default all not found registers are put to custom csrs
bit [11:0] custom_csr[] = {
    12'h3D0, // CSR_PMPADDR32
    12'h7C0, // CSR_MRAC
    12'hBC0, // CSR_MDEAU
    12'hFC0, // CSR_MDSEAC
    12'h7C2, // CSR_MCPC
    12'h7C4, // CSR_DMST
    12'h3C0, // CSR_PMPADDR16
    12'h7C6, // CSR_MPMC
    12'hBC8, // CSR_MEIVT
    12'hFC8, // CSR_MEIHAP
    12'hBC9, // CSR_MEIPT
    12'hBCA, // CSR_MEICPCT
    12'hBCC, // CSR_MEICURPL
    12'hBCB, // CSR_MEICIDPL
    12'h7CE, // CSR_MFDHT
    12'h7CF, // CSR_MFDHS
    12'h7C8, // CSR_DICAWICS
    12'h7CC, // CSR_DICAD0H
    12'h7C9, // CSR_DICAD0
    12'h7CA, // CSR_DICAD1
    12'h7CB, // CSR_DICAGO
    12'h7D3, // CSR_MITB0
    12'h7D4, // CSR_MITCTL0
    12'h7D2, // CSR_MITCNT0
    12'h7D6, // CSR_MITB1
    12'h7D7, // CSR_MITCTL1
    12'h7D5, // CSR_MITCNT1
    12'h3E0, // CSR_PMPADDR48
    12'h7F0, // CSR_MICECT
    12'h7F1, // CSR_MICCMECT
    12'h7F2, // CSR_MDCCMECT
    12'h7F8, // CSR_MCGC
    12'h7F9, // CSR_MFDC
    12'h7FF // CSR_MSCAUSE
};

// ----------------------------------------------------------------------------
// Supported interrupt/exception setting, used for functional coverage
// ----------------------------------------------------------------------------

`ifdef DSIM
interrupt_cause_t implemented_interrupt[] = {
`else
const interrupt_cause_t implemented_interrupt[] = {
`endif
    M_SOFTWARE_INTR,
    M_TIMER_INTR,
    M_EXTERNAL_INTR
    //0x1c custom interrupt used
    //0x1d custom interrupt used
    //0x1e custom interrupt used
};

`ifdef DSIM
exception_cause_t implemented_exception[] = {
`else
const exception_cause_t implemented_exception[] = {
    INSTRUCTION_ACCESS_FAULT,
    BREAKPOINT,
    LOAD_ADDRESS_MISALIGNED,
    LOAD_ACCESS_FAULT,
    STORE_AMO_ADDRESS_MISALIGNED,
    STORE_AMO_ACCESS_FAULT,
    ECALL_MMODE
};
`endif
