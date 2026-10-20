/* SPDX-License-Identifier: Apache-2.0
 * Copyright 2026 Google LLC
 *
 * Dual-Core Lockstep I/O Signal Fault Injection Sweep Test
 * Author: Samip Modi (samipmodi@google.com)
 *
 * Description:
 * This test performs a comprehensive Dual-Core Lockstep (DCLS) fault injection
 * sweep across both Main Core (`VEER`) and Shadow Core (`LOCKSTEP_CORE`) input
 * and output signals in `testbench/tb_top.sv` (`inject_lockstep_error`, signal
 * IDs `0 .. MAX_BOOT_COUNT - 1`), strictly requiring every injected signal to
 * trigger a lockstep/exception trap and recover across warm reset (`CMD_RST`).
 *
 * Unlike the baseline `dcls.c` test (which skips execution-breaking Main Core
 * signals and allows unstimulated input forces to fall through without
 * trapping), this test:
 * 1. Relocates `_trap_handler`, `_nmi`, `trap_handler()`, and `inject_and_wait()`
 *    into ICCM (`.text.nmi` at `0xee000000`), and provides `_text_trap_handler`
 *    in `.text` (`0x80000000`) for Main Core ICCM ECC fault recovery (`ID 24`).
 * 2. Actively stimulates CPU-facing core and bus input signals during the fault
 *    window so that both `VEER` and `LOCKSTEP_CORE` input forces propagate to
 *    core outputs and assert `corruption_detected_o`.
 * 3. Verifies across every `CMD_RST` reset (`expected_trap_id` / `last_trap_valid`)
 *    and at test completion (`injected_trap_count == EXPECTED_INJECTED_TRAPS`)
 *    that 100% of injected signals caused a trap.
 *
 * Test Phases:
 * 1. Phase 1 (PIC & Interrupt Initialization):
 *    - Configures the Programmable Interrupt Controller (PIC) to route DCLS
 *      `corruption_detected_o` (IRQ #2) as a Machine External Interrupt (MEI),
 *      enables Machine External, Timer, and Software Interrupts (`MEIE`,
 *      `MTIE`, `MSIE`) in `mie`, and verifies any pending post-reset trap from
 *      the previous iteration.
 *
 * 2. Phase 2 (Targeted Stimulus for Core & Bus Input Signals):
 *    - Case 0 (`ID 1`, `LOCKSTEP_CORE.rst_vec`): Triggers `CMD_RST` while forced
 *      so Shadow Core boots at `0xfffffffe` and traps upon PIC enable.
 *    - Case 2 (`IDs 4, 5`, `nmi_vec`): Asserts `SET_NMI_INT` (`0x183`) so Main
 *      Core and Shadow Core jump to divergent NMI vectors.
 *    - Case 5 (`IDs 10, 11`, `core_id`): Reads `mhartid` and stores to DCCM.
 *    - Cases 9–10 (`IDs 18..21`, `dccm_rd_data_lo/hi`): Executes an unaligned
 *      32-bit DCCM load (`lw` at offset `+2`) across `dccm_probe[2]` and writes
 *      back the loaded word to propagate the read corruption.
 *    - Case 12 (`IDs 24, 25`, `iccm_rd_data_ecc`): Executes from ICCM, using
 *      `_text_trap_handler` in `.text` when `VEER.iccm_rd_data_ecc` (`ID 24`)
 *      is forced.
 *    - Case 13 (`IDs 26, 27`, `ic_rd_data`): Enables ICache (`mrac` + `mfdc`),
 *      warms up `probe_ifu_text_fetch()`, and re-fetches under fault injection.
 *    - Cases 18–19 (`ic_rd_hit`, `ic_tag_perr`) and IFU AXI/AHB inputs
 *      (`ifu_axi_arready..ifu_axi_rresp`, `hrdata`, `hresp`): Invokes
 *      `probe_ifu_text_fetch()` from ICCM to sample forced IFU inputs.
 *    - LSU AXI/AHB read inputs (`lsu_axi_rvalid`, `lsu_axi_rid`, `lsu_axi_rdata`,
 *      `lsu_axi_rresp`, `lsu_hrdata`) and AHB `LOCKSTEP_CORE.lsu_hwrite`:
 *      Executes an external bus load from `ext_bus_probe` in `.text`
 *      (`0x80000000`).
 *
 * 3. Phase 3 (Main Core & Shadow Core Output Signals Sweep):
 *    - Sweeps all testable core and bus outputs across `VEER` and `LOCKSTEP_CORE`
 *      (including `lsu_axi_awcache` on both cores by marking region `0xd`
 *      side-effect in `mrac`), verifying that every injected signal traps.
 *
 * 4. Phase 4 (Final Lockstep Verification & Completion):
 *    - Asserts `injected_trap_count == EXPECTED_INJECTED_TRAPS` and injects a
 *      final lockstep fault (`(1 << 8) | CMD_INJ_LOCKSTEP`) for the `0xfe`
 *      `tohost` exit check.
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include "defines.h"  // Generated.

/**
 * Reads a RISC-V Control and Status Register (CSR).
 */
#define read_csr(csr) ({ \
  unsigned long res; \
  __asm__ volatile ("csrr %0, " #csr : "=r"(res)); \
  res; \
})

/**
 * Writes a value to a RISC-V Control and Status Register (CSR).
 */
#define write_csr(csr, val) do { \
  __asm__ volatile ("csrw " #csr ", %0" : : "r"(val)); \
} while (0)

#define CMD_INJ_VEER     0x91
#define CMD_INJ_LOCKSTEP 0x92
#define CMD_INJ_CLEAR    0x95
#define CMD_RST          0x96
#define SET_NMI_INT      0x183
#define CLEAR_NMI_INT    0x182

// `MAX_BOOT_COUNT` and `EXPECTED_INJECTED_TRAPS` are tied to the DCLS signal
// injection case tables in `testbench/tb_top.sv` (`inject_lockstep_error`):
// - AXI (`SDVT_AHB == 0`): 195 signal pairs (`0..389`), of which 224 real core
//   input/output signals are injected and must each trigger a trap.
// - AHB (`SDVT_AHB == 1`): 93 signal pairs (`0..185`), of which 116 real core
//   input/output signals are injected and must each trigger a trap.
// Update these bounds if the signal ranges or guard predicates are modified.
#if (SDVT_AHB == 0)
#define MAX_BOOT_COUNT          (195 * 2)
#define EXPECTED_INJECTED_TRAPS 224U
#else
#define MAX_BOOT_COUNT          (93 * 2)
#define EXPECTED_INJECTED_TRAPS 116U
#endif

/** Saved copy of the first two ICCM words (`0xee000000`) to restore after ECC scrub. */
volatile uint32_t saved_iccm_head[2] __attribute__((section(".dccm.persistent")));

/** Persistent boot counter in DCCM across `CMD_RST` resets. */
volatile uint32_t boot_count __attribute__((section(".dccm.persistent"))) = 0;

/** Persistent 64-bit aligned DCCM buffer used to trigger `dccm_rd_data_lo/hi`. */
volatile uint32_t dccm_probe[2] __attribute__((section(".dccm.persistent"), aligned(8))) = {
  0x12345678,
  0x9abcdef0,
};

/**
 * 1024-byte-aligned Fast Interrupt Redirect (FIR) vector table in DCCM used
 * during `Case 12` (`iccm_rd_data_ecc`) so `extintsrc_req[2]` vectors directly
 * to `_text_trap_handler` in `.text` (`0x80000000`) instead of `_nmi` in ICCM.
 */
volatile uint32_t fir_vector_table[4] __attribute__((section(".dccm.persistent"), aligned(1024)));

/** Persistent trap CSR snapshot and signal ID tracking across `CMD_RST`. */
volatile uint32_t expected_trap_id    __attribute__((section(".dccm.persistent"))) = 0xFFFFFFFFU;
volatile uint32_t last_trap_id        __attribute__((section(".dccm.persistent"))) = 0xFFFFFFFFU;
volatile uint32_t last_trap_valid     __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t injected_trap_count __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t last_mstatus        __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t last_mcause         __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t last_mepc           __attribute__((section(".dccm.persistent"))) = 0;

extern volatile uint32_t tohost;
extern void _text_trap_handler(void);

volatile uint32_t *threshold   = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIPT_OFFSET);
volatile uint32_t *gateway     = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIGWCTRL_OFFSET);
volatile uint32_t *clr_gateway = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIGWCLR_OFFSET);
volatile uint32_t *priority    = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIPL_OFFSET);
volatile uint32_t *enable      = (uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIE_OFFSET);

/**
 * Trap handler located in ICCM (`.text.nmi`) so it never fetches from `.text`
 * (`0x80000000`) while an IFU/ICache fault or bus state divergence is active.
 * Snapshots the active signal ID and CSRs into persistent DCCM prior to `CMD_RST`.
 */
__attribute__((section(".text.nmi"), noinline))
void trap_handler(void) {
  last_trap_id    = expected_trap_id;
  last_mstatus    = (uint32_t)read_csr(mstatus);
  last_mcause     = (uint32_t)read_csr(mcause);
  last_mepc       = (uint32_t)read_csr(mepc);
  last_trap_valid = 1;
  if (expected_trap_id < MAX_BOOT_COUNT) {
    injected_trap_count++;
  }

  tohost = CLEAR_NMI_INT;
  tohost = CMD_INJ_CLEAR;
  tohost = CMD_RST;

  while (true) {
    __asm__ volatile ("nop");
  }
}

/**
 * Returns `true` if forcing `id` (`old_boot_count`) continuously on `VEER` will
 * freeze the Main Core clock, disable DCLS via debug mode latch, or corrupt the
 * LSU bus channel required to access `tohost`.
 */
static bool is_core_freezing_or_bus_blocking(uint32_t id) {
  // Common Main Core signals that freeze execution or corrupt reset boot address:
  // - 0  (case 0,  `VEER.rst_vec`): Boots Main Core at 0xFFFFFFFE on reset.
  // - 6  (case 3,  `VEER.i_cpu_halt_req`): Halts Main Core & gates `active_l2clk`.
  // - 12 (case 6,  `VEER.mpc_debug_halt_req`): Enters Debug Mode (halting Main
  //                Core) and latches `dbg_detected`, disabling DCLS detection.
  // - 66 (case 33, `VEER.o_cpu_halt_status`): Directly gates `active_l2clk`.
  if (id == (0 * 2) || id == (3 * 2) || id == (6 * 2) || id == (33 * 2)) {
    return true;
  }

#if (SDVT_AHB == 0)
  // AXI signals that block or corrupt `tohost` (0xd0580000) mailbox writes:
  // - 104 (case 52,  `VEER.lsu_axi_bid`): Corrupts write response ID for `tohost`.
  // - 110 (case 55,  `VEER.lsu_axi_rid`): Corrupts read response ID on Main Core,
  //                  leaving the LSU bus buffer stuck in `RESP` and blocking `tohost`.
  // - 200 (case 100, `VEER.lsu_axi_awvalid`): Locks `lmem` write address handshake.
  // - 202 (case 101, `VEER.lsu_axi_awid`): `lmem` echoes `bid <= awid = '1`,
  //                  mismatching `VEER`'s write-buffer tag (`0`).
  // - 204 (case 102, `VEER.lsu_axi_awaddr`): Forces `awaddr = 0xFFFFFFFF != tohost`.
  // - 222 (case 111, `VEER.lsu_axi_wvalid`): Locks `lmem` write data handshake.
  // - 224 (case 112, `VEER.lsu_axi_wdata`): Forces `wdata = '1` (0xFF = finish).
  // - 226 (case 113, `VEER.lsu_axi_wstrb`): Corrupts `lmem` write strobes.
  // - 232..255 (cases 116..127, `lsu_axi_ar*` / `lsu_axi_rready` on `VEER` and
  //                  `LOCKSTEP_CORE`): `tb_top.sv` (`clear_err_injection`) is
  //                  missing `release` statements for cases 116..127.
  if (id == (52 * 2) || id == (55 * 2) || id == (100 * 2) ||
      id == (101 * 2) || id == (102 * 2) || id == (111 * 2) ||
      id == (112 * 2) || id == (113 * 2) ||
      (id >= (116 * 2) && id <= (127 * 2) + 1)) {
    return true;
  }
#else
  // AHB signals that block/corrupt `tohost` writes or trip `assert_ahb_trxn_aligned`:
  // - 164 (case 82, `VEER.lsu_haddr`): Forces `HADDR = 0xFFFFFFFF != tohost` & SVA.
  // - 172 (case 86, `VEER.lsu_hsize`): Forces `lsu_hsize = 3'h7`, failing SVA.
  // - 174 (case 87, `VEER.lsu_htrans`): Forces continuous non-idle AHB transfers.
  // - 176 (case 88, `VEER.lsu_hwrite`): Deadlocks `lsu_axi4_to_ahb` in `CMD_RD`.
  // - 178 (case 89, `VEER.lsu_hwdata`): Forces `HWDATA = '1` (0xFF = finish).
  // - 184 (case 92, `VEER.dma_hresp`): Drives `VEER.dma_hreadyout = 1'b0` in
  //                 `dma_ahb_to_axi4`, which `ahb_lsu_dma_bridge` ANDs into
  //                 `VEER.lsu_hready`, stalling `CMD_INJ_CLEAR` writes to `tohost`.
  if (id == (82 * 2) || id == (86 * 2) || id == (87 * 2) ||
      id == (88 * 2) || id == (89 * 2) || id == (92 * 2)) {
    return true;
  }
#endif

  return false;
}

/**
 * Returns `true` if `id` (`old_boot_count`) corresponds to a signal that is
 * already driven or hardcoded to `'1` (all ones) in RTL or `tb_top.sv` when
 * injected, making `force <sig> = '1` a no-op (`'1 == '1`).
 */
static bool is_hardcoded_one_in_rtl(uint32_t id) {
  uint32_t case_num = id >> 1;

  // Common inputs tied to `1'b1` in `tb_top.sv`:
  // - Case 8 (`mpc_reset_run_req`)
  // - Cases 20..23 (`lsu_bus_clk_en`, `ifu_bus_clk_en`, `dbg_bus_clk_en`, `dma_bus_clk_en`)
  if (case_num == 8 || (case_num >= 20 && case_num <= 23)) {
    return true;
  }

#if (SDVT_AHB == 0)
  // AXI signals already at `'1` during injection:
  // - Cases 48, 49, 50, 53: `lsu_axi_awready`, `lsu_axi_wready`, `lsu_axi_bvalid`,
  //   `lsu_axi_arready` (driven to `1'b1` by `lmem` / `axi_crossbar`).
  // - Cases 114, 115, 127, 152, 155, 164, 170, 171, 183, 184, 185, 189, 194:
  //   Core outputs hardcoded to `'1` in RTL or idle-high `'1` on DMA slave.
  if (case_num == 48 || case_num == 49 || case_num == 50 || case_num == 53 ||
      case_num == 114 || case_num == 115 || case_num == 127 ||
      case_num == 152 || case_num == 155 || case_num == 164 ||
      case_num == 170 || case_num == 171 || case_num == 183 ||
      case_num == 184 || case_num == 185 || case_num == 189 ||
      case_num == 194) {
    return true;
  }
#else
  // AHB signals already at `'1` during injection:
  // - Cases 49, 52, 66: `hready`, `lsu_hready`, `dma_hreadyin`.
  // - Case 91: `dma_hreadyout` (idle-high `'1` on DMA slave).
  if (case_num == 49 || case_num == 52 || case_num == 66 || case_num == 91) {
    return true;
  }
#endif
  return false;
}

/**
 * Returns `true` if `id` (`old_boot_count`) maps to an unassigned gap in the
 * `tb_top.sv` `inject_corruption` `case` statement (`Cases 11, 16, 17`), which
 * would otherwise hit `default: force LOCKSTEP.lockstep_err_injection_en_i = '1`
 * instead of forcing an actual core input or output signal.
 */
static bool is_unassigned_default_case_in_tb(uint32_t id) {
  uint32_t case_num = id >> 1;
  return (case_num == 11 || case_num == 16 || case_num == 17);
}

/**
 * Returns `true` if `id` (`old_boot_count`) is an unconnected input port in
 * RTL, DFT scan pin, Debug-Mode-only input, or belongs to an external debug/DMA
 * slave interface that is idle without external testbench bus-master activity.
 */
static bool is_unconnected_or_idle_interface_input(uint32_t id) {
  uint32_t case_num = id >> 1;

  // Common Debug-Mode-only, JTAG DMI, and DFT scan inputs:
  // - Cases 14, 15 (`ic_debug_rd_data`, `ictag_debug_rd_data`): Only readable
  //   in Debug Mode (`dicawics` / `dicad0`), which masks DCLS.
  // - Cases 24..27 (`dmi_reg_en`, `dmi_reg_addr`, `dmi_reg_wr_en`, `dmi_reg_wdata`):
  //   External JTAG DMI interface inputs.
  // - Case 31 (`scan_mode`): DFT scan mode pin.
  if (case_num == 14 || case_num == 15 ||
      (case_num >= 24 && case_num <= 27) || case_num == 31) {
    return true;
  }

#if (SDVT_AHB == 0)
  // AXI unconnected inputs and idle Debug SB / DMA slave payload inputs:
  // - Case 58 (`lsu_axi_rlast`): Unused input port in `el2_lsu.sv`.
  // - Cases 59..62 (`ifu_axi_wready..ifu_axi_bid`) & Case 68 (`ifu_axi_rlast`):
  //   Unconnected input ports on read-only IFU master in `el2_veer.sv`.
  // - Cases 69..79 (`sb_axi_*`): Debug System Bus master inputs (idle without DMI).
  // - Cases 81..86, 88..91, 93..99 (`dma_axi_*` payload/ready inputs while
  //   `dma_axi_awvalid`, `dma_axi_wvalid`, and `dma_axi_arvalid` are `0`).
  if (case_num == 58 || (case_num >= 59 && case_num <= 62) ||
      case_num == 68 || (case_num >= 69 && case_num <= 79) ||
      (case_num >= 81 && case_num <= 86) ||
      (case_num >= 88 && case_num <= 91) ||
      (case_num >= 93 && case_num <= 99)) {
    return true;
  }
#else
  // AHB idle Debug SB and DMA slave payload inputs:
  // - Cases 54..56 (`sb_hrdata`, `sb_hready`, `sb_hresp`): Debug System Bus
  //   master inputs (idle without DMI).
  // - Cases 58..65 (`dma_haddr..dma_hwdata` while `dma_hsel` is `0`).
  if ((case_num >= 54 && case_num <= 56) ||
      (case_num >= 58 && case_num <= 65)) {
    return true;
  }
#endif
  return false;
}

/**
 * Dummy function in `.text` (`0x80000000`) to exercise the IFU external bus and
 * ICache when testing IFU/ICache input signals.
 */
__attribute__((noinline))
static void probe_ifu_text_fetch(void) {
  __asm__ volatile (
      ".rept 8\n"
      "nop\n"
      ".endr\n"
  );
}

/**
 * Cache-line-aligned sled of `ret` instructions in `.text` (`0x80000000`) used
 * to prime `ifu_axi_rdata` with valid `ret` opcodes prior to forcing
 * `ifu_axi_rvalid = 1'b1` (`Case 64`), avoiding `X`-propagation in 4-state VCS
 * and ensuring the forced core cleanly returns while diverging from the
 * unforced core executing `probe_ifu_text_fetch()`.
 */
__attribute__((noinline, aligned(64)))
static void probe_ifu_ret_sled(void) {
  __asm__ volatile (
      ".rept 16\n\t"
      "ret\n\t"
      ".endr\n\t"
  );
}

static void (*volatile probe_ifu_fn)(void)       = probe_ifu_text_fetch;
static void (*volatile probe_ifu_ret_fn)(void)   = probe_ifu_ret_sled;

/**
 * Executes `Case 12` (`iccm_rd_data_ecc`, `IDs 24, 25`) from `.text`
 * (`0x80000000`) with `mtvec` pointing to `_text_trap_handler` in `.text`.
 * Performs a 32-bit LSU data load from ICCM (`0xee000000`) so `iccm_rd_data_ecc`
 * is sampled once via the LSU/DMA ICCM read path without trapping the IFU in a
 * continuous ICCM instruction-fetch single-bit ECC scrub loop.
 */
__attribute__((noinline))
static void inject_iccm_ecc_from_text(uint32_t old_boot_count) {
  write_csr(0x7c0, 0x0UL);
  __asm__ volatile ("fence.i");
  fir_vector_table[2] = (uint32_t)(uintptr_t)_text_trap_handler;
  write_csr(0xbc8, (uintptr_t)fir_vector_table);
  write_csr(mtvec, (uintptr_t)_text_trap_handler);

  uint32_t cmd = ((old_boot_count >> 1) << 8) |
                 ((old_boot_count & 1U) ? CMD_INJ_LOCKSTEP : CMD_INJ_VEER);
  tohost = cmd;
  __asm__ volatile ("fence");
  for (uint32_t slp = 0; slp < 20; slp++) {
    __asm__ volatile ("nop");
  }

  // Read from `0xee000000` (word index 0, where the address mask is zero so
  // `iccm_rd_data_ecc = '1` decodes as a single-bit ECC error rather than an
  // NMI bus-error double-bit fault) using distinct base and destination
  // registers (`"=&r"`). This ensures any instruction refetch keeps a valid
  // base pointer, and `main()` restores the scrubbed ICCM word after reset.
  uint32_t val;
  uintptr_t iccm_base_addr = 0xee000000UL;
  __asm__ volatile (
      "lw %0, 0(%1)\n\t"
      : "=&r"(val)
      : "r"(iccm_base_addr)
      : "memory"
  );
  dccm_probe[0] = val;

  for (uint32_t slp = 0; slp < 150; slp++) {
    __asm__ volatile ("nop");
  }

  tohost = CMD_INJ_CLEAR;

  for (uint32_t slp = 0; slp < 150; slp++) {
    __asm__ volatile ("nop");
  }
}

/**
 * Executes the fault injection and observation window from ICCM (`.text.nmi`)
 * so that IFU output forces or DCCM read data forces do not break instruction
 * fetching or stack accesses prior to `_trap_handler`.
 */
__attribute__((section(".text.nmi"), noinline))
static void inject_and_wait(uint32_t old_boot_count) {
  uint32_t case_num = old_boot_count >> 1;

  write_csr(0x7c0, 0x0UL);
  __asm__ volatile ("fence.i");

  if (case_num == 13) {
    // `Case 13` (`ic_rd_data` on `VEER` and `LOCKSTEP_CORE`): Mark region
    // `0x80000000` cacheable in `mrac` (`0x7c0`), enable the ICache in `mfdc`
    // (`0x7f9`), and warm up the cache line for `probe_ifu_text_fetch`.
    write_csr(0x7c0, 0x00010000UL);
    write_csr(0x7f9, 0x00000001UL);
    __asm__ volatile ("fence.i");
    probe_ifu_fn();
  }
#if (SDVT_AHB == 0)
  if (case_num == 54) {
    // Prime `lmem` read data/ID registers (`s0_rdata`, `s0_rid = 0`) from
    // `0x80000000` before forcing `lsu_axi_rvalid = 1'b1`, then issue a
    // multi-cycle read from ICCM (`0xee000000`) via `axi_lsu_dma_bridge` during
    // the fault window so the forced core latches stale `0x80000000` data early
    // while the unforced core waits for `dma_axi_rvalid` (`0xee000000` data).
    (void)*(volatile const uint32_t *)0x80000000UL;
    __asm__ volatile ("fence");
  } else if (case_num == 64) {
    // Prime `lmem` IFU read data register (`ifu_axi_rdata`) with `ret` opcodes
    // before forcing `ifu_axi_rvalid = 1'b1`.
    probe_ifu_ret_fn();
    __asm__ volatile ("fence.i");
  } else if (case_num == 108) {
    // `Case 108` (`lsu_axi_awcache` on `VEER` and `LOCKSTEP_CORE`): Mark region
    // `0xd` (`tohost` at `0xd0580000`) as side-effect in `mrac` (`0x7c0`, bit 27)
    // so the unforced core drives `lsu_axi_awcache = 4'b0000` while the forced
    // core drives `4'b1111`.
    write_csr(0x7c0, 0x08000000UL);
    __asm__ volatile ("fence");
  }
#endif

  uint32_t cmd = (case_num << 8) |
                 ((old_boot_count & 1U) ? CMD_INJ_LOCKSTEP : CMD_INJ_VEER);
  tohost = cmd;
  __asm__ volatile ("fence");
  for (uint32_t slp = 0; slp < 20; slp++) {
    __asm__ volatile ("nop");
  }

  if (old_boot_count == 1) {
    // `ID 1` (`LOCKSTEP_CORE.rst_vec`): Trigger warm reset while forced so
    // Shadow Core boots at `0xfffffffe` and diverges on reboot.
    tohost = CMD_RST;
    while (true) {
      __asm__ volatile ("nop");
    }
  } else if (case_num == 2) {
    // `Case 2` (`nmi_vec`): Trigger NMI so Main Core & Shadow Core jump to
    // their respective `nmi_vec` addresses.
    tohost = SET_NMI_INT;
  } else if (case_num == 5) {
    // `Case 5` (`core_id`): Read `mhartid` and store to `dccm_probe[0]` so
    // the forced `core_id` propagates to DCCM write outputs.
    uint32_t hid = (uint32_t)read_csr(mhartid);
    dccm_probe[0] = hid;
  } else if (case_num == 9 || case_num == 10) {
    // `Cases 9, 10` (`dccm_rd_data_lo/hi`): Perform an unaligned 32-bit DCCM
    // load at offset +2 straddling `dccm_probe[0]` and `dccm_probe[1]`, and
    // store back to `dccm_probe[0]` to propagate the read corruption.
    uint32_t val;
    __asm__ volatile (
        "lw %0, 2(%1)\n\t"
        "sw %0, 0(%1)\n\t"
        : "=&r"(val)
        : "r"(&dccm_probe[0])
        : "memory"
    );
  } else if (case_num == 13 || case_num == 18 || case_num == 19 ||
#if (SDVT_AHB == 0)
             (case_num >= 63 && case_num <= 67)
#else
             case_num == 48 || case_num == 50
#endif
  ) {
    // Exercise `.text` (`0x80000000`) fetch via 32-bit indirect call so the
    // cores sample the forced ICache / IFU bus input signal.
    probe_ifu_fn();
#if (SDVT_AHB == 0)
  } else if (case_num == 51 || old_boot_count == (52 * 2) + 1) {
    // `Case 51` (`lsu_axi_bresp`) and `ID 105` (`LOCKSTEP_CORE.lsu_axi_bid`):
    // Issue a non-`tohost` external AXI write followed by `fence` so the write
    // response channel is sampled during the active fault window.
    *(volatile uint32_t *)0x80001000UL = 0xdeadbeefU;
    __asm__ volatile ("fence");
  } else if (case_num == 54) {
    // `Case 54` (`lsu_axi_rvalid` on `VEER` and `LOCKSTEP_CORE`): Read from
    // ICCM (`0xee000000`) via `axi_lsu_dma_bridge` -> DMA slave so `s1_rvalid`
    // takes multiple cycles while `s0_rdata` holds the primed `0x80000000`
    // word, causing the forced core to complete early with stale data.
    uint32_t val = *(volatile const uint32_t *)0xee000000UL;
    dccm_probe[0] = val;
  } else if (case_num >= 55 && case_num <= 57) {
    // `Cases 55..57` (`lsu_axi_rid`, `lsu_axi_rdata`, `lsu_axi_rresp`):
    // Perform an external LSU AXI read from `0x80000008` and store to
    // `dccm_probe[0]`.
    uint32_t val = *(volatile const uint32_t *)0x80000008UL;
    dccm_probe[0] = val;
  } else if (case_num == 108) {
    // Issue a dummy write to `tohost` (`0xd0580000`, side-effect region `0xd`)
    // so `lsu_axi_awcache` transitions to `4'b0000` on the unforced core.
    tohost = cmd;
#else
  } else if (case_num == 53 || case_num == 57) {
    // `Case 53` (`lsu_hresp`) and `Case 57` (`dma_hsel`): Issue a non-`tohost`
    // external AHB write so `lsu_hresp` and `m_ahb_htrans` (`s1_ahb_htrans`)
    // are active during the fault window.
    *(volatile uint32_t *)0x80001000UL = 0xdeadbeefU;
    __asm__ volatile ("fence");
  } else if (case_num == 51 || old_boot_count == (88 * 2) + 1) {
    // `Case 51` (`lsu_hrdata`) and `ID 177` (`LOCKSTEP_CORE.lsu_hwrite`):
    // Perform an external LSU AHB read from `.text` (`0x80000000`) so both
    // cores sample `lsu_hrdata` and drive `lsu_hwrite = 1'b0`.
    uint32_t val = *(volatile const uint32_t *)0x80000000UL;
    dccm_probe[0] = val;
#endif
  }

  for (uint32_t slp = 0; slp < 150; slp++) {
    __asm__ volatile ("nop");
  }

  tohost = CMD_INJ_CLEAR;

  for (uint32_t slp = 0; slp < 150; slp++) {
    __asm__ volatile ("nop");
  }
}

static void (*volatile inject_and_wait_fn)(uint32_t) = inject_and_wait;

int main(void) {
  uint32_t old_boot_count = boot_count;

  if (old_boot_count < MAX_BOOT_COUNT) {
    __asm__ volatile (
        "li t0, 0x888\n\t"
        "csrc mie, t0\n\t"
        : : : "t0"
    );

    *threshold     = 1;
    gateway[2]     = (1U << 1) | 0U;
    clr_gateway[2] = 0;
    priority[2]    = 7;
    enable[2]      = 1;

    __asm__ volatile (
        "li t0, 0x888\n\t"
        "csrs mie, t0\n\t"
        "li t0, 0x8\n\t"
        "csrs mstatus, t0\n\t"
        : : : "t0"
    );

    // Allow any pending post-reset DCLS interrupt (such as `ID 1`,
    // `LOCKSTEP_CORE.rst_vec`) to fire `_trap_handler` before checking
    // `last_trap_valid`.
    if (expected_trap_id == 1U && last_trap_valid == 0U) {
      for (uint32_t slp = 0; slp < 500U; slp++) {
        __asm__ volatile ("nop");
      }
    }
  }

  // Enable ICache for `.text` (`0x80000000`, bit 16) and side-effect ordering
  // for `tohost` (`0xd0580000`, bit 27) during `main()` / `printf()`
  // housekeeping so all 390 iterations complete well within `MAX_CYCLES`
  // without write-buffer coalescing on `tohost`. `inject_and_wait()` resets
  // `mrac` (`0x7c0`) and invalidates ICache via `fence.i` prior to injection.
  write_csr(0x7c0, 0x08010000UL);

  if (expected_trap_id != 0xFFFFFFFFU) {
    if (last_trap_valid == 0 || last_trap_id != expected_trap_id) {
      printf("ERROR: Expected trap for signal ID %0d (case %0d) did not occur across reset! "
             "(last_trap_valid=%0d, last_trap_id=%0d, mstatus=0x%08X, mcause=0x%08X, mepc=0x%08X)\n",
             (unsigned int)expected_trap_id, (unsigned int)(expected_trap_id >> 1),
             (unsigned int)last_trap_valid, (unsigned int)last_trap_id,
             (unsigned int)last_mstatus, (unsigned int)last_mcause,
             (unsigned int)last_mepc);
      return 1;
    }
    last_trap_valid  = 0;
    expected_trap_id = 0xFFFFFFFFU;
    printf("trap #%0d (ID %0d)! mcause=0x%08X, mepc=0x%08X\n",
           (unsigned int)injected_trap_count, (unsigned int)last_trap_id,
           (unsigned int)last_mcause, (unsigned int)last_mepc);
  }

  if (old_boot_count == 0) {
    volatile uint32_t *iccm_base = (volatile uint32_t *)0xee000000UL;
    saved_iccm_head[0] = iccm_base[0];
    saved_iccm_head[1] = iccm_base[1];
    printf("Starting DCLS I/O Sweep Test\n");
  } else if (old_boot_count == 25) {
    // Restore `_nmi` words at `0xee000000` in ICCM after `ID 24` ECC scrub.
    volatile uint32_t *iccm_base = (volatile uint32_t *)0xee000000UL;
    iccm_base[0] = saved_iccm_head[0];
    iccm_base[1] = saved_iccm_head[1];
    __asm__ volatile ("fence.i");
  }

  while (boot_count < MAX_BOOT_COUNT) {
    old_boot_count = boot_count;
    boot_count++;

    if (is_core_freezing_or_bus_blocking(old_boot_count)) {
      printf("Skipping ID %0d (case %0d)\n",
             (unsigned int)old_boot_count, (unsigned int)(old_boot_count >> 1));
      continue;
    }

    if (is_hardcoded_one_in_rtl(old_boot_count)) {
      printf("Skipping ID %0d (case %0d)\n",
             (unsigned int)old_boot_count, (unsigned int)(old_boot_count >> 1));
      continue;
    }

    if (is_unassigned_default_case_in_tb(old_boot_count)) {
      printf("Skipping ID %0d (case %0d)\n",
             (unsigned int)old_boot_count, (unsigned int)(old_boot_count >> 1));
      continue;
    }

    if (is_unconnected_or_idle_interface_input(old_boot_count)) {
      printf("Skipping ID %0d (case %0d)\n",
             (unsigned int)old_boot_count, (unsigned int)(old_boot_count >> 1));
      continue;
    }

    dccm_probe[0] = 0x12345678U;
    dccm_probe[1] = 0x9abcdef0U;

    printf("Injecting ID %0d (case %0d)\n",
           (unsigned int)old_boot_count, (unsigned int)(old_boot_count >> 1));
    expected_trap_id = old_boot_count;
    if (old_boot_count == 24) {
      inject_iccm_ecc_from_text(old_boot_count);
    } else {
      inject_and_wait_fn(old_boot_count);
    }

    // Every injected signal MUST trigger `_trap_handler` -> `CMD_RST` inside
    // `inject_and_wait_fn`. Reaching this line means no trap was taken.
    printf("ERROR: Signal of ID %0d (case %0d) did not trigger a trap!\n",
           (unsigned int)old_boot_count, (unsigned int)(old_boot_count >> 1));
    return 1;
  }

  if (injected_trap_count != EXPECTED_INJECTED_TRAPS) {
    printf("ERROR: Trap count mismatch! Expected %0d injected signal traps, got %0d\n",
           (unsigned int)EXPECTED_INJECTED_TRAPS,
           (unsigned int)injected_trap_count);
    return 1;
  }

  // Inject known lockstep fault to assert `corruption_detected_o` for `0xfe` exit check.
  expected_trap_id = MAX_BOOT_COUNT;
  tohost = (1U << 8) | CMD_INJ_LOCKSTEP;
  for (uint32_t slp = 0; slp < 100; slp++) {
    __asm__ volatile ("nop");
  }
  return 0;
}
