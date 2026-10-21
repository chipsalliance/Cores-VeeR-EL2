/* SPDX-License-Identifier: Apache-2.0
 * Copyright 2026 Google LLC
 *
 * DCLS Safety Scope: Skipped Signals Fault Injection & Lockstep Detection Test
 * Author: Samip Modi (samipmodi@google.com)
 *
 * Description:
 * This test verifies Dual-Core Lockstep (DCLS) fault detection and recovery for the
 * Main Core (`VEER`) and Shadow Core (`LOCKSTEP_CORE`) signals that were skipped in
 * the baseline `dcls.c` test (`testbench/tests/dcls/dcls.c`).
 *
 * In `dcls.c`, Main Core signals were skipped because executing the injection loop
 * and `_trap_handler` from external `.text` (`0x80000000`) and using the DCCM stack
 * causes instruction fetch hangs, unaligned DCCM stack faults, or unserviced stimulus
 * while the fault is active. By relocating `_trap_handler`, `_nmi`, `trap_handler()`,
 * and the fault-injection window (`inject_and_wait()`) into ICCM (`.text.nmi` at
 * `0xee000000`) and clearing fault injection in assembly using only GPRs before
 * touching the DCCM stack or fetching from `.text`, this test safely exercises and
 * recovers from those skipped signals.
 *
 * Test Phases:
 * 1. Phase 1 (PIC & Interrupt Initialization):
 *    - Configures the Programmable Interrupt Controller (PIC) to route DCLS
 *      `corruption_detected_o` (IRQ #2) as a Machine External Interrupt (MEI).
 *
 * 2. Phase 2 (Targeted Stimulus for Input Signals on Main Core `VEER`):
 *    - Case 2 (`old_boot_count = 4`, `nmi_vec`): Asserts `SET_NMI_INT` (`0x183`) so
 *      Main Core and Shadow Core jump to divergent NMI vectors (`0xffffffff` vs. `_nmi`).
 *    - Cases 9–10 (`old_boot_count = 18, 20`, `dccm_rd_data_lo/hi`): Executes an
 *      unaligned 32-bit load (`lw` at offset `+2`) across `dccm_probe[2]` to sample
 *      both low and high DCCM read banks without corrupting the stack.
 *    - Case 13 (`old_boot_count = 26`, `ic_rd_data`): Enables ICache (`mrac` + `mfdc`),
 *      warms up the cache line for `probe_ifu_text_fetch()`, and re-fetches under
 *      fault injection.
 *    - Cases 18–19 (`ic_rd_hit`, `ic_tag_perr`), Case 28 (`extintsrc_req`), and
 *      IFU AXI/AHB inputs (`ifu_axi_arready`, `ifu_axi_rid`, `ifu_axi_rdata`,
 *      `ifu_axi_rresp`, `hrdata`, `hresp`): Invokes `probe_ifu_text_fetch()` from
 *      ICCM so Main Core actively samples the forced IFU/ICache inputs.
 *
 * 3. Phase 3 (Main Core Output Signals & Bus Divergence Sweep):
 *    - Sweeps all remaining non-freezing skipped Main Core (`VEER`) outputs across
 *      IFU (`ifu_axi_*`, `haddr..hwrite`), System Bus (`sb_*`), DMA (`dma_*`), and
 *      LSU control attributes (`lsu_axi_awregion..lsu_axi_awqos`,
 *      `lsu_hburst..lsu_hwrite`) from ICCM, verifying that `dcls_cmp` detects the
 *      output mismatch and triggers a lockstep trap + warm reset (`CMD_RST`).
 *    - Strictly verifies that EVERY injected signal triggers `_trap_handler`; if
 *      `inject_and_wait()` returns without trapping or resets without setting
 *      `last_trap_valid`, the test immediately fails (`return 1`).
 *
 * 4. Phase 4 (Final Lockstep Verification & Completion):
 *    - Injects a final known lockstep fault (`(1 << 8) | CMD_INJ_LOCKSTEP`) so
 *      `corruption_detected_o` is asserted when `_finish` writes `0xfe` to `tohost`.
 *
 * Guarded Core-Freezing / Bus-Blocking & Hardcoded-1 Signals:
 * - Signals that physically gate the Main Core clock or reset boot PC (`rst_vec`,
 *   `i_cpu_halt_req`, `mpc_debug_halt_req`, `o_cpu_halt_status`), directly block or
 *   corrupt the `tohost` (`0xd0580000`) LSU write channel (`lsu_axi_bid`,
 *   `lsu_axi_awvalid`, `lsu_axi_awid`, `lsu_axi_awaddr`, `lsu_axi_wvalid`,
 *   `lsu_axi_wdata`, `lsu_axi_wstrb`, `lsu_haddr`, `lsu_hsize`, `lsu_htrans`,
 *   `lsu_hwdata`), or lack `release` statements in `tb_top.sv` (`lsu_axi_ar*` /
 *   `lsu_axi_rready`, Cases 116–127) are guarded by
 *   `is_core_freezing_or_bus_blocking()`.
 * - Signals that are hardcoded to `'1` (or driven to `'1` when DMA slave buffers are
 *   idle) in RTL are guarded by `is_hardcoded_one_in_rtl()` because `tb_top.sv`
 *   injects faults via `force <sig> = '1`, which is a no-op on signals already at `'1`.
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <defines.h>

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
// injection case tables in `testbench/tb_top.sv` (`inject_lockstep_error`) and
// the skip list in `testbench/tests/dcls/dcls.c`:
// - AXI (`SDVT_AHB == 0`): 195 signal pairs (`0..389`), of which 76 skipped
//   signals are actively injected and must each trigger a trap.
// - AHB (`SDVT_AHB == 1`): 93 signal pairs (`0..185`), of which 27 skipped
//   signals are actively injected and must each trigger a trap.
// Update these bounds if the signal ranges or skip predicates are modified.
#if (SDVT_AHB == 0)
#define MAX_BOOT_COUNT          (195 * 2)
#define EXPECTED_INJECTED_TRAPS 76U
#else
#define MAX_BOOT_COUNT          (93 * 2)
#define EXPECTED_INJECTED_TRAPS 27U
#endif

/** Persistent boot counter in DCCM across `CMD_RST` resets. */
volatile uint32_t boot_count __attribute__((section(".dccm.persistent"))) = 0;

/** Persistent 64-bit aligned DCCM buffer used to trigger `dccm_rd_data_lo/hi`. */
volatile uint32_t dccm_probe[2] __attribute__((section(".dccm.persistent"), aligned(8))) = {
  0x12345678,
  0x9abcdef0,
};

/** Persistent trap CSR snapshot and signal ID tracking across `CMD_RST`. */
volatile uint32_t expected_trap_id    __attribute__((section(".dccm.persistent"))) = 0xFFFFFFFFU;
volatile uint32_t last_trap_id        __attribute__((section(".dccm.persistent"))) = 0xFFFFFFFFU;
volatile uint32_t last_trap_valid     __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t injected_trap_count __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t last_mstatus        __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t last_mcause         __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t last_mepc           __attribute__((section(".dccm.persistent"))) = 0;

extern volatile uint32_t tohost;

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
 * Returns `true` if `id` (`old_boot_count`) was skipped in `dcls.c`.
 */
static bool is_skipped_in_dcls(uint32_t id) {
  if (id == (0 * 2) ||
      id == (2 * 2) || id == (3 * 2) || id == (6 * 2) ||
      id == (9 * 2) || id == (10 * 2) || id == (13 * 2) ||
      id == (18 * 2) || id == (19 * 2) || id == (28 * 2) ||
      (id == (33 * 2) && (id % 2 == 0)) ||
#if (SDVT_AHB == 0)
      id == (52 * 2) || id == (63 * 2) || id == (65 * 2) ||
      id == (66 * 2) || id == (67 * 2) ||
      (id >= (116 * 2) && id <= (127 * 2)) ||
      (id >= (100 * 2) && id <= (194 * 2) && (id % 2 == 0))
#else
      id == (48 * 2) || id == (50 * 2) || id == (66 * 2) ||
      (id >= (67 * 2) && id <= (89 * 2) && (id % 2 == 0))
#endif
  ) {
    return true;
  }
  return false;
}

/**
 * Returns `true` if forcing `id` (`old_boot_count`) continuously on `VEER` will
 * freeze the Main Core clock, disable DCLS via debug mode latch, or corrupt the
 * LSU write channel required to access `tohost`.
 */
static bool is_core_freezing_or_bus_blocking(uint32_t id) {
  // Common Main Core signals that freeze execution or corrupt reset boot address:
  // - 0  (ID 0,  `VEER.rst_vec`): Boots Main Core at 0xFFFFFFFE on reset.
  // - 6  (ID 3,  `VEER.i_cpu_halt_req`): Halts Main Core & gates `active_l2clk`.
  // - 12 (ID 6,  `VEER.mpc_debug_halt_req`): Enters Debug Mode (halting Main
  //              Core) and latches `dbg_detected`, disabling DCLS detection.
  // - 66 (ID 33, `VEER.o_cpu_halt_status`): Directly gates `active_l2clk`.
  if (id == (0 * 2) || id == (3 * 2) || id == (6 * 2) || id == (33 * 2)) {
    return true;
  }

#if (SDVT_AHB == 0)
  // AXI signals that block or corrupt `tohost` (0xd0580000) mailbox writes:
  // - 104 (ID 52,  `VEER.lsu_axi_bid`): Corrupts write response ID for `tohost`.
  // - 200 (ID 100, `VEER.lsu_axi_awvalid`): Locks `lmem` write address handshake.
  // - 202 (ID 101, `VEER.lsu_axi_awid`): `lmem` echoes `bid <= awid = '1`,
  //                which mismatches `VEER`'s internal write-buffer tag (`0`)
  //                and stalls subsequent `tohost` writes.
  // - 204 (ID 102, `VEER.lsu_axi_awaddr`): Forces `awaddr = 0xFFFFFFFF != tohost`.
  // - 222 (ID 111, `VEER.lsu_axi_wvalid`): Locks `lmem` write data handshake.
  // - 224 (ID 112, `VEER.lsu_axi_wdata`): Forces `wdata = '1` (0xFF = finish).
  // - 226 (ID 113, `VEER.lsu_axi_wstrb`): Corrupts `lmem` write strobes.
  // - 232..255 (IDs 116..127, `lsu_axi_ar*` / `lsu_axi_rready` on `VEER` and
  //                `LOCKSTEP_CORE`): `tb_top.sv` (`clear_err_injection`) is
  //                missing `release` statements for cases 116..127, so forcing
  //                them leaves the signal permanently stuck at `'1` across
  //                subsequent `CMD_RST` resets and causes an infinite trap loop.
  if (id == (52 * 2) || id == (100 * 2) || id == (101 * 2) ||
      id == (102 * 2) || id == (111 * 2) || id == (112 * 2) ||
      id == (113 * 2) || (id >= (116 * 2) && id <= (127 * 2) + 1)) {
    return true;
  }
#else
  // AHB signals that block/corrupt `tohost` writes or trip `assert_ahb_trxn_aligned`:
  // - 164 (ID 82, `VEER.lsu_haddr`): Forces `HADDR = 0xFFFFFFFF != tohost` & SVA.
  // - 172 (ID 86, `VEER.lsu_hsize`): Forces `lsu_hsize = 3'h7`, failing SVA.
  // - 174 (ID 87, `VEER.lsu_htrans`): Forces continuous non-idle AHB transfers.
  // - 176 (ID 88, `VEER.lsu_hwrite`): Latched at `1'b1` (`buf_write`) after the
  //               `tohost = cmd` store, and any AHB read while `lsu_hwrite` is
  //               forced to `1'b1` deadlocks `lsu_axi4_to_ahb` in `CMD_RD`
  //               (`buf_state_en` requires `~ahb_hwrite_q`), blocking `tohost`.
  // - 178 (ID 89, `VEER.lsu_hwdata`): Forces `HWDATA = '1` (0xFF = finish).
  if (id == (82 * 2) || id == (86 * 2) || id == (87 * 2) ||
      id == (88 * 2) || id == (89 * 2)) {
    return true;
  }
#endif

  return false;
}

/**
 * Returns `true` if `id` (`old_boot_count`) corresponds to a signal that is
 * hardcoded to `'1` (all ones) in RTL, or driven to `'1` when the DMA slave
 * buffers are idle. Because `tb_top.sv` injects faults via `force <sig> = '1`,
 * forcing `'1` onto a signal that is already `'1` in RTL creates no difference
 * between `VEER` and `LOCKSTEP_CORE` (`'1 == '1`).
 */
static bool is_hardcoded_one_in_rtl(uint32_t id) {
#if (SDVT_AHB == 0)
  // AXI signals hardcoded to `'1` (or idle-high `'1` on DMA slave) in RTL:
  // - 228 (ID 114, `VEER.lsu_axi_wlast`): Hardcoded to `'1` in `el2_lsu_bus_buffer.sv`
  //                (`assign lsu_axi_wlast = '1;`).
  // - 230 (ID 115, `VEER.lsu_axi_bready`): Hardcoded to `1'b1` in `el2_lsu_bus_buffer.sv`
  //                (`assign lsu_axi_bready = 1;`).
  // - 304 (ID 152, `VEER.ifu_axi_arcache`): Hardcoded to `4'b1111` (`'1`) in
  //                `el2_ifu_mem_ctl.sv` (`assign ifu_axi_arcache[3:0] = 4'b1111;`).
  // - 310 (ID 155, `VEER.ifu_axi_rready`): Hardcoded to `1'b1` in `el2_ifu_mem_ctl.sv`
  //                (`assign ifu_axi_rready = 1'b1;`).
  // - 328 (ID 164, `VEER.sb_axi_awcache`): Hardcoded to `4'b1111` (`'1`) in `el2_dbg.sv`
  //                (`assign sb_axi_awcache[3:0] = 4'b1111;`).
  // - 340 (ID 170, `VEER.sb_axi_wlast`): Hardcoded to `'1` in `el2_dbg.sv`
  //                (`assign sb_axi_wlast = '1;`).
  // - 342 (ID 171, `VEER.sb_axi_bready`): Hardcoded to `1'b1` in `el2_dbg.sv`
  //                (`assign sb_axi_bready = 1'b1;`).
  // - 366 (ID 183, `VEER.sb_axi_rready`): Hardcoded to `1'b1` in `el2_dbg.sv`
  //                (`assign sb_axi_rready = 1'b1;`).
  // - 368 (ID 184, `VEER.dma_axi_awready`): Driven to `1'b1` in `el2_dma_ctrl.sv`
  //                (`assign dma_axi_awready = ~(wrbuf_vld & ~wrbuf_cmd_sent);`).
  // - 370 (ID 185, `VEER.dma_axi_wready`): Driven to `1'b1` in `el2_dma_ctrl.sv`
  //                (`assign dma_axi_wready = ~(wrbuf_data_vld & ~wrbuf_cmd_sent);`).
  // - 378 (ID 189, `VEER.dma_axi_arready`): Driven to `1'b1` in `el2_dma_ctrl.sv`
  //                (`assign dma_axi_arready = ~(rdbuf_vld & ~rdbuf_cmd_sent);`).
  // - 388 (ID 194, `VEER.dma_axi_rlast`): Hardcoded to `1'b1` in `el2_dma_ctrl.sv`
  //                (`assign dma_axi_rlast = 1'b1;`).
  if (id == (114 * 2) || id == (115 * 2) || id == (152 * 2) ||
      id == (155 * 2) || id == (164 * 2) || id == (170 * 2) ||
      id == (171 * 2) || id == (183 * 2) || id == (184 * 2) ||
      id == (185 * 2) || id == (189 * 2) || id == (194 * 2)) {
    return true;
  }
#else
  // AHB signal tied to `1'b1` when DMA slave is idle in RTL:
  // - 132 (ID 66, `VEER.dma_hreadyin`): Tied to `dma_hreadyout` (`1'b1` in
  //               `el2_veer_wrapper.sv` / `el2_dma_ctrl.sv`), and `dma_hreadyin`
  //               is an input port not wired to `dcls_cmp`.
  if (id == (66 * 2)) {
    return true;
  }
#endif
  return false;
}

/**
 * Dummy function in `.text` (`0x80000000`) to exercise the IFU external bus and
 * ICache when testing Main Core IFU/ICache input signals.
 */
__attribute__((noinline))
static void probe_ifu_text_fetch(void) {
  __asm__ volatile (
      ".rept 8\n"
      "nop\n"
      ".endr\n"
  );
}

static void (*volatile probe_ifu_fn)(void) = probe_ifu_text_fetch;

/**
 * Executes the fault injection and observation window from ICCM (`.text.nmi`)
 * so that IFU output forces or DCCM read data forces do not break instruction
 * fetching or stack accesses prior to `_trap_handler`.
 */
__attribute__((section(".text.nmi"), noinline))
static void inject_and_wait(uint32_t old_boot_count) {
  if (old_boot_count == (13 * 2)) {
    // `ID 13` (`VEER.ic_rd_data`): Mark region 0x80000000 cacheable in `mrac`
    // (`0x7c0`), enable the ICache in `mfdc` (`0x7f9`), and warm up the cache
    // line for `probe_ifu_text_fetch` before injecting the fault.
    write_csr(0x7c0, 0x00010000UL);
    write_csr(0x7f9, 0x00000001UL);
    __asm__ volatile ("fence.i");
    probe_ifu_fn();
  }
#if (SDVT_AHB == 0)
  if (old_boot_count == (108 * 2)) {
    // `ID 108` (`VEER.lsu_axi_awcache`): In `el2_lsu_bus_buffer.sv`,
    // `lsu_axi_awcache` is `obuf_sideeffect ? 4'b0 : 4'b1111`. Mark region `0xd`
    // (`tohost` at `0xd0580000`) as side-effect in `mrac` (`0x7c0`, bit 27) so
    // `LOCKSTEP_CORE` drives `lsu_axi_awcache = 4'b0000` while `VEER` is forced
    // to `4'b1111`.
    write_csr(0x7c0, 0x08000000UL);
    __asm__ volatile ("fence");
  }
#endif

  uint32_t cmd = ((old_boot_count >> 1) << 8) |
                 ((old_boot_count & 1U) ? CMD_INJ_LOCKSTEP : CMD_INJ_VEER);
  tohost = cmd;

  if (old_boot_count == (2 * 2)) {
    // `ID 2` (`VEER.nmi_vec`): Trigger NMI so Main Core & Shadow Core jump to
    // their respective `nmi_vec` addresses.
    tohost = SET_NMI_INT;
  } else if (old_boot_count == (9 * 2) || old_boot_count == (10 * 2)) {
    // `IDs 9, 10` (`VEER.dccm_rd_data_lo/hi`): Perform an unaligned 32-bit
    // DCCM load at offset +2 straddling `dccm_probe[0]` (`dccm_rd_data_lo`)
    // and `dccm_probe[1]` (`dccm_rd_data_hi`).
    uint32_t val;
    __asm__ volatile (
        "lw %0, 2(%1)\n\t"
        : "=r"(val)
        : "r"(&dccm_probe[0])
    );
    (void)val;
  } else if (old_boot_count == (13 * 2) || old_boot_count == (18 * 2) ||
             old_boot_count == (19 * 2) ||
#if (SDVT_AHB == 0)
             old_boot_count == (63 * 2) || old_boot_count == (65 * 2) ||
             old_boot_count == (66 * 2) || old_boot_count == (67 * 2)
#else
             old_boot_count == (48 * 2) || old_boot_count == (50 * 2)
#endif
  ) {
    // Exercise `.text` (`0x80000000`) fetch via 32-bit indirect call so Main
    // Core samples the forced ICache / IFU bus input signal.
    probe_ifu_fn();
#if (SDVT_AHB == 0)
  } else if (old_boot_count == (108 * 2)) {
    // Issue a dummy write to `tohost` (`0xd0580000`, side-effect region `0xd`)
    // so `LOCKSTEP_CORE.lsu_axi_awcache` transitions to `4'b0000` while
    // `VEER.lsu_axi_awcache` is forced to `4'b1111`.
    tohost = cmd;
#endif
  }

  for (uint32_t slp = 0; slp < 20; slp++) {
    __asm__ volatile ("nop");
  }

  tohost = CMD_INJ_CLEAR;

  for (uint32_t slp = 0; slp < 20; slp++) {
    __asm__ volatile ("nop");
  }
}

static void (*volatile inject_and_wait_fn)(uint32_t) = inject_and_wait;

int main(void) {
  uint32_t old_boot_count = boot_count;

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
    printf("trap #%0d [signal ID %0d (case %0d)]! mstatus=0x%08X, mcause=0x%08X, mepc=0x%08X\n",
           (unsigned int)injected_trap_count, (unsigned int)last_trap_id,
           (unsigned int)(last_trap_id >> 1), (unsigned int)last_mstatus,
           (unsigned int)last_mcause, (unsigned int)last_mepc);
  }

  printf("Starting DCLS Skipped Signals Test (boot_count=%0d)\n",
         (unsigned int)old_boot_count);

  if (old_boot_count < MAX_BOOT_COUNT) {
    __asm__ volatile (
        "li t0, 0x800\n\t"
        "csrc mie, t0\n\t"
        : : : "t0"
    );

    *threshold     = 1;
    gateway[2]     = (1U << 1) | 0U;
    clr_gateway[2] = 0;
    priority[2]    = 7;
    enable[2]      = 1;

    __asm__ volatile (
        "li t0, 0x800\n\t"
        "csrs mie, t0\n\t"
        "li t0, 0x8\n\t"
        "csrs mstatus, t0\n\t"
        : : : "t0"
    );
  }

  while (old_boot_count < MAX_BOOT_COUNT) {
    old_boot_count = boot_count;
    boot_count++;

    if (!is_skipped_in_dcls(old_boot_count)) {
      continue;
    }

    if (is_core_freezing_or_bus_blocking(old_boot_count)) {
      printf("Skipping core-freezing/bus-blocking signal of ID %0d (case %0d)\n",
             (unsigned int)old_boot_count, (unsigned int)(old_boot_count >> 1));
      continue;
    }

    if (is_hardcoded_one_in_rtl(old_boot_count)) {
      printf("Skipping hardcoded-to-1 in RTL signal of ID %0d (case %0d)\n",
             (unsigned int)old_boot_count, (unsigned int)(old_boot_count >> 1));
      continue;
    }

    printf("Injecting error into skipped signal of ID %0d (case %0d)\n",
           (unsigned int)old_boot_count, (unsigned int)(old_boot_count >> 1));
    expected_trap_id = old_boot_count;
    inject_and_wait_fn(old_boot_count);

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
