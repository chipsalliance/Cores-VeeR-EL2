/* SPDX-License-Identifier: Apache-2.0
 * Copyright 2026 Google LLC
 *
 * Dual-Core Lockstep I/O Signal Fault Injection Sweep Test
 * Author: Samip Modi (samipmodi@google.com)
 *
 * Description:
 * This test performs a comprehensive Dual-Core Lockstep (DCLS) fault injection
 * sweep across both Main Core (`VEER`) and Shadow Core (`LOCKSTEP_CORE`) input
 * and output signals wired in `testbench/tb_top.sv` (`inject_lockstep_error`,
 * signal IDs `0 .. MAX_BOOT_COUNT - 1`), strictly requiring every injected
 * signal to assert DCLS `corruption_detected_o`, trigger a trap, and recover
 * across warm reset (`CMD_RST`). Internal CCM/ICache SRAM, ECC telemetry, and
 * debug ports in `el2_lockstep_pkg.sv` that are not wired into `tb_top.sv`
 * `0..194` (along with unassigned gap cases `11, 16, 17`) are verified
 * separately by `dcls_ecc_asymmetric`, `dcls_debug`, and `dcls_internal_state`.
 *
 * Unlike the baseline `dcls.c` test (which skips execution-breaking Main Core
 * signals and allows unstimulated input forces to fall through without
 * trapping), this test:
 * 1. Relocates `_trap_handler`, `_nmi`, `trap_handler()`, and `inject_and_wait()`
 *    into ICCM (`.text.nmi` at `0xee000000`), and provides `_text_trap_handler`
 *    in `.text` (`0x80000000`) for Main Core ICCM ECC fault recovery (`ID 24`).
 * 2. Centralizes all `tb_top.sv` case classifications (`0..194` for AXI4,
 *    `0..92` for AHB-Lite) and stimulus selectors into `kDclsCaseTable[]`, and
 *    verifies at both compile time (`static_assert`) and Boot 0
 *    (`verify_case_table_sanity()`) that the configured bus mode (`SDVT_AHB`),
 *    table ordering, and injectable signal count match `EXPECTED_INJECTED_TRAPS`.
 * 3. Actively stimulates CPU-facing core and bus input signals during the fault
 *    window so that both `VEER` and `LOCKSTEP_CORE` input forces propagate to
 *    core outputs and assert `corruption_detected_o`.
 * 4. Verifies across every `CMD_RST` reset (`expected_trap_id`, `last_trap_valid`,
 *    and PIC `MEIP[2]` via `last_dcls_irq_pending`) and at test completion
 *    (`injected_trap_count == EXPECTED_INJECTED_TRAPS`) that 100% of injected
 *    signals asserted DCLS `corruption_detected_o` and trapped, preventing false
 *    passes if DCLS corruption detection is disabled (`0x94`).
 *
 * Test Phases:
 * 1. Phase 1 (Upfront Sanity Check, PIC & Interrupt Initialization):
 *    - On Boot 0, validates `kDclsCaseTable[]` ordering and confirms that the
 *      sum of injectable `VEER` and `LOCKSTEP_CORE` entries matches
 *      `EXPECTED_INJECTED_TRAPS` (`248` for AXI4, `116` for AHB-Lite).
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
 *    - Case 13 (`IDs 26, 27`, `ic_rd_data`): Marks `.text` (`0x80000000`)
 *      cacheable in `mrac` (`0x7c0`), warms up `probe_ifu_text_fetch()`, and
 *      re-fetches under fault injection.
 *    - Cases 18–19 (`ic_rd_hit`, `ic_tag_perr`) and IFU AXI/AHB inputs
 *      (`ifu_axi_arready..ifu_axi_rresp`, `hrdata`, `hresp`): Invokes
 *      `probe_ifu_text_fetch()` from ICCM to sample forced IFU inputs.
 *    - LSU AXI/AHB write/read inputs (`lsu_axi_bvalid`, `lsu_axi_bresp`,
 *      `lsu_axi_rvalid`, `lsu_axi_rid`, `lsu_axi_rdata`, `lsu_axi_rresp`,
 *      `lsu_hrdata`, `lsu_hresp`) and AHB `LOCKSTEP_CORE.lsu_hwrite`:
 *      Executes targeted external bus stores/loads during the fault window.
 *
 * 3. Phase 3 (Main Core & Shadow Core Output Signals Sweep):
 *    - Sweeps all testable core and bus outputs across `VEER` and `LOCKSTEP_CORE`
 *      (including `lsu_axi_awcache` and `lsu_axi_arcache` on both cores by
 *      marking region `0xd` side-effect in `mrac`), verifying that every
 *      injected signal asserts `corruption_detected_o` (`MEIP[2]`) and traps.
 *
 * 4. Phase 4 (Final Lockstep Verification & Completion):
 *    - Asserts `injected_trap_count == EXPECTED_INJECTED_TRAPS` and injects a
 *      final lockstep fault (`(1 << 8) | CMD_INJ_LOCKSTEP`) for the `0xfe`
 *      `tohost` exit check.
 */

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include "defines.h"  // Generated.

#ifndef asm
#define asm __asm__
#endif

#ifndef static_assert
#define static_assert _Static_assert
#endif

#ifndef RV_LOCKSTEP_ENABLE
#error "dcls_io_sweep requires RV_LOCKSTEP_ENABLE"
#endif

#if (SDVT_AHB == 0)
#if !defined(RV_BUILD_AXI4) || defined(RV_BUILD_AHB_LITE)
#error "Bus mode mismatch: SDVT_AHB == 0 requires RV_BUILD_AXI4 without RV_BUILD_AHB_LITE"
#endif
#elif (SDVT_AHB == 1)
#if !defined(RV_BUILD_AHB_LITE) || defined(RV_BUILD_AXI4)
#error "Bus mode mismatch: SDVT_AHB == 1 requires RV_BUILD_AHB_LITE without RV_BUILD_AXI4"
#endif
#else
#error "Invalid SDVT_AHB value: expected 0 (AXI4) or 1 (AHB-Lite)"
#endif

#define CSR_STR_(x) #x
#define CSR_STR(x)  CSR_STR_(x)

/**
 * Reads a RISC-V Control and Status Register (CSR).
 */
#define read_csr(csr) ({                                   \
  unsigned long res_;                                      \
  asm volatile("csrr %0, " CSR_STR(csr) : "=r"(res_));     \
  res_;                                                    \
})

/**
 * Writes a value to a RISC-V Control and Status Register (CSR).
 */
#define write_csr(csr, val) do {                           \
  asm volatile("csrw " CSR_STR(csr) ", %0" :: "r"(val));   \
} while (0)

#define CSR_VEER_MRAC    0x7c0
#define CSR_VEER_MEIVT   0xbc8

#define CMD_INJ_VEER     0x91
#define CMD_INJ_LOCKSTEP 0x92
#define CMD_INJ_CLEAR    0x95
#define CMD_RST          0x96
#define SET_NMI_INT      0x183
#define CLEAR_NMI_INT    0x182

// `MAX_BOOT_COUNT` and `EXPECTED_INJECTED_TRAPS` are tied to the DCLS signal
// injection case tables in `testbench/tb_top.sv` (`inject_lockstep_error`):
// - AXI (`SDVT_AHB == 0`): 195 signal pairs (`0..389`), of which 248 real core
//   input/output signals are injected and must each trigger a DCLS trap.
// - AHB (`SDVT_AHB == 1`): 93 signal pairs (`0..185`), of which 116 real core
//   input/output signals are injected and must each trigger a DCLS trap.
#if (SDVT_AHB == 0)
#define MAX_BOOT_COUNT          (195U * 2U)
#define EXPECTED_INJECTED_TRAPS 248U
#else
#define MAX_BOOT_COUNT          (93U * 2U)
#define EXPECTED_INJECTED_TRAPS 116U
#endif

/**
 * Per-core disposition for a `tb_top.sv` fault injection case (`case_num`).
 */
typedef enum dcls_action {
  /** Inject fault on this core and require a DCLS trap + `MEIP[2]`. */
  kDclsActionInject = 0,
  /**
   * Skip on Main Core (`VEER`): forcing `'1` freezes `active_l2clk`, enters
   * Debug Mode (latching `dbg_detected`), or blocks `tohost` mailbox writes.
   */
  kDclsActionSkipCoreFreezing,
  /** Skip on both cores: signal is already tied/driven to `'1` (`'1 == '1`). */
  kDclsActionSkipHardcodedOne,
  /** Skip on both cores: unassigned case number in `tb_top.sv` (`11, 16, 17`). */
  kDclsActionSkipUnassignedGap,
  /**
   * Skip on both cores: unconnected RTL input, DFT scan pin, Debug-Mode-only
   * input, or idle external debug/DMA bus input while valid/select is `0`.
   */
  kDclsActionSkipUnconnectedOrIdle,
} dcls_action_t;

/**
 * Targeted stimulus executed during the fault injection window so forced inputs
 * or state-dependent outputs propagate to the DCLS comparator.
 */
typedef enum dcls_stim {
  /** Passive execution in ICCM (`.text.nmi`). */
  kDclsStimDefault = 0,
  /** Issue `CMD_RST` while `LOCKSTEP_CORE.rst_vec` is forced (`Case 0`). */
  kDclsStimWarmReset,
  /** Issue `SET_NMI_INT` while `nmi_vec` is forced (`Case 2`). */
  kDclsStimNmiVec,
  /** Read `mhartid` and store to `dccm_probe[0]` (`Case 5`). */
  kDclsStimCoreId,
  /** Unaligned 32-bit DCCM load/store across `dccm_probe[0..1]` (`Cases 9, 10`). */
  kDclsStimDccmUnalignedLoad,
  /** ICCM ECC fault (`Case 12`): `.text` LSU load on `VEER`, ICCM fetch on Shadow. */
  kDclsStimIccmEcc,
  /** Warm up ICache (`mrac = 0x00010000`) and fetch `.text` (`Case 13`). */
  kDclsStimIcacheFetch,
  /** Indirect call to `probe_ifu_text_fetch()` in `.text` (`0x80000000`). */
  kDclsStimIfuTextFetch,
  /** Two non-merged stores to `0xee003fc0` via `axi_lsu_dma_bridge` (`Case 50`). */
  kDclsStimAxiBvalidDoubleStore,
  /** Non-`tohost` external store to `0x80001000` followed by `fence`. */
  kDclsStimExtBusWrite,
  /** Prime `0x80000000` read, then read `0xee000000` via DMA bridge (`Case 54`). */
  kDclsStimAxiRvalidIccmRead,
  /** External AXI read from `0x80000008` (`Cases 55..57`). */
  kDclsStimExtAxiRead,
  /** Prime `probe_ifu_ret_sled()`, then call `probe_ifu_text_fetch()` (`Case 64`). */
  kDclsStimIfuRvalidRetSled,
  /** Mark `tohost` region `0xd` side-effect in `mrac` (`Cases 108, 124`). */
  kDclsStimAxiCacheSideEffect,
  /** External AHB read from `0x80000000` (`Cases 51, 88`). */
  kDclsStimExtAhbRead,
} dcls_stim_t;

/**
 * Descriptor for a single `tb_top.sv` fault injection case (`case_num`),
 * covering both `id = case_num * 2` (`VEER`) and `id = case_num * 2 + 1`
 * (`LOCKSTEP_CORE`).
 */
typedef struct dcls_case_desc {
  uint16_t case_num;
  uint8_t veer_action;
  uint8_t shadow_action;
  uint8_t stim;
  const char *signal_name;
} dcls_case_desc_t;

#define DCLS_CASE(case_no, veer_act, shadow_act, stim_kind, sig_name) \
  {                                                                   \
    .case_num = (case_no),                                            \
    .veer_action = (veer_act),                                        \
    .shadow_action = (shadow_act),                                    \
    .stim = (stim_kind),                                              \
    .signal_name = (sig_name),                                        \
  }

/**
 * Central lookup table mapping every `tb_top.sv` `inject_corruption` case
 * (`0..194` for AXI4, `0..92` for AHB-Lite) to its per-core action and
 * stimulus kind.
 */
static const dcls_case_desc_t kDclsCaseTable[] = {
  // --- Common Core Inputs (`0..31`) ---
  DCLS_CASE(0,  kDclsActionSkipCoreFreezing,      kDclsActionInject,                kDclsStimWarmReset,         "rst_vec"),
  DCLS_CASE(1,  kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,           "nmi_int"),
  DCLS_CASE(2,  kDclsActionInject,                kDclsActionInject,                kDclsStimNmiVec,            "nmi_vec"),
  DCLS_CASE(3,  kDclsActionSkipCoreFreezing,      kDclsActionInject,                kDclsStimDefault,           "i_cpu_halt_req"),
  DCLS_CASE(4,  kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,           "i_cpu_run_req"),
  DCLS_CASE(5,  kDclsActionInject,                kDclsActionInject,                kDclsStimCoreId,            "core_id"),
  DCLS_CASE(6,  kDclsActionSkipCoreFreezing,      kDclsActionInject,                kDclsStimDefault,           "mpc_debug_halt_req"),
  DCLS_CASE(7,  kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,           "mpc_debug_run_req"),
  DCLS_CASE(8,  kDclsActionSkipHardcodedOne,      kDclsActionSkipHardcodedOne,      kDclsStimDefault,           "mpc_reset_run_req"),
  DCLS_CASE(9,  kDclsActionInject,                kDclsActionInject,                kDclsStimDccmUnalignedLoad, "dccm_rd_data_lo"),
  DCLS_CASE(10, kDclsActionInject,                kDclsActionInject,                kDclsStimDccmUnalignedLoad, "dccm_rd_data_hi"),
  DCLS_CASE(11, kDclsActionSkipUnassignedGap,     kDclsActionSkipUnassignedGap,     kDclsStimDefault,           "unassigned_case_11"),
  DCLS_CASE(12, kDclsActionInject,                kDclsActionInject,                kDclsStimIccmEcc,           "iccm_rd_data_ecc"),
  DCLS_CASE(13, kDclsActionInject,                kDclsActionInject,                kDclsStimIcacheFetch,       "ic_rd_data"),
  DCLS_CASE(14, kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,           "ic_debug_rd_data"),
  DCLS_CASE(15, kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,           "ictag_debug_rd_data"),
  DCLS_CASE(16, kDclsActionSkipUnassignedGap,     kDclsActionSkipUnassignedGap,     kDclsStimDefault,           "unassigned_case_16"),
  DCLS_CASE(17, kDclsActionSkipUnassignedGap,     kDclsActionSkipUnassignedGap,     kDclsStimDefault,           "unassigned_case_17"),
  DCLS_CASE(18, kDclsActionInject,                kDclsActionInject,                kDclsStimIfuTextFetch,      "ic_rd_hit"),
  DCLS_CASE(19, kDclsActionInject,                kDclsActionInject,                kDclsStimIfuTextFetch,      "ic_tag_perr"),
  DCLS_CASE(20, kDclsActionSkipHardcodedOne,      kDclsActionSkipHardcodedOne,      kDclsStimDefault,           "lsu_bus_clk_en"),
  DCLS_CASE(21, kDclsActionSkipHardcodedOne,      kDclsActionSkipHardcodedOne,      kDclsStimDefault,           "ifu_bus_clk_en"),
  DCLS_CASE(22, kDclsActionSkipHardcodedOne,      kDclsActionSkipHardcodedOne,      kDclsStimDefault,           "dbg_bus_clk_en"),
  DCLS_CASE(23, kDclsActionSkipHardcodedOne,      kDclsActionSkipHardcodedOne,      kDclsStimDefault,           "dma_bus_clk_en"),
  DCLS_CASE(24, kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,           "dmi_reg_en"),
  DCLS_CASE(25, kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,           "dmi_reg_addr"),
  DCLS_CASE(26, kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,           "dmi_reg_wr_en"),
  DCLS_CASE(27, kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,           "dmi_reg_wdata"),
  DCLS_CASE(28, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,           "extintsrc_req"),
  DCLS_CASE(29, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,           "timer_int"),
  DCLS_CASE(30, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,           "soft_int"),
  DCLS_CASE(31, kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,           "scan_mode"),

  // --- Common Core Outputs (`32..47`) ---
  DCLS_CASE(32, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,           "o_cpu_halt_ack"),
  DCLS_CASE(33, kDclsActionSkipCoreFreezing,      kDclsActionInject,                kDclsStimDefault,           "o_cpu_halt_status"),
  DCLS_CASE(34, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,           "o_cpu_run_ack"),
  DCLS_CASE(35, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,           "mpc_debug_halt_ack"),
  DCLS_CASE(36, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,           "mpc_debug_run_ack"),
  DCLS_CASE(37, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,           "trace_rv_i_insn_ip"),
  DCLS_CASE(38, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,           "trace_rv_i_address_ip"),
  DCLS_CASE(39, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,           "trace_rv_i_valid_ip"),
  DCLS_CASE(40, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,           "trace_rv_i_exception_ip"),
  DCLS_CASE(41, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,           "trace_rv_i_ecause_ip"),
  DCLS_CASE(42, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,           "trace_rv_i_interrupt_ip"),
  DCLS_CASE(43, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,           "trace_rv_i_tval_ip"),
  DCLS_CASE(44, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,           "dec_tlu_perfcnt0"),
  DCLS_CASE(45, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,           "dec_tlu_perfcnt1"),
  DCLS_CASE(46, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,           "dec_tlu_perfcnt2"),
  DCLS_CASE(47, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,           "dec_tlu_perfcnt3"),

#if (SDVT_AHB == 0)
  // --- AXI4 Bus Inputs (`48..99`) ---
  DCLS_CASE(48,  kDclsActionSkipHardcodedOne,      kDclsActionSkipHardcodedOne,      kDclsStimDefault,              "lsu_axi_awready"),
  DCLS_CASE(49,  kDclsActionSkipHardcodedOne,      kDclsActionSkipHardcodedOne,      kDclsStimDefault,              "lsu_axi_wready"),
  DCLS_CASE(50,  kDclsActionInject,                kDclsActionInject,                kDclsStimAxiBvalidDoubleStore, "lsu_axi_bvalid"),
  DCLS_CASE(51,  kDclsActionInject,                kDclsActionInject,                kDclsStimExtBusWrite,          "lsu_axi_bresp"),
  DCLS_CASE(52,  kDclsActionSkipCoreFreezing,      kDclsActionInject,                kDclsStimExtBusWrite,          "lsu_axi_bid"),
  DCLS_CASE(53,  kDclsActionSkipHardcodedOne,      kDclsActionSkipHardcodedOne,      kDclsStimDefault,              "lsu_axi_arready"),
  DCLS_CASE(54,  kDclsActionInject,                kDclsActionInject,                kDclsStimAxiRvalidIccmRead,    "lsu_axi_rvalid"),
  DCLS_CASE(55,  kDclsActionSkipCoreFreezing,      kDclsActionInject,                kDclsStimExtAxiRead,           "lsu_axi_rid"),
  DCLS_CASE(56,  kDclsActionInject,                kDclsActionInject,                kDclsStimExtAxiRead,           "lsu_axi_rdata"),
  DCLS_CASE(57,  kDclsActionInject,                kDclsActionInject,                kDclsStimExtAxiRead,           "lsu_axi_rresp"),
  DCLS_CASE(58,  kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,              "lsu_axi_rlast"),
  DCLS_CASE(59,  kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,              "ifu_axi_wready"),
  DCLS_CASE(60,  kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,              "ifu_axi_bvalid"),
  DCLS_CASE(61,  kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,              "ifu_axi_bresp"),
  DCLS_CASE(62,  kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,              "ifu_axi_bid"),
  DCLS_CASE(63,  kDclsActionInject,                kDclsActionInject,                kDclsStimIfuTextFetch,         "ifu_axi_arready"),
  DCLS_CASE(64,  kDclsActionInject,                kDclsActionInject,                kDclsStimIfuRvalidRetSled,     "ifu_axi_rvalid"),
  DCLS_CASE(65,  kDclsActionInject,                kDclsActionInject,                kDclsStimIfuTextFetch,         "ifu_axi_rid"),
  DCLS_CASE(66,  kDclsActionInject,                kDclsActionInject,                kDclsStimIfuTextFetch,         "ifu_axi_rdata"),
  DCLS_CASE(67,  kDclsActionInject,                kDclsActionInject,                kDclsStimIfuTextFetch,         "ifu_axi_rresp"),
  DCLS_CASE(68,  kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,              "ifu_axi_rlast"),
  DCLS_CASE(69,  kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,              "sb_axi_awready"),
  DCLS_CASE(70,  kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,              "sb_axi_wready"),
  DCLS_CASE(71,  kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,              "sb_axi_bvalid"),
  DCLS_CASE(72,  kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,              "sb_axi_bresp"),
  DCLS_CASE(73,  kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,              "sb_axi_bid"),
  DCLS_CASE(74,  kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,              "sb_axi_arready"),
  DCLS_CASE(75,  kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,              "sb_axi_rvalid"),
  DCLS_CASE(76,  kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,              "sb_axi_rid"),
  DCLS_CASE(77,  kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,              "sb_axi_rdata"),
  DCLS_CASE(78,  kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,              "sb_axi_rresp"),
  DCLS_CASE(79,  kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,              "sb_axi_rlast"),
  DCLS_CASE(80,  kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "dma_axi_awvalid"),
  DCLS_CASE(81,  kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,              "dma_axi_awid"),
  DCLS_CASE(82,  kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,              "dma_axi_awaddr"),
  DCLS_CASE(83,  kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,              "dma_axi_awsize"),
  DCLS_CASE(84,  kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,              "dma_axi_awprot"),
  DCLS_CASE(85,  kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,              "dma_axi_awlen"),
  DCLS_CASE(86,  kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,              "dma_axi_awburst"),
  DCLS_CASE(87,  kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "dma_axi_wvalid"),
  DCLS_CASE(88,  kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,              "dma_axi_wdata"),
  DCLS_CASE(89,  kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,              "dma_axi_wstrb"),
  DCLS_CASE(90,  kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,              "dma_axi_wlast"),
  DCLS_CASE(91,  kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,              "dma_axi_bready"),
  DCLS_CASE(92,  kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "dma_axi_arvalid"),
  DCLS_CASE(93,  kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,              "dma_axi_arid"),
  DCLS_CASE(94,  kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,              "dma_axi_araddr"),
  DCLS_CASE(95,  kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,              "dma_axi_arsize"),
  DCLS_CASE(96,  kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,              "dma_axi_arprot"),
  DCLS_CASE(97,  kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,              "dma_axi_arlen"),
  DCLS_CASE(98,  kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,              "dma_axi_arburst"),
  DCLS_CASE(99,  kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,              "dma_axi_rready"),

  // --- AXI4 Bus Outputs (`100..194`) ---
  DCLS_CASE(100, kDclsActionSkipCoreFreezing,      kDclsActionInject,                kDclsStimDefault,              "lsu_axi_awvalid"),
  DCLS_CASE(101, kDclsActionSkipCoreFreezing,      kDclsActionInject,                kDclsStimDefault,              "lsu_axi_awid"),
  DCLS_CASE(102, kDclsActionSkipCoreFreezing,      kDclsActionInject,                kDclsStimDefault,              "lsu_axi_awaddr"),
  DCLS_CASE(103, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "lsu_axi_awregion"),
  DCLS_CASE(104, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "lsu_axi_awlen"),
  DCLS_CASE(105, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "lsu_axi_awsize"),
  DCLS_CASE(106, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "lsu_axi_awburst"),
  DCLS_CASE(107, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "lsu_axi_awlock"),
  DCLS_CASE(108, kDclsActionInject,                kDclsActionInject,                kDclsStimAxiCacheSideEffect,   "lsu_axi_awcache"),
  DCLS_CASE(109, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "lsu_axi_awprot"),
  DCLS_CASE(110, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "lsu_axi_awqos"),
  DCLS_CASE(111, kDclsActionSkipCoreFreezing,      kDclsActionInject,                kDclsStimDefault,              "lsu_axi_wvalid"),
  DCLS_CASE(112, kDclsActionSkipCoreFreezing,      kDclsActionInject,                kDclsStimDefault,              "lsu_axi_wdata"),
  DCLS_CASE(113, kDclsActionSkipCoreFreezing,      kDclsActionInject,                kDclsStimDefault,              "lsu_axi_wstrb"),
  DCLS_CASE(114, kDclsActionSkipHardcodedOne,      kDclsActionSkipHardcodedOne,      kDclsStimDefault,              "lsu_axi_wlast"),
  DCLS_CASE(115, kDclsActionSkipHardcodedOne,      kDclsActionSkipHardcodedOne,      kDclsStimDefault,              "lsu_axi_bready"),
  DCLS_CASE(116, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "lsu_axi_arvalid"),
  DCLS_CASE(117, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "lsu_axi_arid"),
  DCLS_CASE(118, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "lsu_axi_araddr"),
  DCLS_CASE(119, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "lsu_axi_arregion"),
  DCLS_CASE(120, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "lsu_axi_arlen"),
  DCLS_CASE(121, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "lsu_axi_arsize"),
  DCLS_CASE(122, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "lsu_axi_arburst"),
  DCLS_CASE(123, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "lsu_axi_arlock"),
  DCLS_CASE(124, kDclsActionInject,                kDclsActionInject,                kDclsStimAxiCacheSideEffect,   "lsu_axi_arcache"),
  DCLS_CASE(125, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "lsu_axi_arprot"),
  DCLS_CASE(126, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "lsu_axi_arqos"),
  DCLS_CASE(127, kDclsActionSkipHardcodedOne,      kDclsActionSkipHardcodedOne,      kDclsStimDefault,              "lsu_axi_rready"),
  DCLS_CASE(128, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "ifu_axi_awvalid"),
  DCLS_CASE(129, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "ifu_axi_awid"),
  DCLS_CASE(130, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "ifu_axi_awaddr"),
  DCLS_CASE(131, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "ifu_axi_awregion"),
  DCLS_CASE(132, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "ifu_axi_awlen"),
  DCLS_CASE(133, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "ifu_axi_awsize"),
  DCLS_CASE(134, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "ifu_axi_awburst"),
  DCLS_CASE(135, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "ifu_axi_awlock"),
  DCLS_CASE(136, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "ifu_axi_awcache"),
  DCLS_CASE(137, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "ifu_axi_awprot"),
  DCLS_CASE(138, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "ifu_axi_awqos"),
  DCLS_CASE(139, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "ifu_axi_wvalid"),
  DCLS_CASE(140, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "ifu_axi_wdata"),
  DCLS_CASE(141, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "ifu_axi_wstrb"),
  DCLS_CASE(142, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "ifu_axi_wlast"),
  DCLS_CASE(143, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "ifu_axi_bready"),
  DCLS_CASE(144, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "ifu_axi_arvalid"),
  DCLS_CASE(145, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "ifu_axi_arid"),
  DCLS_CASE(146, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "ifu_axi_araddr"),
  DCLS_CASE(147, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "ifu_axi_arregion"),
  DCLS_CASE(148, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "ifu_axi_arlen"),
  DCLS_CASE(149, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "ifu_axi_arsize"),
  DCLS_CASE(150, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "ifu_axi_arburst"),
  DCLS_CASE(151, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "ifu_axi_arlock"),
  DCLS_CASE(152, kDclsActionSkipHardcodedOne,      kDclsActionSkipHardcodedOne,      kDclsStimDefault,              "ifu_axi_arcache"),
  DCLS_CASE(153, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "ifu_axi_arprot"),
  DCLS_CASE(154, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "ifu_axi_arqos"),
  DCLS_CASE(155, kDclsActionSkipHardcodedOne,      kDclsActionSkipHardcodedOne,      kDclsStimDefault,              "ifu_axi_rready"),
  DCLS_CASE(156, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "sb_axi_awvalid"),
  DCLS_CASE(157, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "sb_axi_awid"),
  DCLS_CASE(158, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "sb_axi_awaddr"),
  DCLS_CASE(159, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "sb_axi_awregion"),
  DCLS_CASE(160, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "sb_axi_awlen"),
  DCLS_CASE(161, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "sb_axi_awsize"),
  DCLS_CASE(162, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "sb_axi_awburst"),
  DCLS_CASE(163, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "sb_axi_awlock"),
  DCLS_CASE(164, kDclsActionSkipHardcodedOne,      kDclsActionSkipHardcodedOne,      kDclsStimDefault,              "sb_axi_awcache"),
  DCLS_CASE(165, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "sb_axi_awprot"),
  DCLS_CASE(166, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "sb_axi_awqos"),
  DCLS_CASE(167, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "sb_axi_wvalid"),
  DCLS_CASE(168, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "sb_axi_wdata"),
  DCLS_CASE(169, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "sb_axi_wstrb"),
  DCLS_CASE(170, kDclsActionSkipHardcodedOne,      kDclsActionSkipHardcodedOne,      kDclsStimDefault,              "sb_axi_wlast"),
  DCLS_CASE(171, kDclsActionSkipHardcodedOne,      kDclsActionSkipHardcodedOne,      kDclsStimDefault,              "sb_axi_bready"),
  DCLS_CASE(172, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "sb_axi_arvalid"),
  DCLS_CASE(173, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "sb_axi_arid"),
  DCLS_CASE(174, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "sb_axi_araddr"),
  DCLS_CASE(175, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "sb_axi_arregion"),
  DCLS_CASE(176, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "sb_axi_arlen"),
  DCLS_CASE(177, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "sb_axi_arsize"),
  DCLS_CASE(178, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "sb_axi_arburst"),
  DCLS_CASE(179, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "sb_axi_arlock"),
  DCLS_CASE(180, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "sb_axi_arcache"),
  DCLS_CASE(181, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "sb_axi_arprot"),
  DCLS_CASE(182, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "sb_axi_arqos"),
  DCLS_CASE(183, kDclsActionSkipHardcodedOne,      kDclsActionSkipHardcodedOne,      kDclsStimDefault,              "sb_axi_rready"),
  DCLS_CASE(184, kDclsActionSkipHardcodedOne,      kDclsActionSkipHardcodedOne,      kDclsStimDefault,              "dma_axi_awready"),
  DCLS_CASE(185, kDclsActionSkipHardcodedOne,      kDclsActionSkipHardcodedOne,      kDclsStimDefault,              "dma_axi_wready"),
  DCLS_CASE(186, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "dma_axi_bvalid"),
  DCLS_CASE(187, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "dma_axi_bresp"),
  DCLS_CASE(188, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "dma_axi_bid"),
  DCLS_CASE(189, kDclsActionSkipHardcodedOne,      kDclsActionSkipHardcodedOne,      kDclsStimDefault,              "dma_axi_arready"),
  DCLS_CASE(190, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "dma_axi_rvalid"),
  DCLS_CASE(191, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "dma_axi_rid"),
  DCLS_CASE(192, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "dma_axi_rdata"),
  DCLS_CASE(193, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,              "dma_axi_rresp"),
  DCLS_CASE(194, kDclsActionSkipHardcodedOne,      kDclsActionSkipHardcodedOne,      kDclsStimDefault,              "dma_axi_rlast"),
#else
  // --- AHB-Lite Bus Inputs (`48..66`) ---
  DCLS_CASE(48, kDclsActionInject,                kDclsActionInject,                kDclsStimIfuTextFetch, "hrdata"),
  DCLS_CASE(49, kDclsActionSkipHardcodedOne,      kDclsActionSkipHardcodedOne,      kDclsStimDefault,      "hready"),
  DCLS_CASE(50, kDclsActionInject,                kDclsActionInject,                kDclsStimIfuTextFetch, "hresp"),
  DCLS_CASE(51, kDclsActionInject,                kDclsActionInject,                kDclsStimExtAhbRead,   "lsu_hrdata"),
  DCLS_CASE(52, kDclsActionSkipHardcodedOne,      kDclsActionSkipHardcodedOne,      kDclsStimDefault,      "lsu_hready"),
  DCLS_CASE(53, kDclsActionInject,                kDclsActionInject,                kDclsStimExtBusWrite,  "lsu_hresp"),
  DCLS_CASE(54, kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,      "sb_hrdata"),
  DCLS_CASE(55, kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,      "sb_hready"),
  DCLS_CASE(56, kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,      "sb_hresp"),
  DCLS_CASE(57, kDclsActionInject,                kDclsActionInject,                kDclsStimExtBusWrite,  "dma_hsel"),
  DCLS_CASE(58, kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,      "dma_haddr"),
  DCLS_CASE(59, kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,      "dma_hburst"),
  DCLS_CASE(60, kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,      "dma_hmastlock"),
  DCLS_CASE(61, kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,      "dma_hprot"),
  DCLS_CASE(62, kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,      "dma_hsize"),
  DCLS_CASE(63, kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,      "dma_htrans"),
  DCLS_CASE(64, kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,      "dma_hwrite"),
  DCLS_CASE(65, kDclsActionSkipUnconnectedOrIdle, kDclsActionSkipUnconnectedOrIdle, kDclsStimDefault,      "dma_hwdata"),
  DCLS_CASE(66, kDclsActionSkipHardcodedOne,      kDclsActionSkipHardcodedOne,      kDclsStimDefault,      "dma_hreadyin"),

  // --- AHB-Lite Bus Outputs (`67..92`) ---
  DCLS_CASE(67, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,      "haddr"),
  DCLS_CASE(68, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,      "hburst"),
  DCLS_CASE(69, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,      "hmastlock"),
  DCLS_CASE(70, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,      "hprot"),
  DCLS_CASE(71, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,      "hsize"),
  DCLS_CASE(72, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,      "htrans"),
  DCLS_CASE(73, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,      "hwrite"),
  DCLS_CASE(74, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,      "sb_haddr"),
  DCLS_CASE(75, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,      "sb_hburst"),
  DCLS_CASE(76, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,      "sb_hmastlock"),
  DCLS_CASE(77, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,      "sb_hprot"),
  DCLS_CASE(78, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,      "sb_hsize"),
  DCLS_CASE(79, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,      "sb_htrans"),
  DCLS_CASE(80, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,      "sb_hwrite"),
  DCLS_CASE(81, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,      "sb_hwdata"),
  DCLS_CASE(82, kDclsActionSkipCoreFreezing,      kDclsActionInject,                kDclsStimDefault,      "lsu_haddr"),
  DCLS_CASE(83, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,      "lsu_hburst"),
  DCLS_CASE(84, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,      "lsu_hmastlock"),
  DCLS_CASE(85, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,      "lsu_hprot"),
  DCLS_CASE(86, kDclsActionSkipCoreFreezing,      kDclsActionInject,                kDclsStimDefault,      "lsu_hsize"),
  DCLS_CASE(87, kDclsActionSkipCoreFreezing,      kDclsActionInject,                kDclsStimDefault,      "lsu_htrans"),
  DCLS_CASE(88, kDclsActionSkipCoreFreezing,      kDclsActionInject,                kDclsStimExtAhbRead,   "lsu_hwrite"),
  DCLS_CASE(89, kDclsActionSkipCoreFreezing,      kDclsActionInject,                kDclsStimDefault,      "lsu_hwdata"),
  DCLS_CASE(90, kDclsActionInject,                kDclsActionInject,                kDclsStimDefault,      "dma_hrdata"),
  DCLS_CASE(91, kDclsActionSkipHardcodedOne,      kDclsActionSkipHardcodedOne,      kDclsStimDefault,      "dma_hreadyout"),
  DCLS_CASE(92, kDclsActionSkipCoreFreezing,      kDclsActionInject,                kDclsStimDefault,      "dma_hresp"),
#endif
};

static_assert((sizeof(kDclsCaseTable) / sizeof(kDclsCaseTable[0])) ==
                  (MAX_BOOT_COUNT / 2U),
              "kDclsCaseTable size must match MAX_BOOT_COUNT / 2");

/** Saved copy of the first two ICCM words (`0xee000000`) to restore after ECC scrub. */
volatile uint32_t saved_iccm_head[2] __attribute__((section(".dccm.persistent")));

/** Persistent boot counter and initial sync-reset guard in DCCM across `CMD_RST`. */
volatile uint32_t boot_count         __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t initial_reset_done __attribute__((section(".dccm.persistent"))) = 0;

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

/** Persistent trap CSR snapshot and DCLS IRQ status across `CMD_RST`. */
volatile uint32_t expected_trap_id      __attribute__((section(".dccm.persistent"))) = 0xFFFFFFFFU;
volatile uint32_t last_trap_id          __attribute__((section(".dccm.persistent"))) = 0xFFFFFFFFU;
volatile uint32_t last_trap_valid       __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t last_dcls_irq_pending __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t injected_trap_count   __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t last_mstatus          __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t last_mcause           __attribute__((section(".dccm.persistent"))) = 0;
volatile uint32_t last_mepc             __attribute__((section(".dccm.persistent"))) = 0;

extern volatile uint32_t tohost;
extern void _text_trap_handler(void);

static volatile uint32_t *const threshold =
    (volatile uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIPT_OFFSET);
static volatile uint32_t *const gateway =
    (volatile uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIGWCTRL_OFFSET);
static volatile uint32_t *const clr_gateway =
    (volatile uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIGWCLR_OFFSET);
static volatile uint32_t *const priority =
    (volatile uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIPL_OFFSET);
static volatile uint32_t *const enable =
    (volatile uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIE_OFFSET);
static volatile uint32_t *const meip =
    (volatile uint32_t *)(RV_PIC_BASE_ADDR + RV_PIC_MEIP_OFFSET);

/**
 * Performs an upfront Boot-0 sanity check confirming that:
 * 1. The configured bus mode (`SDVT_AHB`) matches the expected signal ID range
 *    (`MAX_BOOT_COUNT` = 390 for AXI4, 186 for AHB-Lite) and `kDclsCaseTable`
 *    has no missing or out-of-order case numbers (`0 .. (MAX_BOOT_COUNT / 2) - 1`).
 * 2. The total number of `kDclsActionInject` slots across `VEER` and
 *    `LOCKSTEP_CORE` in `kDclsCaseTable` equals `EXPECTED_INJECTED_TRAPS`
 *    (`248` for AXI4, `116` for AHB-Lite).
 */
static bool verify_case_table_sanity(void) {
  const uint32_t num_cases =
      (uint32_t)(sizeof(kDclsCaseTable) / sizeof(kDclsCaseTable[0]));
  const uint32_t expected_cases = (SDVT_AHB == 0) ? 195U : 93U;
  if (num_cases != expected_cases || (num_cases * 2U) != MAX_BOOT_COUNT) {
    printf("ERROR: Bus mode sanity check failed! SDVT_AHB=%0d, num_cases=%0d, "
           "expected_cases=%0d, MAX_BOOT_COUNT=%0d\n",
           (unsigned int)SDVT_AHB, (unsigned int)num_cases,
           (unsigned int)expected_cases, (unsigned int)MAX_BOOT_COUNT);
    return false;
  }

  uint32_t table_injectable_count = 0U;
  for (uint32_t i = 0U; i < num_cases; i++) {
    if (kDclsCaseTable[i].case_num != i ||
        kDclsCaseTable[i].signal_name == NULL) {
      printf("ERROR: Case table ordering mismatch at index %0d (case_num=%0d)!\n",
             (unsigned int)i, (unsigned int)kDclsCaseTable[i].case_num);
      return false;
    }
    if (kDclsCaseTable[i].veer_action == kDclsActionInject) {
      table_injectable_count++;
    }
    if (kDclsCaseTable[i].shadow_action == kDclsActionInject) {
      table_injectable_count++;
    }
  }

  if (table_injectable_count != EXPECTED_INJECTED_TRAPS) {
    printf("ERROR: Case table injectable count (%0d) != EXPECTED_INJECTED_TRAPS (%0d)!\n",
           (unsigned int)table_injectable_count,
           (unsigned int)EXPECTED_INJECTED_TRAPS);
    return false;
  }

  // Note: `testbench/asm/printf.c` (`whisperPuts`) automatically appends `'\n'`
  // after `%s`, so `%s` is placed at the end of format strings without `\n`.
  printf("DCLS Sanity Check Passed: cases=%0d (IDs 0..%0d), expected_traps=%0d, bus=%s",
         (unsigned int)num_cases, (unsigned int)(MAX_BOOT_COUNT - 1U),
         (unsigned int)EXPECTED_INJECTED_TRAPS,
         (SDVT_AHB == 0) ? "AXI4" : "AHB-Lite");
  return true;
}

/**
 * Trap handler located in ICCM (`.text.nmi`) so it never fetches from `.text`
 * (`0x80000000`) while an IFU/ICache fault or bus state divergence is active.
 * Snapshots the active signal ID, CSRs, and PIC `MEIP[2]` (`corruption_detected_o`
 * gateway latch) into persistent DCCM prior to `CMD_RST`.
 */
__attribute__((section(".text.nmi"), noinline))
void trap_handler(void) {
  last_trap_id = expected_trap_id;
  last_mstatus = (uint32_t)read_csr(mstatus);
  last_mcause  = (uint32_t)read_csr(mcause);
  last_mepc    = (uint32_t)read_csr(mepc);

  // Allow `DCLS_DELAY`, `tb_top` `extintsrc_req[2]` registration, and the
  // 2-stage PIC gateway synchronizer (`el2_configurable_gw`) to latch any DCLS
  // `corruption_detected_o` assertion into `MEIP[2]` when `VEER` entered
  // `_trap_handler` first via a synchronous exception, NMI, or timer/soft IRQ.
  for (uint32_t slp = 0; slp < 20U; slp++) {
    asm volatile("nop");
  }

  if (expected_trap_id == (28U * 2U)) {
    // `Case 28` (`ID 56`, `VEER.extintsrc_req`) directly forced `VEER`'s
    // internal `extintsrc_req` pins prior to `_trap_handler` issuing
    // `CMD_INJ_CLEAR`. Clear the pre-release gateway latch and wait for real
    // `corruption_detected_o` (from `VEER` vs. `LOCKSTEP_CORE` divergence) to
    // re-latch `MEIP[2]`.
    clr_gateway[2] = 0;
    asm volatile("fence");
    for (uint32_t slp = 0; slp < 20U; slp++) {
      asm volatile("nop");
    }
  }

  last_dcls_irq_pending = ((*meip >> 2) & 1U);
  last_trap_valid       = 1U;
  if (expected_trap_id < MAX_BOOT_COUNT && last_dcls_irq_pending != 0U) {
    injected_trap_count++;
  }

  tohost = CMD_INJ_CLEAR;
  asm volatile("fence");
  tohost = CLEAR_NMI_INT;
  asm volatile("fence");
  tohost = CMD_RST;

  while (true) {
    asm volatile("nop");
  }
}

/**
 * Dummy function in `.text` (`0x80000000`) to exercise the IFU external bus and
 * ICache when testing IFU/ICache input signals.
 */
__attribute__((noinline))
static void probe_ifu_text_fetch(void) {
  asm volatile(
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
  asm volatile(
      ".rept 16\n\t"
      "ret\n\t"
      ".endr\n\t"
  );
}

static void (*volatile probe_ifu_fn)(void)     = probe_ifu_text_fetch;
static void (*volatile probe_ifu_ret_fn)(void) = probe_ifu_ret_sled;

/**
 * Executes `Case 12` (`VEER.iccm_rd_data_ecc`, `ID 24`) from `.text`
 * (`0x80000000`) with `mtvec` pointing to `_text_trap_handler` in `.text`.
 * Performs a 32-bit LSU data load from ICCM (`0xee000000`) so `iccm_rd_data_ecc`
 * is sampled once via the LSU/DMA ICCM read path without trapping the IFU in a
 * continuous ICCM instruction-fetch single-bit ECC scrub loop.
 */
__attribute__((noinline))
static void inject_iccm_ecc_from_text(uint32_t old_boot_count) {
  write_csr(CSR_VEER_MRAC, 0x0UL);
  asm volatile("fence.i");
  fir_vector_table[2] = (uint32_t)(uintptr_t)_text_trap_handler;
  write_csr(CSR_VEER_MEIVT, (uintptr_t)fir_vector_table);
  write_csr(mtvec, (uintptr_t)_text_trap_handler);

  uint32_t cmd = ((old_boot_count >> 1) << 8) |
                 ((old_boot_count & 1U) ? CMD_INJ_LOCKSTEP : CMD_INJ_VEER);
  tohost = cmd;
  asm volatile("fence");
  for (uint32_t slp = 0; slp < 20; slp++) {
    asm volatile("nop");
  }

  // Read from `0xee000000` (word index 0, where the address mask is zero so
  // `iccm_rd_data_ecc = '1` decodes as a single-bit ECC error rather than an
  // NMI bus-error double-bit fault) using distinct base and destination
  // registers (`"=&r"`). This ensures any instruction refetch keeps a valid
  // base pointer, and `main()` restores the scrubbed ICCM word after reset.
  uint32_t val;
  uintptr_t iccm_base_addr = 0xee000000UL;
  asm volatile(
      "lw %0, 0(%1)\n\t"
      : "=&r"(val)
      : "r"(iccm_base_addr)
      : "memory"
  );
  dccm_probe[0] = val;

  for (uint32_t slp = 0; slp < 150; slp++) {
    asm volatile("nop");
  }

  tohost = CMD_INJ_CLEAR;
  asm volatile("fence");

  for (uint32_t slp = 0; slp < 150; slp++) {
    asm volatile("nop");
  }
}

/**
 * Executes the fault injection and observation window from ICCM (`.text.nmi`)
 * so that IFU output forces or DCCM read data forces do not break instruction
 * fetching or stack accesses prior to `_trap_handler`. `stim_raw` is passed in
 * a GPR from `main()` (`kDclsCaseTable[case_num].stim`) so no `.rodata` table
 * lookup occurs in DCCM while a fault is active.
 */
__attribute__((section(".text.nmi"), noinline, optimize("no-jump-tables")))
static void inject_and_wait(uint32_t old_boot_count, uint32_t stim_raw) {
  uint32_t case_num = old_boot_count >> 1;
  dcls_stim_t stim  = (dcls_stim_t)stim_raw;

  write_csr(CSR_VEER_MRAC, 0x0UL);
  asm volatile("fence.i");

  if (stim == kDclsStimIcacheFetch) {
    // `Case 13` (`ic_rd_data` on `VEER` and `LOCKSTEP_CORE`): Mark region
    // `0x80000000` cacheable in `mrac` (`0x7c0`, bit 16) and warm up the cache
    // line for `probe_ifu_text_fetch` before injecting the fault.
    write_csr(CSR_VEER_MRAC, 0x00010000UL);
    asm volatile("fence.i");
    probe_ifu_fn();
  }
#if (SDVT_AHB == 0)
  if (stim == kDclsStimAxiRvalidIccmRead) {
    // Prime `lmem` read data/ID registers (`s0_rdata`, `s0_rid = 0`) from
    // `0x80000000` before forcing `lsu_axi_rvalid = 1'b1`, then issue a
    // multi-cycle read from ICCM (`0xee000000`) via `axi_lsu_dma_bridge` during
    // the fault window so the forced core latches stale `0x80000000` data early
    // while the unforced core waits for `dma_axi_rvalid` (`0xee000000` data).
    (void)*(volatile const uint32_t *)0x80000000UL;
    asm volatile("fence");
  } else if (stim == kDclsStimIfuRvalidRetSled) {
    // Prime `lmem` IFU read data register (`ifu_axi_rdata`) with `ret` opcodes
    // before forcing `ifu_axi_rvalid = 1'b1`.
    probe_ifu_ret_fn();
    asm volatile("fence.i");
  } else if (stim == kDclsStimAxiCacheSideEffect) {
    // `Cases 108, 124` (`lsu_axi_awcache`, `lsu_axi_arcache` on `VEER` and
    // `LOCKSTEP_CORE`): In `el2_lsu_bus_buffer.sv`, both `lsu_axi_awcache` and
    // `lsu_axi_arcache` are driven by `obuf_sideeffect ? 4'b0 : 4'b1111`. Mark
    // region `0xd` (`tohost` at `0xd0580000`) as side-effect in `mrac` (`0x7c0`,
    // bit 27) so the unforced core drives `4'b0000` while the forced core
    // drives `4'b1111`.
    write_csr(CSR_VEER_MRAC, 0x08000000UL);
    asm volatile("fence");
  }
#endif

  uint32_t cmd = (case_num << 8) |
                 ((old_boot_count & 1U) ? CMD_INJ_LOCKSTEP : CMD_INJ_VEER);
  tohost = cmd;
  asm volatile("fence");
  for (uint32_t slp = 0; slp < 20; slp++) {
    asm volatile("nop");
  }

  if (stim == kDclsStimWarmReset) {
    // `ID 1` (`LOCKSTEP_CORE.rst_vec`): Trigger warm reset while forced so
    // Shadow Core boots at `0xfffffffe` and diverges on reboot.
    tohost = CMD_RST;
    while (true) {
      asm volatile("nop");
    }
  } else if (stim == kDclsStimNmiVec) {
    // `Case 2` (`nmi_vec`): Trigger NMI so Main Core & Shadow Core jump to
    // their respective `nmi_vec` addresses.
    tohost = SET_NMI_INT;
    asm volatile("fence");
  } else if (stim == kDclsStimCoreId) {
    // `Case 5` (`core_id`): Read `mhartid` and store to `dccm_probe[0]` so
    // the forced `core_id` propagates to DCCM write outputs.
    uint32_t hid = (uint32_t)read_csr(mhartid);
    dccm_probe[0] = hid;
  } else if (stim == kDclsStimDccmUnalignedLoad) {
    // `Cases 9, 10` (`dccm_rd_data_lo/hi`): Perform an unaligned 32-bit DCCM
    // load at offset +2 straddling `dccm_probe[0]` and `dccm_probe[1]`, and
    // store back to `dccm_probe[0]` to propagate the read corruption.
    uint32_t val;
    asm volatile(
        "lw %0, 2(%1)\n\t"
        "sw %0, 0(%1)\n\t"
        : "=&r"(val)
        : "r"(&dccm_probe[0])
        : "memory"
    );
  } else if (stim == kDclsStimIcacheFetch || stim == kDclsStimIfuTextFetch ||
             stim == kDclsStimIfuRvalidRetSled) {
    // Exercise `.text` (`0x80000000`) fetch via 32-bit indirect call so the
    // cores sample the forced ICache / IFU bus input signal.
    probe_ifu_fn();
#if (SDVT_AHB == 0)
  } else if (stim == kDclsStimAxiBvalidDoubleStore) {
    // `Case 50` (`lsu_axi_bvalid` on `VEER` and `LOCKSTEP_CORE`): Issue two
    // non-merged stores to the same unused ICCM scratch doubleword (`0xee003fc0`
    // via `axi_lsu_dma_bridge`) so early `RESP` retirement on the forced core
    // diverges on `bus_addr_match_pending`.
    *(volatile uint32_t *)0xee003fc0UL = 0x11111111U;
    asm volatile("fence");
    *(volatile uint32_t *)0xee003fc0UL = 0x22222222U;
    asm volatile("fence");
  } else if (stim == kDclsStimExtBusWrite) {
    // `Case 51` (`lsu_axi_bresp`) and `ID 105` (`LOCKSTEP_CORE.lsu_axi_bid`):
    // Issue a non-`tohost` external AXI write followed by `fence` so the write
    // response channel is sampled during the active fault window.
    *(volatile uint32_t *)0x80001000UL = 0xdeadbeefU;
    asm volatile("fence");
  } else if (stim == kDclsStimAxiRvalidIccmRead) {
    // `Case 54` (`lsu_axi_rvalid` on `VEER` and `LOCKSTEP_CORE`): Read from
    // ICCM (`0xee000000`) via `axi_lsu_dma_bridge` -> DMA slave so `s1_rvalid`
    // takes multiple cycles while `s0_rdata` holds the primed `0x80000000`
    // word, causing the forced core to complete early with stale data.
    uint32_t val = *(volatile const uint32_t *)0xee000000UL;
    dccm_probe[0] = val;
  } else if (stim == kDclsStimExtAxiRead) {
    // `Cases 55..57` (`lsu_axi_rid`, `lsu_axi_rdata`, `lsu_axi_rresp`):
    // Perform an external LSU AXI read from `0x80000008` and store to
    // `dccm_probe[0]`.
    uint32_t val = *(volatile const uint32_t *)0x80000008UL;
    dccm_probe[0] = val;
  } else if (stim == kDclsStimAxiCacheSideEffect) {
    // Issue a dummy write to `tohost` (`0xd0580000`, side-effect region `0xd`)
    // so `obuf_sideeffect` transitions to `1'b1` (`4'b0000`) on the unforced
    // core while the forced core drives `4'b1111`.
    tohost = cmd;
    asm volatile("fence");
#else
  } else if (stim == kDclsStimExtBusWrite) {
    // `Case 53` (`lsu_hresp`) and `Case 57` (`dma_hsel`): Issue a non-`tohost`
    // external AHB write so `lsu_hresp` and `m_ahb_htrans` (`s1_ahb_htrans`)
    // are active during the fault window.
    *(volatile uint32_t *)0x80001000UL = 0xdeadbeefU;
    asm volatile("fence");
  } else if (stim == kDclsStimExtAhbRead) {
    // `Case 51` (`lsu_hrdata`) and `ID 177` (`LOCKSTEP_CORE.lsu_hwrite`):
    // Perform an external LSU AHB read from `.text` (`0x80000000`) so both
    // cores sample `lsu_hrdata` and drive `lsu_hwrite = 1'b0`.
    uint32_t val = *(volatile const uint32_t *)0x80000000UL;
    dccm_probe[0] = val;
#endif
  }

  for (uint32_t slp = 0; slp < 150; slp++) {
    asm volatile("nop");
  }

  tohost = CMD_INJ_CLEAR;
  asm volatile("fence");

  for (uint32_t slp = 0; slp < 150; slp++) {
    asm volatile("nop");
  }
}

static void (*volatile inject_and_wait_fn)(uint32_t, uint32_t) = inject_and_wait;

int main(void) {
  // If the simulator ran with `--test-halt` (`tools/Makefile` default), initial
  // boot exercised `mpc_debug_halt_req`, latching `dbg_detected = MuBiTrue` in
  // `el2_veer_lockstep` until `rst_l` asserts. Issue one clean warm reset
  // (`CMD_RST`) before starting the sweep so DCLS detection is active from ID 0.
  if (initial_reset_done == 0U) {
    write_csr(CSR_VEER_MRAC, 0x08010000UL);
    initial_reset_done = 1U;
    tohost = CMD_RST;
    while (true) {
      asm volatile("nop");
    }
  }

  uint32_t old_boot_count = boot_count;

  if (old_boot_count < MAX_BOOT_COUNT) {
    asm volatile(
        "li t0, 0x888\n\t"
        "csrc mie, t0\n\t"
        ::: "t0"
    );

    *threshold     = 1;
    gateway[2]     = (1U << 1) | 0U;
    clr_gateway[2] = 0;
    priority[2]    = 7;
    enable[2]      = 1;

    asm volatile(
        "li t0, 0x888\n\t"
        "csrs mie, t0\n\t"
        "li t0, 0x8\n\t"
        "csrs mstatus, t0\n\t"
        ::: "t0"
    );

    // Allow any pending post-reset DCLS interrupt (such as `ID 1`,
    // `LOCKSTEP_CORE.rst_vec`) to fire `_trap_handler` before checking
    // `last_trap_valid`.
    if (expected_trap_id == 1U && last_trap_valid == 0U) {
      for (uint32_t slp = 0; slp < 500U; slp++) {
        asm volatile("nop");
      }
    }
  }

  // Enable ICache for `.text` (`0x80000000`, bit 16) and side-effect ordering
  // for `tohost` (`0xd0580000`, bit 27) during `main()` / `printf()`
  // housekeeping so all 390 iterations complete well within `MAX_CYCLES`
  // without write-buffer coalescing on `tohost`. `inject_and_wait()` resets
  // `mrac` (`0x7c0`) and invalidates ICache via `fence.i` prior to injection.
  write_csr(CSR_VEER_MRAC, 0x08010000UL);

  if (expected_trap_id != 0xFFFFFFFFU) {
    if (last_trap_valid == 0U || last_trap_id != expected_trap_id ||
        last_dcls_irq_pending == 0U) {
      printf("ERROR: Expected DCLS trap for signal ID %0d (case %0d) failed across reset! "
             "(last_trap_valid=%0d, dcls_irq_pending=%0d, last_trap_id=%0d, "
             "mstatus=0x%08X, mcause=0x%08X, mepc=0x%08X)\n",
             (unsigned int)expected_trap_id, (unsigned int)(expected_trap_id >> 1),
             (unsigned int)last_trap_valid, (unsigned int)last_dcls_irq_pending,
             (unsigned int)last_trap_id, (unsigned int)last_mstatus,
             (unsigned int)last_mcause, (unsigned int)last_mepc);
      return 1;
    }
    last_trap_valid       = 0U;
    last_dcls_irq_pending = 0U;
    expected_trap_id      = 0xFFFFFFFFU;
    printf("trap #%0d (ID %0d)! mcause=0x%08X, mepc=0x%08X\n",
           (unsigned int)injected_trap_count, (unsigned int)last_trap_id,
           (unsigned int)last_mcause, (unsigned int)last_mepc);
  }

  if (old_boot_count == 0U) {
    if (!verify_case_table_sanity()) {
      return 1;
    }
    volatile uint32_t *const iccm_base = (volatile uint32_t *)0xee000000UL;
    saved_iccm_head[0] = iccm_base[0];
    saved_iccm_head[1] = iccm_base[1];
    printf("Starting DCLS I/O Sweep Test\n");
  } else if (old_boot_count == 25U) {
    // Restore `_nmi` words at `0xee000000` in ICCM after `ID 24` ECC scrub.
    volatile uint32_t *const iccm_base = (volatile uint32_t *)0xee000000UL;
    iccm_base[0] = saved_iccm_head[0];
    iccm_base[1] = saved_iccm_head[1];
    asm volatile("fence.i");
  }

  while (boot_count < MAX_BOOT_COUNT) {
    old_boot_count = boot_count;
    boot_count++;

    const uint32_t case_num = old_boot_count >> 1;
    const bool is_shadow    = (old_boot_count & 1U) != 0U;
    const dcls_case_desc_t *const desc = &kDclsCaseTable[case_num];
    const dcls_action_t action =
        (dcls_action_t)(is_shadow ? desc->shadow_action : desc->veer_action);

    if (action != kDclsActionInject) {
      printf("Skipping ID %0d (case %0d): %s",
             (unsigned int)old_boot_count, (unsigned int)case_num,
             desc->signal_name);
      continue;
    }

    dccm_probe[0] = 0x12345678U;
    dccm_probe[1] = 0x9abcdef0U;

    printf("Injecting ID %0d (case %0d): %s",
           (unsigned int)old_boot_count, (unsigned int)case_num,
           desc->signal_name);
    expected_trap_id = old_boot_count;
    if (desc->stim == kDclsStimIccmEcc && !is_shadow) {
      inject_iccm_ecc_from_text(old_boot_count);
    } else {
      inject_and_wait_fn(old_boot_count, (uint32_t)desc->stim);
    }

    // Every injected signal MUST trigger `_trap_handler` -> `CMD_RST` inside
    // `inject_and_wait_fn`. Reaching this line means no trap was taken.
    printf("ERROR: Signal did not trigger a trap for ID %0d (case %0d): %s",
           (unsigned int)old_boot_count, (unsigned int)case_num,
           desc->signal_name);
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
    asm volatile("nop");
  }
  return 0;
}
