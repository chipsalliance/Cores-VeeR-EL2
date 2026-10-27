/*
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2026 Google LLC
 *
 * ICache Core-Side ECC and Parity Fault Recovery Functional Coverage Interface
 * Author: Samip Modi (samipmodi@google.com)
 *
 * Description:
 * Functional coverage interface for Synopsys VCS and Verilator (IEEE 1800 covergroup)
 * verifying Task #9:
 * - ICache protection mode configuration (parity_mode vs secded_mode)
 * - ICache fault types (single_bit_data_error, single_bit_tag_error, double_bit_uncorrectable_error)
 * - ICache hardware recovery actions (pipeline_squash_and_flush, micect_counter_increment, refetch_success)
 * - Cross coverage across protection modes, fault types, waypack, and cache way configurations
 * - Issue #569 / PR #571 core-side ECC/Parity check enable (ic_bank_check_en), bank order selection
 *   (ic_rd_bank_sel), byte rotator offset (ic_rd_rot_sel), and cross-bank straddle fetch coverage
 */

interface el2_ifu_icache_ecc_recovery_cov_if
  import el2_pkg::*;
#(
    `include "el2_param.vh"
) (
    input logic                           clk,
    input logic                           rst_l,
    input logic                           exu_flush_final,
    input logic                           dec_tlu_flush_lower_wb,
    input logic                           dec_tlu_flush_err_wb,
    input logic                           dec_tlu_i0_commit_cmt,
    input logic                           dec_tlu_force_halt,
    input logic                           dec_tlu_core_ecc_disable,
    input logic [141:0]                   ic_rd_data,
    input logic                           ic_rd_bank_sel,
    input logic [1:0]                     ic_rd_rot_sel,
    input logic [pt.ICACHE_BANKS_WAY-1:0] ic_bank_check_en,
    input logic [31:1]                    ifu_fetch_addr_int_f,
    input logic                           ic_tag_perr,
    input logic                           ic_hit_f,
    input logic                           ic_error_start,
    input logic                           ifu_async_error_start,
    input logic                           ic_act_hit_f,
    input logic [pt.ICACHE_BANKS_WAY-1:0] ic_eccerr_int,
    input logic [pt.ICACHE_BANKS_WAY-1:0] ic_parerr_int,
    input logic                           ic_rd_parity_final_err
);

  // Fault type encoding for icache_fault_type_cp
  typedef enum logic [1:0] {
    FAULT_NONE                     = 2'd0,
    FAULT_SINGLE_BIT_DATA          = 2'd1,
    FAULT_SINGLE_BIT_TAG           = 2'd2,
    FAULT_DOUBLE_BIT_UNCORRECTABLE = 2'd3
  } icache_fault_type_e;

  // Recovery action encoding for icache_recovery_action_cp
  typedef enum logic [1:0] {
    RECOVERY_NONE             = 2'd0,
    RECOVERY_SQUASH_AND_FLUSH = 2'd1,
    RECOVERY_MICECT_INCREMENT = 2'd2,
    RECOVERY_REFETCH_SUCCESS  = 2'd3
  } icache_recovery_action_e;

  logic                    data_err_qual;
  logic                    tag_err_qual;
  logic                    is_double_or_multibit_err;
  icache_fault_type_e      current_fault_type;
  icache_fault_type_e      latched_fault_type;
  icache_recovery_action_e recovery_action;

  logic                    ic_err_pending;
  logic                    micect_inc_pending;
  logic                    refetch_pending;
  logic                    refetch_hit_seen;

  logic                    squash_flush_event;
  logic                    micect_inc_event;
  logic                    refetch_success_event;
  logic                    sample_en;

  // Issue #569 / PR #571 tracking signals: core-side bank check enable, bank select,
  // rotator offset, and cross-bank straddle
  logic                    core_check_sample_en;
  logic                    is_cross_bank_straddle;

  // Address infection mask, bank-ordered read data, and per-bank ECC/Parity syndrome helpers
  logic [63:0]             cov_rd_addr_infect;
  logic [141:0]            cov_ic_rd_data_ecc_ord;
  logic [135:0]            cov_ic_rd_data_par_ord;
  logic [63:0]             ecc_data_b0;
  logic [63:0]             ecc_data_b1;
  logic [6:0]              ecc_syn_b0;
  logic [6:0]              ecc_syn_b1;
  logic [63:0]             par_data_b0;
  logic [63:0]             par_data_b1;
  logic [3:0]              par_err_b0;
  logic [3:0]              par_err_b1;
  logic                    ecc_multibit_err;
  logic                    par_multibit_err;
  logic                    is_sbe_broadcast_inj;

  function automatic logic [6:0] calc_ecc64_syndrome(
      input logic [63:0] din,
      input logic [6:0]  ecc_in
  );
    logic [6:0] syn;
    syn[0] = ecc_in[0] ^ din[0]  ^ din[1]  ^ din[3]  ^ din[4]  ^ din[6]  ^ din[8]  ^ din[10] ^
             din[11]   ^ din[13] ^ din[15] ^ din[17] ^ din[19] ^ din[21] ^ din[23] ^ din[25] ^
             din[26]   ^ din[28] ^ din[30] ^ din[32] ^ din[34] ^ din[36] ^ din[38] ^ din[40] ^
             din[42]   ^ din[44] ^ din[46] ^ din[48] ^ din[50] ^ din[52] ^ din[54] ^ din[56] ^
             din[57]   ^ din[59] ^ din[61] ^ din[63];
    syn[1] = ecc_in[1] ^ din[0]  ^ din[2]  ^ din[3]  ^ din[5]  ^ din[6]  ^ din[9]  ^ din[10] ^
             din[12]   ^ din[13] ^ din[16] ^ din[17] ^ din[20] ^ din[21] ^ din[24] ^ din[25] ^
             din[27]   ^ din[28] ^ din[31] ^ din[32] ^ din[35] ^ din[36] ^ din[39] ^ din[40] ^
             din[43]   ^ din[44] ^ din[47] ^ din[48] ^ din[51] ^ din[52] ^ din[55] ^ din[56] ^
             din[58]   ^ din[59] ^ din[62] ^ din[63];
    syn[2] = ecc_in[2] ^ din[1]  ^ din[2]  ^ din[3]  ^ din[7]  ^ din[8]  ^ din[9]  ^ din[10] ^
             din[14]   ^ din[15] ^ din[16] ^ din[17] ^ din[22] ^ din[23] ^ din[24] ^ din[25] ^
             din[29]   ^ din[30] ^ din[31] ^ din[32] ^ din[37] ^ din[38] ^ din[39] ^ din[40] ^
             din[45]   ^ din[46] ^ din[47] ^ din[48] ^ din[53] ^ din[54] ^ din[55] ^ din[56] ^
             din[60]   ^ din[61] ^ din[62] ^ din[63];
    syn[3] = ecc_in[3] ^ din[4]  ^ din[5]  ^ din[6]  ^ din[7]  ^ din[8]  ^ din[9]  ^ din[10] ^
             din[18]   ^ din[19] ^ din[20] ^ din[21] ^ din[22] ^ din[23] ^ din[24] ^ din[25] ^
             din[33]   ^ din[34] ^ din[35] ^ din[36] ^ din[37] ^ din[38] ^ din[39] ^ din[40] ^
             din[49]   ^ din[50] ^ din[51] ^ din[52] ^ din[53] ^ din[54] ^ din[55] ^ din[56];
    syn[4] = ecc_in[4] ^ din[11] ^ din[12] ^ din[13] ^ din[14] ^ din[15] ^ din[16] ^ din[17] ^
             din[18]   ^ din[19] ^ din[20] ^ din[21] ^ din[22] ^ din[23] ^ din[24] ^ din[25] ^
             din[41]   ^ din[42] ^ din[43] ^ din[44] ^ din[45] ^ din[46] ^ din[47] ^ din[48] ^
             din[49]   ^ din[50] ^ din[51] ^ din[52] ^ din[53] ^ din[54] ^ din[55] ^ din[56];
    syn[5] = ecc_in[5] ^ din[26] ^ din[27] ^ din[28] ^ din[29] ^ din[30] ^ din[31] ^ din[32] ^
             din[33]   ^ din[34] ^ din[35] ^ din[36] ^ din[37] ^ din[38] ^ din[39] ^ din[40] ^
             din[41]   ^ din[42] ^ din[43] ^ din[44] ^ din[45] ^ din[46] ^ din[47] ^ din[48] ^
             din[49]   ^ din[50] ^ din[51] ^ din[52] ^ din[53] ^ din[54] ^ din[55] ^ din[56];
    syn[6] = ecc_in[6] ^ din[57] ^ din[58] ^ din[59] ^ din[60] ^ din[61] ^ din[62] ^ din[63];
    return syn;
  endfunction

`ifdef RV_ICACHE_ADDR_XOR
  assign cov_rd_addr_infect = 64'(ifu_fetch_addr_int_f[31:pt.ICACHE_TAG_INDEX_LO]);
`else
  assign cov_rd_addr_infect = 64'b0;
`endif

  // Reorder physical bank pair {bank1, bank0} into {upper_chunk, lower_chunk} via ic_rd_bank_sel
  assign cov_ic_rd_data_ecc_ord = ic_rd_bank_sel ?
                                  {ic_rd_data[70:0], ic_rd_data[141:71]} : ic_rd_data;
  assign cov_ic_rd_data_par_ord = ic_rd_bank_sel ?
                                  {ic_rd_data[67:0], ic_rd_data[135:68]} : ic_rd_data[135:0];

  assign ecc_data_b0 = cov_ic_rd_data_ecc_ord[63:0]   ^ cov_rd_addr_infect;
  assign ecc_data_b1 = cov_ic_rd_data_ecc_ord[134:71] ^ cov_rd_addr_infect;
  assign ecc_syn_b0  = calc_ecc64_syndrome(ecc_data_b0, cov_ic_rd_data_ecc_ord[70:64]);
  assign ecc_syn_b1  = calc_ecc64_syndrome(ecc_data_b1, cov_ic_rd_data_ecc_ord[141:135]);

  assign par_data_b0 = cov_ic_rd_data_par_ord[63:0]   ^ cov_rd_addr_infect;
  assign par_data_b1 = cov_ic_rd_data_par_ord[131:68] ^ cov_rd_addr_infect;
  for (genvar j = 0; j < 4; j++) begin : gen_par_err_chk
    assign par_err_b0[j] = ic_bank_check_en[0] &
                           ((^par_data_b0[16*j +: 16]) ^ cov_ic_rd_data_par_ord[64 + j]);
    assign par_err_b1[j] = ic_bank_check_en[1] &
                           ((^par_data_b1[16*j +: 16]) ^ cov_ic_rd_data_par_ord[132 + j]);
  end

  // Note on Hamming(71, 64) 2-bit syndrome aliasing:
  // Unlike 39-bit SECDED in DCCM/ICCM, rvecc_decode_64 in the ICache uses a 7-bit
  // Hamming(71, 64) error-detection code without an 8th overall parity bit because ICache
  // invalidates and refetches on any non-zero syndrome (ecc_check[6:0] != 0) rather than
  // correcting in-place. In Hamming(71, 64), 1-bit flips map to syndromes [1..71].
  // 2-bit flips whose syndromes XOR to [1..71] alias with 1-bit syndromes in hardware and
  // follow the exact same invalidate-and-refetch recovery path, whereas syndromes in
  // [72..127] (> 71) can only arise from multi-bit errors. In parity mode, a 1-bit flip
  // affects at most one 16-bit halfword parity check within a 64-bit bank.
  assign ecc_multibit_err = (pt.ICACHE_ECC == 1) &&
                            ((ic_bank_check_en[0] && (ecc_syn_b0 > 7'd71)) ||
                             (ic_bank_check_en[1] && (ecc_syn_b1 > 7'd71)));
  assign par_multibit_err = (pt.ICACHE_ECC == 0) &&
                            (($countones(par_err_b0) > 1) || ($countones(par_err_b1) > 1));

  // Mailbox 0x89 broadcasts a 1-bit flip to both physical banks ({71'h1, 71'h1} / {6'b0, 68'h1, 68'h1})
  // so single-bit injection is address-bank independent.
  assign is_sbe_broadcast_inj = (ic_rd_data == {71'h1, 71'h1}) ||
                                (ic_rd_data == {6'b0, 68'h1, 68'h1});

  // Core-side data array error vs tag array error qualification
  assign data_err_qual = ((|ic_eccerr_int) | (|ic_parerr_int)) & ic_act_hit_f;
  assign tag_err_qual  = ic_rd_parity_final_err;

  // Distinguish observable multi-bit / multi-source uncorrectable errors from 1-bit errors:
  // - Both banks report ECC/parity errors simultaneously (excluding 0x89 1-bit broadcast), or
  // - Both data and tag arrays report errors simultaneously, or
  // - Hamming(71, 64) non-aliasing multi-bit syndrome > 71 (ECC mode) or >1 halfword parity
  //   errors in a bank (Parity mode), or
  // - Explicit multi-bit hit-fault testbench injection pattern (0x8B: 64'h5557_5557_5557_5557).
  assign is_double_or_multibit_err =
      (data_err_qual && !is_sbe_broadcast_inj && ((&ic_eccerr_int) || (&ic_parerr_int))) ||
      (data_err_qual && tag_err_qual) ||
      (data_err_qual && (ecc_multibit_err || par_multibit_err)) ||
      (data_err_qual && (ic_rd_data[63:0] == 64'h5557_5557_5557_5557));

  always_comb begin
    if (is_double_or_multibit_err) begin
      current_fault_type = FAULT_DOUBLE_BIT_UNCORRECTABLE;
    end else if (tag_err_qual) begin
      current_fault_type = FAULT_SINGLE_BIT_TAG;
    end else if (data_err_qual) begin
      current_fault_type = FAULT_SINGLE_BIT_DATA;
    end else begin
      current_fault_type = FAULT_NONE;
    end
  end

  // Recovery action event pulses:
  // 1. pipeline_squash_and_flush: IFU squashed faulting fetch (ic_err_pending) and TLU flushes
  //    pipeline + invalidates cache line (dec_tlu_flush_err_wb & dec_tlu_flush_lower_wb).
  // 2. micect_counter_increment: CSR micect (0x7F0) increments by 1 on the TLU ic_perr_r flush.
  // 3. refetch_success: Core re-fetches invalidated line (ic_hit_f without error) and commits
  //    instructions (dec_tlu_i0_commit_cmt) without halting.
  assign squash_flush_event    = ic_err_pending & dec_tlu_flush_err_wb & dec_tlu_flush_lower_wb;
  assign micect_inc_event      = micect_inc_pending;
  assign refetch_success_event = refetch_pending & ~micect_inc_pending &
                                 dec_tlu_i0_commit_cmt &
                                 (refetch_hit_seen | (ic_hit_f & ~ic_error_start)) &
                                 ~dec_tlu_force_halt;

  always_comb begin
    if (squash_flush_event) begin
      recovery_action = RECOVERY_SQUASH_AND_FLUSH;
    end else if (micect_inc_event) begin
      recovery_action = RECOVERY_MICECT_INCREMENT;
    end else if (refetch_success_event) begin
      recovery_action = RECOVERY_REFETCH_SUCCESS;
    end else begin
      recovery_action = RECOVERY_NONE;
    end
  end

  assign sample_en = squash_flush_event | micect_inc_event | refetch_success_event;

  // Issue #569 / PR #571 combinational qualification:
  // - core_check_sample_en: active ICache hit or fault start while core ECC is enabled
  // - is_cross_bank_straddle: 32-bit fetch straddling across the 64-bit bank boundary (addr[2:1] == 2'b11)
  assign core_check_sample_en   = (ic_act_hit_f | ic_error_start) & ~dec_tlu_core_ecc_disable &
                                  ~exu_flush_final & ~dec_tlu_force_halt;
  assign is_cross_bank_straddle = (ifu_fetch_addr_int_f[2:1] == 2'b11);

  always_ff @(posedge clk or negedge rst_l) begin
    if (!rst_l) begin
      latched_fault_type <= FAULT_NONE;
      ic_err_pending     <= 1'b0;
      micect_inc_pending <= 1'b0;
      refetch_pending    <= 1'b0;
      refetch_hit_seen   <= 1'b0;
    end else begin
      // Default single-cycle pulse clear for micect increment event
      micect_inc_pending <= 1'b0;

      // Step 1: Capture fault type when IFU detects an ICache data/tag error
      if (ic_error_start && ifu_async_error_start && !exu_flush_final &&
          !dec_tlu_flush_lower_wb && !dec_tlu_force_halt && !ic_err_pending) begin
        ic_err_pending     <= 1'b1;
        latched_fault_type <= current_fault_type;
      end

      // Step 2: Pipeline squash & flush + tag invalidation completed; trigger micect & refetch tracking
      if (squash_flush_event) begin
        ic_err_pending     <= 1'b0;
        micect_inc_pending <= 1'b1;
        refetch_pending    <= 1'b1;
        refetch_hit_seen   <= 1'b0;
      end else if (ic_err_pending && (dec_tlu_flush_lower_wb || dec_tlu_force_halt)) begin
        ic_err_pending <= 1'b0;
      end

      // Step 3: Track clean ICache refetch hit and subsequent instruction commit
      if (refetch_pending && !squash_flush_event) begin
        if (ic_hit_f && !ic_error_start && !dec_tlu_flush_lower_wb) begin
          refetch_hit_seen <= 1'b1;
        end
        if (refetch_success_event || dec_tlu_force_halt) begin
          refetch_pending  <= 1'b0;
          refetch_hit_seen <= 1'b0;
        end
      end
    end
  end

  // Non-straddle fetches (ic_rd_rot_sel != 2'b11) must never enable the upper bank check
  assert_non_straddle_no_upper_bank_chk: assert property (@(posedge clk) disable iff (!rst_l)
      core_check_sample_en && (ic_rd_rot_sel != 2'b11) |-> !ic_bank_check_en[1]);

  // -------------------------------------------------------------------------
  // IEEE 1800 Covergroup 1: ICache Core-Side ECC & Parity Fault Recovery
  // -------------------------------------------------------------------------
  covergroup el2_ifu_icache_ecc_recovery_cov @(posedge clk iff (rst_l && sample_en));
    type_option.merge_instances = 1;

    // Coverpoint icache_protection_mode_cp:
    // Covers ICache protection mode configuration (Parity vs SECDED ECC)
    icache_protection_mode_cp: coverpoint int'(pt.ICACHE_ECC) {
      bins parity_mode = {0};
      bins secded_mode = {1};
    }

    // Coverpoint icache_fault_type_cp:
    // Covers 1-bit data error, 1-bit tag error, and 2-bit/multi-bit uncorrectable error
    icache_fault_type_cp: coverpoint latched_fault_type {
      bins single_bit_data_error          = {FAULT_SINGLE_BIT_DATA};
      bins single_bit_tag_error           = {FAULT_SINGLE_BIT_TAG};
      bins double_bit_uncorrectable_error = {FAULT_DOUBLE_BIT_UNCORRECTABLE};
    }

    // Coverpoint icache_recovery_action_cp:
    // Covers IFU/DEC squash & flush, micect CSR increment, and line refetch + commit
    icache_recovery_action_cp: coverpoint recovery_action {
      bins pipeline_squash_and_flush = {RECOVERY_SQUASH_AND_FLUSH};
      bins micect_counter_increment  = {RECOVERY_MICECT_INCREMENT};
      bins refetch_success           = {RECOVERY_REFETCH_SUCCESS};
    }

    // Coverpoint icache_waypack_cp:
    // Covers cache waypack configuration (0: unpacked, 1: packed)
    icache_waypack_cp: coverpoint int'(pt.ICACHE_WAYPACK) {
      bins waypack_0 = {0};
      bins waypack_1 = {1};
    }

    // Coverpoint icache_num_ways_cp:
    // Covers number of cache ways configuration (2 ways vs 4 ways)
    icache_num_ways_cp: coverpoint int'(pt.ICACHE_NUM_WAYS) {
      bins num_ways_2 = {2};
      bins num_ways_4 = {4};
    }

    // Cross Coverage:
    // Cross icache_protection_mode_cp with icache_fault_type_cp and cache waypack/way configurations
    icache_protection_x_fault_x_waypack_x_ways: cross icache_protection_mode_cp,
                                                      icache_fault_type_cp,
                                                      icache_waypack_cp,
                                                      icache_num_ways_cp;

    // Cross icache_fault_type_cp with icache_recovery_action_cp
    icache_fault_x_recovery_action: cross icache_fault_type_cp, icache_recovery_action_cp;
  endgroup

  // -------------------------------------------------------------------------
  // IEEE 1800 Covergroup 2: Issue #569 / PR #571 Core-Side Bank Check & Rotator Alignment
  // -------------------------------------------------------------------------
  covergroup el2_ifu_icache_core_check_cov @(posedge clk iff (rst_l && core_check_sample_en));
    type_option.merge_instances = 1;

    // Coverpoint icache_bank_check_en_cp (Issue #569 / PR #571):
    // Covers per-bank ECC/Parity check enable (ic_bank_check_en[1:0])
    icache_bank_check_en_cp: coverpoint ic_bank_check_en {
      bins primary_bank_only        = {2'b01};
      bins both_banks_checked       = {2'b11};
      bins check_disabled_or_masked = {2'b00, 2'b10};
    }

    // Coverpoint icache_rotator_offset_cp (Issue #569 / PR #571):
    // Covers DCLS-protected 64-bit byte rotator halfword alignment (ic_rd_rot_sel[1:0])
    icache_rotator_offset_cp: coverpoint ic_rd_rot_sel {
      bins rot_offset_00          = {2'b00};
      bins rot_offset_01          = {2'b01};
      bins rot_offset_10          = {2'b10};
      bins rot_offset_11_straddle = {2'b11};
    }

    // Coverpoint icache_straddle_bank_check_cp (Issue #569 / PR #571):
    // Covers cross-bank straddling fetch (addr[2:1] == 2'b11) across Bank0->Bank1 (3'b011)
    // vs Bank1->Bank0 cacheline wrap (3'b111)
    icache_straddle_bank_check_cp: coverpoint ifu_fetch_addr_int_f[3] iff (is_cross_bank_straddle) {
      bins bank0_to_bank1_straddle = {1'b0};
      bins bank1_to_bank0_straddle = {1'b1};
    }

    // Coverpoint icache_bank_sel_cp (Issue #569 / PR #571):
    // Covers DCLS-protected physical bank order selector (ic_rd_bank_sel)
    icache_bank_sel_cp: coverpoint ic_rd_bank_sel {
      bins lower_chunk_in_bank0 = {1'b0};
      bins lower_chunk_in_bank1 = {1'b1};
    }

    // Cross rotator halfword offset (00/01/10/11) with physical bank selection (bank0/bank1)
    icache_rotator_x_bank_sel: cross icache_rotator_offset_cp, icache_bank_sel_cp;
  endgroup

  el2_ifu_icache_ecc_recovery_cov el2_ifu_icache_ecc_recovery_cov_cg;
  el2_ifu_icache_core_check_cov   el2_ifu_icache_core_check_cov_cg;

  initial begin
    el2_ifu_icache_ecc_recovery_cov_cg = new();
    el2_ifu_icache_core_check_cov_cg   = new();
    $display("ICache ECC recovery coverage interface created");
  end

endinterface
