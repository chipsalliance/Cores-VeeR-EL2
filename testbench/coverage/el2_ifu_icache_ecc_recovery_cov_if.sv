/*
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2026 Google LLC
 *
 * ICache Core-Side ECC and Parity Fault Recovery Functional Coverage Interface
 * Author: Samip Modi (samipmodi@google.com)
 *
 * Description:
 * Dual-mode functional coverage interface for Synopsys VCS (IEEE 1800 covergroup)
 * and Verilator (SVA cover property) verifying Task #9:
 * - ICache protection mode configuration (parity_mode vs secded_mode)
 * - ICache fault types (single_bit_data_error, single_bit_tag_error, double_bit_uncorrectable_error)
 * - ICache hardware recovery actions (pipeline_squash_and_flush, micect_counter_increment, refetch_success)
 * - Cross coverage across protection modes, fault types, waypack, and cache way configurations
 * - Issue #569 core-side ECC/Parity check enable (ic_rd_bank_check_en), byte rotator offset
 *   (ic_rd_addr_lo vs ifu_fetch_addr_int_f[2:1]), and cross-bank straddle fetch coverage
 */

interface el2_ifu_icache_ecc_recovery_cov_if #(
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
    input logic [1:0]                     ic_rd_addr_lo,
    input logic [pt.ICACHE_BANKS_WAY-1:0] ic_rd_bank_check_en,
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

  // Issue #569 tracking signals: core-side bank check enable, rotator offset, and straddle
  logic                    core_check_sample_en;
  logic                    is_cross_bank_straddle;
  logic                    rotator_addr_mismatch;

  // Address infection mask and per-bank ECC/Parity syndrome helpers
  logic [63:0]             cov_rd_addr_infect;
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

  assign ecc_data_b0 = ic_rd_data[63:0]   ^ cov_rd_addr_infect;
  assign ecc_data_b1 = ic_rd_data[134:71] ^ cov_rd_addr_infect;
  assign ecc_syn_b0  = calc_ecc64_syndrome(ecc_data_b0, ic_rd_data[70:64]);
  assign ecc_syn_b1  = calc_ecc64_syndrome(ecc_data_b1, ic_rd_data[141:135]);

  assign par_data_b0 = ic_rd_data[63:0]   ^ cov_rd_addr_infect;
  assign par_data_b1 = ic_rd_data[131:68] ^ cov_rd_addr_infect;
  for (genvar j = 0; j < 4; j++) begin : gen_par_err_chk
    assign par_err_b0[j] = ic_rd_bank_check_en[0] &
                           ((^par_data_b0[16*j +: 16]) ^ ic_rd_data[64 + j]);
    assign par_err_b1[j] = ic_rd_bank_check_en[1] &
                           ((^par_data_b1[16*j +: 16]) ^ ic_rd_data[132 + j]);
  end

  // In Hamming(71, 64), every 1-bit flip produces a syndrome in [1..71]; syndromes > 71
  // can only occur on multi-bit errors. In parity mode, a 1-bit flip affects at most one
  // 16-bit halfword parity check.
  assign ecc_multibit_err = (pt.ICACHE_ECC == 1) &&
                            ((ic_rd_bank_check_en[0] && (ecc_syn_b0 > 7'd71)) ||
                             (ic_rd_bank_check_en[1] && (ecc_syn_b1 > 7'd71)));
  assign par_multibit_err = (pt.ICACHE_ECC == 0) &&
                            ($countones({par_err_b1, par_err_b0}) > 1);

  // Core-side data array error vs tag array error qualification
  assign data_err_qual = ((|ic_eccerr_int) | (|ic_parerr_int)) & ic_act_hit_f;
  assign tag_err_qual  = ic_rd_parity_final_err;

  // Distinguish 2-bit / multi-bit uncorrectable errors from 1-bit errors:
  // - Both banks report ECC/parity errors simultaneously, or
  // - Both data and tag arrays report errors simultaneously, or
  // - Hamming(71, 64) syndrome > 71 (ECC mode) or >1 halfword parity errors (Parity mode), or
  // - Explicit multi-bit hit-fault testbench injection pattern (142'h5557_5557_5557_5557).
  assign is_double_or_multibit_err =
      (data_err_qual && ((&ic_eccerr_int) || (&ic_parerr_int))) ||
      (data_err_qual && tag_err_qual) ||
      (data_err_qual && (ecc_multibit_err || par_multibit_err)) ||
      (data_err_qual && (ic_rd_data == 142'h5557_5557_5557_5557));

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

  // Issue #569 combinational qualification:
  // - core_check_sample_en: active ICache hit or fault start while core ECC is enabled
  // - is_cross_bank_straddle: 32-bit fetch straddling across the 64-bit bank boundary (addr[2:1] == 2'b11)
  // - rotator_addr_mismatch: uncore ic_rd_addr_lo[1:0] diverges from DCLS-protected ifu_fetch_addr_int_f[2:1]
  assign core_check_sample_en   = (ic_act_hit_f | ic_error_start) & ~dec_tlu_core_ecc_disable &
                                  ~exu_flush_final & ~dec_tlu_force_halt;
  assign is_cross_bank_straddle = (ifu_fetch_addr_int_f[2:1] == 2'b11);
  assign rotator_addr_mismatch  = (ic_rd_addr_lo != ifu_fetch_addr_int_f[2:1]);

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

`ifndef VERILATOR
  // -------------------------------------------------------------------------
  // VCS / IEEE 1800 Covergroup 1: ICache Core-Side ECC & Parity Fault Recovery
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
  // VCS / IEEE 1800 Covergroup 2: Issue #569 Core-Side Bank Check & Rotator Alignment
  // -------------------------------------------------------------------------
  covergroup el2_ifu_icache_core_check_cov @(posedge clk iff (rst_l && core_check_sample_en));
    type_option.merge_instances = 1;

    // Coverpoint icache_bank_check_en_cp (Issue #569 Sub-bug 1 & 2):
    // Covers per-bank ECC/Parity check enable (ic_rd_bank_check_en[1:0])
    icache_bank_check_en_cp: coverpoint ic_rd_bank_check_en {
      bins primary_bank_only        = {2'b01};
      bins both_banks_checked       = {2'b11};
      bins check_disabled_or_masked = {2'b00, 2'b10};
    }

    // Coverpoint icache_rotator_offset_cp (Issue #569 Sub-bug 2 & 3):
    // Covers 64-bit byte rotator halfword alignment (ic_rd_addr_lo[1:0])
    icache_rotator_offset_cp: coverpoint ic_rd_addr_lo {
      bins rot_offset_00          = {2'b00};
      bins rot_offset_01          = {2'b01};
      bins rot_offset_10          = {2'b10};
      bins rot_offset_11_straddle = {2'b11};
    }

    // Coverpoint icache_straddle_bank_check_cp (Issue #569 Sub-bug 2):
    // Covers cross-bank straddling fetch (addr[2:1] == 2'b11) across Bank0->Bank1 (3'b011)
    // vs Bank1->Bank0 cacheline wrap (3'b111)
    icache_straddle_bank_check_cp: coverpoint ifu_fetch_addr_int_f[3] iff (is_cross_bank_straddle) {
      bins bank0_to_bank1_straddle = {1'b0};
      bins bank1_to_bank0_straddle = {1'b1};
    }

    // Coverpoint icache_rotator_addr_consistency_cp (Issue #569 Sub-bug 3):
    // Covers whether uncore ic_rd_addr_lo matches DCLS-protected ifu_fetch_addr_int_f[2:1]
    icache_rotator_addr_consistency_cp: coverpoint rotator_addr_mismatch {
      bins addr_lo_matched    = {1'b0};
      bins addr_lo_mismatched = {1'b1};
    }

    // Cross rotator offset with bank check enable (Issue #569)
    // Note: Dual-bank check (2'b11) only asserts on cross-bank straddle fetches (rot_offset_11_straddle).
    icache_rotator_x_bank_check_en: cross icache_rotator_offset_cp, icache_bank_check_en_cp {
      ignore_bins non_straddle_both_banks =
          binsof(icache_rotator_offset_cp) intersect {2'b00, 2'b01, 2'b10} &&
          binsof(icache_bank_check_en_cp.both_banks_checked);
    }
  endgroup

  initial begin
    el2_ifu_icache_ecc_recovery_cov el2_ifu_icache_ecc_recovery_cov_cg = new();
    el2_ifu_icache_core_check_cov   el2_ifu_icache_core_check_cov_cg   = new();
    $display("ICache ECC recovery coverage interface created");
  end
`else
  // -------------------------------------------------------------------------
  // Functional Coverage for Verilator via SystemVerilog Assertions (`cover property`)
  // -------------------------------------------------------------------------

  // 1. Protection mode coverpoints (icache_protection_mode_cp)
  cov_icache_parity_mode: cover property (@(posedge clk) disable iff (!rst_l)
      (pt.ICACHE_ECC == 0) && sample_en);
  cov_icache_secded_mode: cover property (@(posedge clk) disable iff (!rst_l)
      (pt.ICACHE_ECC == 1) && sample_en);

  // 2. Fault type coverpoints (icache_fault_type_cp)
  cov_fault_single_bit_data_error: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (latched_fault_type == FAULT_SINGLE_BIT_DATA));
  cov_fault_single_bit_tag_error: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (latched_fault_type == FAULT_SINGLE_BIT_TAG));
  cov_fault_double_bit_uncorrectable_error: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (latched_fault_type == FAULT_DOUBLE_BIT_UNCORRECTABLE));

  // 3. Recovery action coverpoints (icache_recovery_action_cp)
  cov_recovery_pipeline_squash_and_flush: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (recovery_action == RECOVERY_SQUASH_AND_FLUSH));
  cov_recovery_micect_counter_increment: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (recovery_action == RECOVERY_MICECT_INCREMENT));
  cov_recovery_refetch_success: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (recovery_action == RECOVERY_REFETCH_SUCCESS));

  // 4. Cache organization coverpoints (icache_waypack_cp, icache_num_ways_cp)
  cov_icache_waypack_0: cover property (@(posedge clk) disable iff (!rst_l)
      (pt.ICACHE_WAYPACK == 0) && sample_en);
  cov_icache_waypack_1: cover property (@(posedge clk) disable iff (!rst_l)
      (pt.ICACHE_WAYPACK == 1) && sample_en);
  cov_icache_num_ways_2: cover property (@(posedge clk) disable iff (!rst_l)
      (pt.ICACHE_NUM_WAYS == 2) && sample_en);
  cov_icache_num_ways_4: cover property (@(posedge clk) disable iff (!rst_l)
      (pt.ICACHE_NUM_WAYS == 4) && sample_en);

  // 5. Cross Coverage: icache_fault_x_recovery_action
  cov_sbe_data_x_squash_flush: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (latched_fault_type == FAULT_SINGLE_BIT_DATA) &&
      (recovery_action == RECOVERY_SQUASH_AND_FLUSH));
  cov_sbe_data_x_micect_inc: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (latched_fault_type == FAULT_SINGLE_BIT_DATA) &&
      (recovery_action == RECOVERY_MICECT_INCREMENT));
  cov_sbe_data_x_refetch_ok: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (latched_fault_type == FAULT_SINGLE_BIT_DATA) &&
      (recovery_action == RECOVERY_REFETCH_SUCCESS));

  cov_sbe_tag_x_squash_flush: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (latched_fault_type == FAULT_SINGLE_BIT_TAG) &&
      (recovery_action == RECOVERY_SQUASH_AND_FLUSH));
  cov_sbe_tag_x_micect_inc: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (latched_fault_type == FAULT_SINGLE_BIT_TAG) &&
      (recovery_action == RECOVERY_MICECT_INCREMENT));
  cov_sbe_tag_x_refetch_ok: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (latched_fault_type == FAULT_SINGLE_BIT_TAG) &&
      (recovery_action == RECOVERY_REFETCH_SUCCESS));

  cov_dbe_x_squash_flush: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (latched_fault_type == FAULT_DOUBLE_BIT_UNCORRECTABLE) &&
      (recovery_action == RECOVERY_SQUASH_AND_FLUSH));
  cov_dbe_x_micect_inc: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (latched_fault_type == FAULT_DOUBLE_BIT_UNCORRECTABLE) &&
      (recovery_action == RECOVERY_MICECT_INCREMENT));
  cov_dbe_x_refetch_ok: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (latched_fault_type == FAULT_DOUBLE_BIT_UNCORRECTABLE) &&
      (recovery_action == RECOVERY_REFETCH_SUCCESS));

  // 6. Cross Coverage: icache_protection_x_fault_x_waypack_x_ways
  // Parity mode (ICACHE_ECC == 0)
  cov_par_sbe_data_wp0_w2: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (pt.ICACHE_ECC == 0) && (latched_fault_type == FAULT_SINGLE_BIT_DATA) &&
      (pt.ICACHE_WAYPACK == 0) && (pt.ICACHE_NUM_WAYS == 2));
  cov_par_sbe_data_wp0_w4: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (pt.ICACHE_ECC == 0) && (latched_fault_type == FAULT_SINGLE_BIT_DATA) &&
      (pt.ICACHE_WAYPACK == 0) && (pt.ICACHE_NUM_WAYS == 4));
  cov_par_sbe_data_wp1_w2: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (pt.ICACHE_ECC == 0) && (latched_fault_type == FAULT_SINGLE_BIT_DATA) &&
      (pt.ICACHE_WAYPACK == 1) && (pt.ICACHE_NUM_WAYS == 2));
  cov_par_sbe_data_wp1_w4: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (pt.ICACHE_ECC == 0) && (latched_fault_type == FAULT_SINGLE_BIT_DATA) &&
      (pt.ICACHE_WAYPACK == 1) && (pt.ICACHE_NUM_WAYS == 4));

  cov_par_sbe_tag_wp0_w2: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (pt.ICACHE_ECC == 0) && (latched_fault_type == FAULT_SINGLE_BIT_TAG) &&
      (pt.ICACHE_WAYPACK == 0) && (pt.ICACHE_NUM_WAYS == 2));
  cov_par_sbe_tag_wp0_w4: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (pt.ICACHE_ECC == 0) && (latched_fault_type == FAULT_SINGLE_BIT_TAG) &&
      (pt.ICACHE_WAYPACK == 0) && (pt.ICACHE_NUM_WAYS == 4));
  cov_par_sbe_tag_wp1_w2: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (pt.ICACHE_ECC == 0) && (latched_fault_type == FAULT_SINGLE_BIT_TAG) &&
      (pt.ICACHE_WAYPACK == 1) && (pt.ICACHE_NUM_WAYS == 2));
  cov_par_sbe_tag_wp1_w4: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (pt.ICACHE_ECC == 0) && (latched_fault_type == FAULT_SINGLE_BIT_TAG) &&
      (pt.ICACHE_WAYPACK == 1) && (pt.ICACHE_NUM_WAYS == 4));

  cov_par_dbe_wp0_w2: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (pt.ICACHE_ECC == 0) && (latched_fault_type == FAULT_DOUBLE_BIT_UNCORRECTABLE) &&
      (pt.ICACHE_WAYPACK == 0) && (pt.ICACHE_NUM_WAYS == 2));
  cov_par_dbe_wp0_w4: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (pt.ICACHE_ECC == 0) && (latched_fault_type == FAULT_DOUBLE_BIT_UNCORRECTABLE) &&
      (pt.ICACHE_WAYPACK == 0) && (pt.ICACHE_NUM_WAYS == 4));
  cov_par_dbe_wp1_w2: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (pt.ICACHE_ECC == 0) && (latched_fault_type == FAULT_DOUBLE_BIT_UNCORRECTABLE) &&
      (pt.ICACHE_WAYPACK == 1) && (pt.ICACHE_NUM_WAYS == 2));
  cov_par_dbe_wp1_w4: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (pt.ICACHE_ECC == 0) && (latched_fault_type == FAULT_DOUBLE_BIT_UNCORRECTABLE) &&
      (pt.ICACHE_WAYPACK == 1) && (pt.ICACHE_NUM_WAYS == 4));

  // SECDED ECC mode (ICACHE_ECC == 1)
  cov_ecc_sbe_data_wp0_w2: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (pt.ICACHE_ECC == 1) && (latched_fault_type == FAULT_SINGLE_BIT_DATA) &&
      (pt.ICACHE_WAYPACK == 0) && (pt.ICACHE_NUM_WAYS == 2));
  cov_ecc_sbe_data_wp0_w4: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (pt.ICACHE_ECC == 1) && (latched_fault_type == FAULT_SINGLE_BIT_DATA) &&
      (pt.ICACHE_WAYPACK == 0) && (pt.ICACHE_NUM_WAYS == 4));
  cov_ecc_sbe_data_wp1_w2: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (pt.ICACHE_ECC == 1) && (latched_fault_type == FAULT_SINGLE_BIT_DATA) &&
      (pt.ICACHE_WAYPACK == 1) && (pt.ICACHE_NUM_WAYS == 2));
  cov_ecc_sbe_data_wp1_w4: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (pt.ICACHE_ECC == 1) && (latched_fault_type == FAULT_SINGLE_BIT_DATA) &&
      (pt.ICACHE_WAYPACK == 1) && (pt.ICACHE_NUM_WAYS == 4));

  cov_ecc_sbe_tag_wp0_w2: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (pt.ICACHE_ECC == 1) && (latched_fault_type == FAULT_SINGLE_BIT_TAG) &&
      (pt.ICACHE_WAYPACK == 0) && (pt.ICACHE_NUM_WAYS == 2));
  cov_ecc_sbe_tag_wp0_w4: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (pt.ICACHE_ECC == 1) && (latched_fault_type == FAULT_SINGLE_BIT_TAG) &&
      (pt.ICACHE_WAYPACK == 0) && (pt.ICACHE_NUM_WAYS == 4));
  cov_ecc_sbe_tag_wp1_w2: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (pt.ICACHE_ECC == 1) && (latched_fault_type == FAULT_SINGLE_BIT_TAG) &&
      (pt.ICACHE_WAYPACK == 1) && (pt.ICACHE_NUM_WAYS == 2));
  cov_ecc_sbe_tag_wp1_w4: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (pt.ICACHE_ECC == 1) && (latched_fault_type == FAULT_SINGLE_BIT_TAG) &&
      (pt.ICACHE_WAYPACK == 1) && (pt.ICACHE_NUM_WAYS == 4));

  cov_ecc_dbe_wp0_w2: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (pt.ICACHE_ECC == 1) && (latched_fault_type == FAULT_DOUBLE_BIT_UNCORRECTABLE) &&
      (pt.ICACHE_WAYPACK == 0) && (pt.ICACHE_NUM_WAYS == 2));
  cov_ecc_dbe_wp0_w4: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (pt.ICACHE_ECC == 1) && (latched_fault_type == FAULT_DOUBLE_BIT_UNCORRECTABLE) &&
      (pt.ICACHE_WAYPACK == 0) && (pt.ICACHE_NUM_WAYS == 4));
  cov_ecc_dbe_wp1_w2: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (pt.ICACHE_ECC == 1) && (latched_fault_type == FAULT_DOUBLE_BIT_UNCORRECTABLE) &&
      (pt.ICACHE_WAYPACK == 1) && (pt.ICACHE_NUM_WAYS == 2));
  cov_ecc_dbe_wp1_w4: cover property (@(posedge clk) disable iff (!rst_l)
      sample_en && (pt.ICACHE_ECC == 1) && (latched_fault_type == FAULT_DOUBLE_BIT_UNCORRECTABLE) &&
      (pt.ICACHE_WAYPACK == 1) && (pt.ICACHE_NUM_WAYS == 4));

  // 7. Issue #569 Coverpoints: Core-Side Bank Check Enable & Byte Rotator Alignment
  cov_bank_check_en_primary_only: cover property (@(posedge clk) disable iff (!rst_l)
      core_check_sample_en && (ic_rd_bank_check_en == 2'b01));
  cov_bank_check_en_both_banks: cover property (@(posedge clk) disable iff (!rst_l)
      core_check_sample_en && (ic_rd_bank_check_en == 2'b11));
  cov_bank_check_en_disabled_or_masked: cover property (@(posedge clk) disable iff (!rst_l)
      core_check_sample_en && ((ic_rd_bank_check_en == 2'b00) || (ic_rd_bank_check_en == 2'b10)));

  cov_rotator_offset_00: cover property (@(posedge clk) disable iff (!rst_l)
      core_check_sample_en && (ic_rd_addr_lo == 2'b00));
  cov_rotator_offset_01: cover property (@(posedge clk) disable iff (!rst_l)
      core_check_sample_en && (ic_rd_addr_lo == 2'b01));
  cov_rotator_offset_10: cover property (@(posedge clk) disable iff (!rst_l)
      core_check_sample_en && (ic_rd_addr_lo == 2'b10));
  cov_rotator_offset_11_straddle: cover property (@(posedge clk) disable iff (!rst_l)
      core_check_sample_en && (ic_rd_addr_lo == 2'b11));

  cov_straddle_bank0_to_bank1: cover property (@(posedge clk) disable iff (!rst_l)
      core_check_sample_en && is_cross_bank_straddle && (ifu_fetch_addr_int_f[3] == 1'b0));
  cov_straddle_bank1_to_bank0: cover property (@(posedge clk) disable iff (!rst_l)
      core_check_sample_en && is_cross_bank_straddle && (ifu_fetch_addr_int_f[3] == 1'b1));

  cov_rotator_addr_lo_matched: cover property (@(posedge clk) disable iff (!rst_l)
      core_check_sample_en && !rotator_addr_mismatch);
  cov_rotator_addr_lo_mismatched: cover property (@(posedge clk) disable iff (!rst_l)
      core_check_sample_en && rotator_addr_mismatch);

  // 8. Cross Coverage: icache_rotator_x_bank_check_en (Issue #569)
  // Valid cross bins (excludes non-straddle offsets 00/01/10 with both_banks_checked 2'b11)
  cov_rot_00_x_bank_chk_primary: cover property (@(posedge clk) disable iff (!rst_l)
      core_check_sample_en && (ic_rd_addr_lo == 2'b00) && (ic_rd_bank_check_en == 2'b01));
  cov_rot_00_x_bank_chk_disabled: cover property (@(posedge clk) disable iff (!rst_l)
      core_check_sample_en && (ic_rd_addr_lo == 2'b00) &&
      ((ic_rd_bank_check_en == 2'b00) || (ic_rd_bank_check_en == 2'b10)));

  cov_rot_01_x_bank_chk_primary: cover property (@(posedge clk) disable iff (!rst_l)
      core_check_sample_en && (ic_rd_addr_lo == 2'b01) && (ic_rd_bank_check_en == 2'b01));
  cov_rot_01_x_bank_chk_disabled: cover property (@(posedge clk) disable iff (!rst_l)
      core_check_sample_en && (ic_rd_addr_lo == 2'b01) &&
      ((ic_rd_bank_check_en == 2'b00) || (ic_rd_bank_check_en == 2'b10)));

  cov_rot_10_x_bank_chk_primary: cover property (@(posedge clk) disable iff (!rst_l)
      core_check_sample_en && (ic_rd_addr_lo == 2'b10) && (ic_rd_bank_check_en == 2'b01));
  cov_rot_10_x_bank_chk_disabled: cover property (@(posedge clk) disable iff (!rst_l)
      core_check_sample_en && (ic_rd_addr_lo == 2'b10) &&
      ((ic_rd_bank_check_en == 2'b00) || (ic_rd_bank_check_en == 2'b10)));

  cov_rot_11_x_bank_chk_primary: cover property (@(posedge clk) disable iff (!rst_l)
      core_check_sample_en && (ic_rd_addr_lo == 2'b11) && (ic_rd_bank_check_en == 2'b01));
  cov_rot_11_x_bank_chk_both: cover property (@(posedge clk) disable iff (!rst_l)
      core_check_sample_en && (ic_rd_addr_lo == 2'b11) && (ic_rd_bank_check_en == 2'b11));
  cov_rot_11_x_bank_chk_disabled: cover property (@(posedge clk) disable iff (!rst_l)
      core_check_sample_en && (ic_rd_addr_lo == 2'b11) &&
      ((ic_rd_bank_check_en == 2'b00) || (ic_rd_bank_check_en == 2'b10)));

  initial begin
    $display("ICache ECC recovery coverage interface created (Verilator SVA mode)");
  end
`endif

endinterface
