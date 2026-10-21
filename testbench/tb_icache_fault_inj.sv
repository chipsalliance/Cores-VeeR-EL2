// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Google LLC
//
// ICache Address-XOR & Outside-DCLS Boundary Fault Injection Module
// Author: Samip Modi (samipmodi@google.com)
//
// Description:
// Test-scoped fault-injection module instantiated in `tb_top` when
// `TB_ICACHE_FAULT_INJ` is defined (enabled via `.mki` by `icache_infection`
// and `icache_dcls_boundary`).
//
// - Mailboxes `0x8A` (`ifu_fetch_addr_int_f`) and `0x8D` (`imb_ff` / `ic_rw_addr`)
//   force core-internal IFU address signals unconditionally to directly verify
//   `ic_rd_addr_infect` and `ic_wr_addr_infect` in `el2_ifu_mem_ctl.sv` (and
//   replay the identical 1-cycle window `LockstepDelay` cycles later on
//   `xshadow_core` when `RV_LOCKSTEP_ENABLE` is enabled).
// - Mailboxes `0x89`, `0x8B`, `0x8C`, `0x8E`, and `0x8F` inject faults outside
//   the DCLS boundary on shared `el2_veer_wrapper` / `EL2_IC_DATA` signals.
// - Target instruction addresses are passed dynamically at runtime via Mailbox
//   commands `0xC0` (low 16 bits) and `0xC1` (high 16 bits) rather than
//   hard-coding linker-script constants in SystemVerilog, and an unfired-fault
//   guard fails simulation if any armed fault does not trigger before the next
//   command or `CMD_TEST_PASSED` (`0xFF`).

`ifdef VERILATOR
`verilator_config
inline -module "el2_veer"
inline -module "el2_ifu"
inline -module "el2_ifu_mem_ctl"
`verilog
`endif

`include "common_defines.vh"

module tb_icache_fault_inj
  import el2_pkg::*;
#(
    `include "el2_param.vh"
) (
    input logic        core_clk,
    input logic        rst_l_combined,
    input logic        mailbox_write,
    input logic [63:0] mailbox_data
);

`ifndef GATELEVEL_DUT
`ifndef RV_TRIPLE_MODULAR_REDUNDANCY_ENABLE

  `define TB_IC_VEER tb_top.rvtop_wrapper.rvtop.veer
  `define TB_IC_WRAP tb_top.rvtop_wrapper.rvtop
  `define TB_IC_DATA `TB_IC_WRAP.mem.icache.icm.ic_data_inst
  `define TB_IC_MEM_EXPORT tb_top.el2_mem_export

  // ===========================================================================
  // ICache Fault-Injection State & Single-Cycle Release Tracking Signals
  // (`*_d1` flops detect 1->0 transitions so negedge force blocks issue a
  //  single-shot `release` when a fault window closes)
  // ===========================================================================
  logic [31:1] ic_fault_target_addr;    // 0xC0/0xC1: Dynamic target fetch PC [31:1]
  logic        ic_fault_target_lo_set;  // 0xC0: Low halfword latched, awaiting 0xC1
  logic        ic_fault_target_valid;   // 0xC1: Full 31-bit target PC ready for 0x8C/0x8F

  logic        ic_perr_r_d1;            // Delayed `tlu.ic_perr_r` pulse for post-error release
  logic        next_ic_error;           // 0x89: Armed flag for 1-bit data fault on `ic_rd_data`
  logic        next_ic_error_d1;        // 0x89: Falling-edge release tracker
  logic        next_ic_addr_error;      // 0x8A: Armed flag for single-hit read-side XOR fault
  logic        next_ic_addr_error_d1;   // 0x8A: Falling-edge release tracker
  logic [4:0]  ic_addr_fault_bit;       // 0x8A: Selected fetch-address bit [ICACHE_TAG_INDEX_LO:31]
  logic        next_ic_hit_error;       // 0x8B: Armed flag for multi-bit `ic_rd_data` corruption
  logic        next_ic_hit_error_d1;    // 0x8B: Falling-edge release tracker
  logic        next_ic_way_error;       // 0x8C: Armed flag for wrong-way hit swap (`ic_rd_hit_q`)
  logic        ic_way_err_active;       // 0x8C: Latched once fetch enters target cache line
  logic        next_ic_way_error_d1;    // 0x8C: Falling-edge release tracker for `ic_rd_hit_q`
  logic        next_ic_wr_addr_error;   // 0x8D: Armed flag for write-side XOR fault on next miss
  logic        ic_wr_err_active;        // 0x8D: Active during line fill until `last_beat` write
  logic        ic_wr_err_active_d1;     // 0x8D: Falling-edge release tracker for `imb_ff`/`ic_rw_addr`
  logic        next_ic_bank1_error;     // 0x8E: Armed flag for cross-bank upper-chunk data flip
  logic        next_ic_bank1_error_d1;  // 0x8E: Falling-edge release tracker for `ic_rd_data`
  logic [2:0]  ic_dcls_boundary_mode;   // 0x8F: Active sub-mode (1..4) for `EL2_IC_DATA` faults
  logic [2:0]  ic_dcls_boundary_mode_d1;// 0x8F: Falling-edge release tracker for Mode 1..4 forces

`ifdef RV_LOCKSTEP_ENABLE
  `define TB_IC_LOCKSTEP_CORE tb_top.rvtop_wrapper.rvtop.lockstep.xshadow_core

  // ===========================================================================
  // DCLS Shadow-Core Fault Synchronization Pipeline (`LockstepDelay` cycles):
  // Replays the exact `0x8A` and `0x8D` internal IFU address fault windows on
  // `TB_IC_LOCKSTEP_CORE` `LockstepDelay` (0..4) cycles after `TB_IC_VEER`.
  // ===========================================================================
  localparam int unsigned LockstepDelay = 32'(pt.LOCKSTEP_DELAY);
  localparam int ShadowIcDelayIdx = (LockstepDelay > 0) ? (LockstepDelay - 1) : 0;

  logic [4:0]      shadow_ic_addr_error_q;
  logic            shadow_ic_addr_error;
  logic            shadow_ic_addr_error_d1;
  logic [4:0][4:0] shadow_ic_addr_fault_bit_q;
  logic [4:0]      shadow_ic_addr_fault_bit;
  logic [4:0]      shadow_ic_wr_err_active_q;
  logic            shadow_ic_wr_err_active;
  logic            shadow_ic_wr_err_active_d1;

  always @(posedge core_clk or negedge rst_l_combined) begin
    if (~rst_l_combined) begin
      shadow_ic_addr_error_q     <= '0;
      shadow_ic_addr_error_d1    <= 1'b0;
      shadow_ic_addr_fault_bit_q <= '0;
      shadow_ic_wr_err_active_q  <= '0;
      shadow_ic_wr_err_active_d1 <= 1'b0;
    end else begin
      shadow_ic_addr_error_q     <= {shadow_ic_addr_error_q[3:0], next_ic_addr_error};
      shadow_ic_addr_error_d1    <= shadow_ic_addr_error;
      shadow_ic_addr_fault_bit_q <= {shadow_ic_addr_fault_bit_q[3:0], ic_addr_fault_bit};
      shadow_ic_wr_err_active_q  <= {shadow_ic_wr_err_active_q[3:0], ic_wr_err_active};
      shadow_ic_wr_err_active_d1 <= shadow_ic_wr_err_active;
    end
  end

  assign shadow_ic_addr_error     = (LockstepDelay == 0) ? next_ic_addr_error
                                                         : shadow_ic_addr_error_q[ShadowIcDelayIdx];
  assign shadow_ic_addr_fault_bit = (LockstepDelay == 0) ? ic_addr_fault_bit
                                                         : shadow_ic_addr_fault_bit_q[ShadowIcDelayIdx];
  assign shadow_ic_wr_err_active  = (LockstepDelay == 0) ? ic_wr_err_active
                                                         : shadow_ic_wr_err_active_q[ShadowIcDelayIdx];
`endif // RV_LOCKSTEP_ENABLE

  wire is_ic_fault_cmd = mailbox_write && (
      (mailbox_data[7:0] == 8'h89) ||
      (mailbox_data[7:0] == 8'h8A) ||
      (mailbox_data[7:0] == 8'h8B) ||
      ((mailbox_data[7:0] == 8'h8C) && (mailbox_data[15:8] != 8'h00)) ||
      (mailbox_data[7:0] == 8'h8D) ||
      (mailbox_data[7:0] == 8'h8E) ||
      (mailbox_data[7:0] == 8'h8F)
  );

  wire is_test_pass_cmd = mailbox_write && (mailbox_data[7:0] == 8'hFF);

  // ===========================================================================
  // ICache Fault Injection Sequencer & `micect` CSR (0x7F0) Timing Protocol:
  // - 0xC0: Latch `ic_fault_target_addr[15:1]` from `mailbox_data[23:9]`.
  // - 0xC1: Latch `ic_fault_target_addr[31:16]` from `mailbox_data[23:8]` and
  //         mark `ic_fault_target_valid` ready for the next `0x8C` or `0x8F`.
  // - 0x89: Bank-0/1 single-bit read data fault (`ic_rd_data` bit 0 of each bank).
  // - 0x8A: Read-side Address-XOR 1-bit flip on `ifu_fetch_addr_int_f` (selected
  //         bit in `mailbox_data[15:8]`, default `ICACHE_TAG_INDEX_LO`).
  // - 0x8B: Multi-bit read data corruption (`16'h5557` pattern across both banks).
  // - 0x8C: Wrong-way selection (`mailbox_data[15:8] != 0`; swaps Way 0/1 in
  //         `ic_rd_hit_q` when fetching from `ic_fault_target_addr`).
  // - 0x8D: Write-side Address-XOR fault (inverts `imb_ff[31]` into
  //         `ic_wr_addr_infect` on `last_beat` while preserving `ic_rw_addr[31]`).
  // - 0x8E: Cross-bank upper-chunk single-bit read data fault (`ic_rd_data`).
  // - 0x8F: `EL2_IC_DATA` outside-DCLS boundary faults at `ic_fault_target_addr`
  //         (`mailbox_data[10:8]` = Mode 1..4).
  // ===========================================================================
  always @(posedge core_clk or negedge rst_l_combined) begin
    if (~rst_l_combined) begin
      ic_fault_target_addr     <= '0;
      ic_fault_target_lo_set   <= 1'b0;
      ic_fault_target_valid    <= 1'b0;
      ic_perr_r_d1             <= 1'b0;
      next_ic_error            <= 1'b0;
      next_ic_error_d1         <= 1'b0;
      next_ic_addr_error       <= 1'b0;
      next_ic_addr_error_d1    <= 1'b0;
      ic_addr_fault_bit        <= 5'(pt.ICACHE_TAG_INDEX_LO);
      next_ic_hit_error        <= 1'b0;
      next_ic_hit_error_d1     <= 1'b0;
      next_ic_way_error        <= 1'b0;
      ic_way_err_active        <= 1'b0;
      next_ic_way_error_d1     <= 1'b0;
      next_ic_wr_addr_error    <= 1'b0;
      ic_wr_err_active         <= 1'b0;
      ic_wr_err_active_d1      <= 1'b0;
      next_ic_bank1_error      <= 1'b0;
      next_ic_bank1_error_d1   <= 1'b0;
      ic_dcls_boundary_mode    <= 3'd0;
      ic_dcls_boundary_mode_d1 <= 3'd0;
    end else begin
      ic_perr_r_d1             <= `TB_IC_VEER.dec.tlu.ic_perr_r;
      next_ic_error_d1         <= next_ic_error;
      next_ic_addr_error_d1    <= next_ic_addr_error;
      next_ic_hit_error_d1     <= next_ic_hit_error;
      next_ic_way_error_d1     <= next_ic_way_error;
      ic_wr_err_active_d1      <= ic_wr_err_active;
      next_ic_bank1_error_d1   <= next_ic_bank1_error;
      ic_dcls_boundary_mode_d1 <= ic_dcls_boundary_mode;

      // Guard: fail immediately if any previously armed fault never fired
      // before the next fault command or `CMD_TEST_PASSED` (`0xFF`).
      if (is_ic_fault_cmd || is_test_pass_cmd) begin
        if (next_ic_error ||
            next_ic_addr_error ||
            next_ic_hit_error ||
            next_ic_way_error ||
            next_ic_wr_addr_error ||
            next_ic_bank1_error ||
            (ic_dcls_boundary_mode != 3'd0)) begin
          $fatal(1, "TEST_FAILED: [tb_icache_fault_inj] Armed fault did not trigger before mailbox 0x%02x (err=%b addr=%b hit=%b way=%b wr=%b b1=%b mode=%0d)!",
                 mailbox_data[7:0], next_ic_error, next_ic_addr_error,
                 next_ic_hit_error, next_ic_way_error,
                 next_ic_wr_addr_error, next_ic_bank1_error, ic_dcls_boundary_mode);
        end
      end

      // Mailbox 0xC0 / 0xC1: Latch dynamic 32-bit target instruction address [31:1]
      if (mailbox_write && (mailbox_data[7:0] == 8'hC0)) begin
        ic_fault_target_addr[15:1] <= mailbox_data[23:9];
        ic_fault_target_lo_set     <= 1'b1;
        ic_fault_target_valid      <= 1'b0;
      end else if (mailbox_write && (mailbox_data[7:0] == 8'hC1)) begin
        if (!ic_fault_target_lo_set) begin
          $fatal(1, "TEST_FAILED: [tb_icache_fault_inj] Mailbox 0xC1 (ADDR_HI) written without preceding 0xC0 (ADDR_LO)!");
        end
        ic_fault_target_addr[31:16] <= mailbox_data[23:8];
        ic_fault_target_lo_set      <= 1'b0;
        ic_fault_target_valid       <= 1'b1;
      end

      // Mailbox 0x89: Single-bit read data corruption on `ic_rd_data`
      if (mailbox_write && (mailbox_data[7:0] == 8'h89)) begin
        next_ic_error <= 1'b1;
      end else if (next_ic_error && ic_perr_r_d1) begin
        next_ic_error <= 1'b0;
      end

      // Mailbox 0x8A: Single-hit read-side Address-XOR 1-bit flip on `ifu_fetch_addr_int_f`.
      // Clears on the first `ic_act_hit_f` so back-to-back cache hits never double-count `micect`.
      if (mailbox_write && (mailbox_data[7:0] == 8'h8A)) begin
        next_ic_addr_error <= 1'b1;
        ic_addr_fault_bit  <= (mailbox_data[15:8] == 8'd0) ?
                              5'(pt.ICACHE_TAG_INDEX_LO) : mailbox_data[12:8];
      end else if (next_ic_addr_error && `TB_IC_VEER.ifu.mem_ctl.ic_act_hit_f) begin
        next_ic_addr_error <= 1'b0;
      end

      // Mailbox 0x8B: Multi-bit read data corruption across both banks
      if (mailbox_write && (mailbox_data[7:0] == 8'h8B)) begin
        next_ic_hit_error <= 1'b1;
      end else if (next_ic_hit_error && ic_perr_r_d1) begin
        next_ic_hit_error <= 1'b0;
      end

      // Mailbox 0x8C (`mailbox_data[15:8] != 0`): Wrong-way selection (`ic_rd_hit_q`
      // swap in `EL2_IC_DATA`) when fetching within the 128B window at `ic_fault_target_addr`.
      if (mailbox_write && (mailbox_data[7:0] == 8'h8C) && (mailbox_data[15:8] != 8'h00)) begin
        if (!ic_fault_target_valid) begin
          $fatal(1, "TEST_FAILED: [tb_icache_fault_inj] Mailbox 0x8C armed without target address (0xC0/0xC1)!");
        end
        next_ic_way_error     <= 1'b1;
        ic_way_err_active     <= 1'b0;
        ic_fault_target_valid <= 1'b0;
      end else if (next_ic_way_error) begin
        if (ic_perr_r_d1 ||
            (ic_way_err_active && `TB_IC_VEER.ifu.mem_ctl.ic_act_hit_f &&
             (`TB_IC_VEER.ifu.mem_ctl.ifu_fetch_addr_int_f[31:7] != ic_fault_target_addr[31:7]))) begin
          next_ic_way_error <= 1'b0;
          ic_way_err_active <= 1'b0;
        end else if (`TB_IC_VEER.ifu.mem_ctl.ic_act_hit_f &&
                     (`TB_IC_VEER.ifu.mem_ctl.ifu_fetch_addr_int_f[31:7] == ic_fault_target_addr[31:7]) &&
                     (&`TB_IC_WRAP.ic_tag_valid[1:0])) begin
          ic_way_err_active <= 1'b1;
        end
      end

      // Mailbox 0x8D: Write-side Address-XOR fault on `last_beat` of next cache miss
      if (mailbox_write && (mailbox_data[7:0] == 8'h8D)) begin
        next_ic_wr_addr_error <= 1'b1;
        ic_wr_err_active      <= 1'b0;
      end else if (next_ic_wr_addr_error) begin
        if (ic_wr_err_active &&
            `TB_IC_VEER.ifu.mem_ctl.last_beat &&
            `TB_IC_VEER.ifu.mem_ctl.bus_ifu_wr_en_ff) begin
          next_ic_wr_addr_error <= 1'b0;
          ic_wr_err_active      <= 1'b0;
        end else if (`TB_IC_VEER.ifu.mem_ctl.ic_act_miss_f) begin
          ic_wr_err_active <= 1'b1;
        end
      end

      // Mailbox 0x8E: Single-hit cross-bank upper-chunk read data fault
      if (mailbox_write && (mailbox_data[7:0] == 8'h8E)) begin
        next_ic_bank1_error <= 1'b1;
      end else if (next_ic_bank1_error &&
                   (ic_perr_r_d1 ||
                    (`TB_IC_VEER.ifu.mem_ctl.ic_act_hit_f &&
                     (`TB_IC_VEER.ifu.mem_ctl.ifu_fetch_addr_int_f[2:1] == 2'b11)))) begin
        next_ic_bank1_error <= 1'b0;
      end

      // Mailbox 0x8F: `EL2_IC_DATA` outside-DCLS boundary faults at `ic_fault_target_addr`
      if (mailbox_write && (mailbox_data[7:0] == 8'h8F)) begin
        if (!ic_fault_target_valid ||
            (mailbox_data[10:8] < 3'd1) || (mailbox_data[10:8] > 3'd4)) begin
          $fatal(1, "TEST_FAILED: [tb_icache_fault_inj] Invalid Mailbox 0x8F arming (target_valid=%b, mode=%0d)!",
                 ic_fault_target_valid, mailbox_data[10:8]);
        end
        ic_dcls_boundary_mode <= mailbox_data[10:8];
        ic_fault_target_valid <= 1'b0;
      end else if (ic_dcls_boundary_mode != 3'd0) begin
        if (`TB_IC_VEER.ifu.mem_ctl.ic_act_hit_f &&
            (`TB_IC_VEER.ifu.mem_ctl.ifu_fetch_addr_int_f == ic_fault_target_addr)) begin
          ic_dcls_boundary_mode <= 3'd0;
        end
      end
    end
  end

  // ===========================================================================
  // Force Drivers (`negedge core_clk`):
  // Grouped strictly by target RTL signal so each net has a single `force`/`release`
  // driver, and driven on `negedge core_clk` after `posedge core_clk` state/SRAM
  // outputs settle and before F-stage ECC/parity capture.
  // ===========================================================================
  always @(negedge core_clk) begin
    // 1a. 0x8A (Primary Core): Unconditional 1-bit flip on `ifu_fetch_addr_int_f`
    //     during `ic_act_hit_f` to verify `ic_rd_addr_infect` directly.
    if (next_ic_addr_error && `TB_IC_VEER.ifu.mem_ctl.ic_act_hit_f) begin
      force `TB_IC_VEER.ifu.mem_ctl.ifu_fetch_addr_int_f =
          `TB_IC_VEER.ifu.mem_ctl.ifu_fetch_addr_f_ff.dout ^
          (31'd1 << (ic_addr_fault_bit - 5'd1));
    end else if (next_ic_addr_error || next_ic_addr_error_d1) begin
      release `TB_IC_VEER.ifu.mem_ctl.ifu_fetch_addr_int_f;
    end

    // 1b. 0x8D (Primary Core): Unconditional 1-bit flip on `imb_ff[31]` on
    //     `last_beat` while canceling `ic_rw_addr[31]` so the cache line is
    //     written to its true tag/set with an inverted `ic_wr_addr_infect` MSB.
    if (ic_wr_err_active &&
        `TB_IC_VEER.ifu.mem_ctl.write_ic_16_bytes &&
        `TB_IC_VEER.ifu.mem_ctl.last_beat &&
        !`TB_IC_VEER.ifu.mem_ctl.ic_act_miss_f) begin
      force `TB_IC_VEER.ifu.mem_ctl.imb_ff =
          `TB_IC_VEER.ifu.mem_ctl.imb_f_ff.dout ^ 31'h4000_0000;
      force `TB_IC_VEER.ifu.mem_ctl.ic_rw_addr =
          `TB_IC_VEER.ifu.mem_ctl.ifu_ic_rw_int_addr ^
          {`TB_IC_VEER.ifu.mem_ctl.sel_mb_addr, 30'b0};
    end else if (ic_wr_err_active || ic_wr_err_active_d1) begin
      release `TB_IC_VEER.ifu.mem_ctl.imb_ff;
      release `TB_IC_VEER.ifu.mem_ctl.ic_rw_addr;
    end

`ifdef RV_LOCKSTEP_ENABLE
    // 1c. 0x8A & 0x8D (Shadow Core): Synchronized `LockstepDelay` cycles later.
    if (shadow_ic_addr_error && `TB_IC_LOCKSTEP_CORE.ifu.mem_ctl.ic_act_hit_f) begin
      force `TB_IC_LOCKSTEP_CORE.ifu.mem_ctl.ifu_fetch_addr_int_f =
          `TB_IC_LOCKSTEP_CORE.ifu.mem_ctl.ifu_fetch_addr_f_ff.dout ^
          (31'd1 << (shadow_ic_addr_fault_bit - 5'd1));
    end else if (shadow_ic_addr_error || shadow_ic_addr_error_d1) begin
      release `TB_IC_LOCKSTEP_CORE.ifu.mem_ctl.ifu_fetch_addr_int_f;
    end

    if (shadow_ic_wr_err_active &&
        `TB_IC_LOCKSTEP_CORE.ifu.mem_ctl.write_ic_16_bytes &&
        `TB_IC_LOCKSTEP_CORE.ifu.mem_ctl.last_beat &&
        !`TB_IC_LOCKSTEP_CORE.ifu.mem_ctl.ic_act_miss_f) begin
      force `TB_IC_LOCKSTEP_CORE.ifu.mem_ctl.imb_ff =
          `TB_IC_LOCKSTEP_CORE.ifu.mem_ctl.imb_f_ff.dout ^ 31'h4000_0000;
      force `TB_IC_LOCKSTEP_CORE.ifu.mem_ctl.ic_rw_addr =
          `TB_IC_LOCKSTEP_CORE.ifu.mem_ctl.ifu_ic_rw_int_addr ^
          {`TB_IC_LOCKSTEP_CORE.ifu.mem_ctl.sel_mb_addr, 30'b0};
    end else if (shadow_ic_wr_err_active || shadow_ic_wr_err_active_d1) begin
      release `TB_IC_LOCKSTEP_CORE.ifu.mem_ctl.imb_ff;
      release `TB_IC_LOCKSTEP_CORE.ifu.mem_ctl.ic_rw_addr;
    end
`endif // RV_LOCKSTEP_ENABLE

`ifdef RV_ICACHE_ENABLE
    // 2. Shared `ic_rd_data` faults (0x89, 0x8B, 0x8E Bank-1, 0x8F Mode 1)
    if (next_ic_error) begin
      force `TB_IC_WRAP.ic_rd_data = `RV_ICACHE_ECC ? {71'h1, 71'h1}
                                                    : {6'b0, 68'h1, 68'h1};
    end else if (next_ic_hit_error) begin
      force `TB_IC_WRAP.ic_rd_data = `RV_ICACHE_ECC
          ? {71'h5557_5557_5557_5557, 71'h5557_5557_5557_5557}
          : {6'b0, 68'h5557_5557_5557_5557, 68'h5557_5557_5557_5557};
    end else if (next_ic_bank1_error &&
                 (`TB_IC_VEER.ifu.mem_ctl.ifu_fetch_addr_int_f[2:1] == 2'b11)) begin
      force `TB_IC_WRAP.ic_rd_data =
          `TB_IC_DATA.wb_dout_ecc ^
          (`TB_IC_VEER.ifu.mem_ctl.ifu_fetch_addr_int_f[3] ? 142'd1 : (142'd1 << 71));
    end else if ((ic_dcls_boundary_mode == 3'd1) &&
                 `TB_IC_VEER.ifu.mem_ctl.ic_act_hit_f &&
                 (`TB_IC_VEER.ifu.mem_ctl.ifu_fetch_addr_int_f == ic_fault_target_addr)) begin
      force `TB_IC_WRAP.ic_rd_data =
          `TB_IC_DATA.wb_dout_ecc ^
          (`RV_ICACHE_ECC ? (142'd1 << 75) : (142'd1 << 72));
    end else if (next_ic_error_d1 || next_ic_hit_error_d1 ||
                 next_ic_bank1_error || next_ic_bank1_error_d1 ||
                 (ic_dcls_boundary_mode == 3'd1) || (ic_dcls_boundary_mode_d1 == 3'd1)) begin
      release `TB_IC_WRAP.ic_rd_data;
    end

    // 3. 0x8C: Wrong-way selection (`EL2_IC_DATA.ic_rd_hit_q`)
    if (next_ic_way_error &&
        (`TB_IC_VEER.ifu.mem_ctl.ifu_fetch_addr_int_f[31:7] == ic_fault_target_addr[31:7]) &&
        (&`TB_IC_WRAP.ic_tag_valid[1:0]) &&
        (|`TB_IC_WRAP.ic_rd_hit[1:0])) begin
      force `TB_IC_DATA.ic_rd_hit_q =
          `TB_IC_WRAP.ic_rd_hit ^ (pt.ICACHE_NUM_WAYS)'(2'b11);
    end else if (next_ic_way_error || next_ic_way_error_d1) begin
      release `TB_IC_DATA.ic_rd_hit_q;
    end

    // 4. 0x8F Mode 2 (BF-stage): Suppress `EL2_IC_DATA` Bank-1 SRAM read enable
    if ((ic_dcls_boundary_mode == 3'd2) &&
        `TB_IC_VEER.ifu.mem_ctl.ifc_fetch_req_bf &&
        !`TB_IC_VEER.ifu.mem_ctl.sel_mb_addr &&
        (`TB_IC_VEER.ifu.mem_ctl.ifc_fetch_addr_bf == ic_fault_target_addr)) begin
      force `TB_IC_DATA.ic_b_read_en = 2'b01;
      force `TB_IC_DATA.ic_b_read_en_up = {pt.ICACHE_NUM_WAYS{2'b01}};
      force `TB_IC_MEM_EXPORT.ic_bank_way_clken_final = 2'b01;
      force `TB_IC_MEM_EXPORT.ic_bank_way_clken_final_up = {pt.ICACHE_NUM_WAYS{2'b01}};
    end else if ((ic_dcls_boundary_mode == 3'd2) || (ic_dcls_boundary_mode_d1 == 3'd2)) begin
      release `TB_IC_DATA.ic_b_read_en;
      release `TB_IC_DATA.ic_b_read_en_up;
      release `TB_IC_MEM_EXPORT.ic_bank_way_clken_final;
      release `TB_IC_MEM_EXPORT.ic_bank_way_clken_final_up;
    end

    // 5. 0x8F Mode 1 & Mode 2 (F-stage): Force `EL2_IC_DATA.ic_b_rden_ff` check-enable flops
    if ((ic_dcls_boundary_mode == 3'd1) &&
        `TB_IC_VEER.ifu.mem_ctl.ic_act_hit_f &&
        (`TB_IC_VEER.ifu.mem_ctl.ifu_fetch_addr_int_f == ic_fault_target_addr)) begin
      force `TB_IC_DATA.ic_b_rden_ff = 2'b00;
    end else if ((ic_dcls_boundary_mode == 3'd2) &&
                 `TB_IC_VEER.ifu.mem_ctl.ic_act_hit_f &&
                 (`TB_IC_VEER.ifu.mem_ctl.ifu_fetch_addr_int_f == ic_fault_target_addr)) begin
      force `TB_IC_DATA.ic_b_rden_ff = 2'b01;
    end else if ((ic_dcls_boundary_mode == 3'd1) || (ic_dcls_boundary_mode_d1 == 3'd1) ||
                 (ic_dcls_boundary_mode == 3'd2) || (ic_dcls_boundary_mode_d1 == 3'd2)) begin
      release `TB_IC_DATA.ic_b_rden_ff;
    end

    // 6. 0x8F Mode 1, Mode 3 & Mode 4 (F-stage): Force `EL2_IC_DATA.ic_rw_addr_ff`
    //    (`logic [pt.ICACHE_TAG_INDEX_LO-1:1]`, 1-based LSB at bit 1):
    //    - Mode 1 (`ic_rw_addr_ff = '1`): false cacheline-wrap alongside `ic_b_rden_ff = 2'b00`.
    //    - Mode 3 (`ic_rw_addr_ff[2:1] = 2'b10`): tests core-side byte rotator (`ic_rd_rot_sel`).
    //    - Mode 4 (`ic_rw_addr_ff[3]   = 1'b1`):  tests core-side bank select (`ic_rd_bank_sel`).
    if ((ic_dcls_boundary_mode == 3'd1) &&
        `TB_IC_VEER.ifu.mem_ctl.ic_act_hit_f &&
        (`TB_IC_VEER.ifu.mem_ctl.ifu_fetch_addr_int_f == ic_fault_target_addr)) begin
      force `TB_IC_DATA.ic_rw_addr_ff = '1;
    end else if ((ic_dcls_boundary_mode == 3'd3) &&
                 `TB_IC_VEER.ifu.mem_ctl.ic_act_hit_f &&
                 (`TB_IC_VEER.ifu.mem_ctl.ifu_fetch_addr_int_f == ic_fault_target_addr)) begin
      force `TB_IC_DATA.ic_rw_addr_ff = {{(pt.ICACHE_TAG_INDEX_LO - 3){1'b0}}, 2'b10};
    end else if ((ic_dcls_boundary_mode == 3'd4) &&
                 `TB_IC_VEER.ifu.mem_ctl.ic_act_hit_f &&
                 (`TB_IC_VEER.ifu.mem_ctl.ifu_fetch_addr_int_f == ic_fault_target_addr)) begin
      force `TB_IC_DATA.ic_rw_addr_ff = {{(pt.ICACHE_TAG_INDEX_LO - 4){1'b0}}, 1'b1, 2'b00};
    end else if ((ic_dcls_boundary_mode == 3'd1) || (ic_dcls_boundary_mode_d1 == 3'd1) ||
                 (ic_dcls_boundary_mode == 3'd3) || (ic_dcls_boundary_mode_d1 == 3'd3) ||
                 (ic_dcls_boundary_mode == 3'd4) || (ic_dcls_boundary_mode_d1 == 3'd4)) begin
      release `TB_IC_DATA.ic_rw_addr_ff;
    end
  end
`endif // RV_ICACHE_ENABLE

`undef TB_IC_VEER
`undef TB_IC_WRAP
`undef TB_IC_DATA
`undef TB_IC_MEM_EXPORT
`ifdef TB_IC_LOCKSTEP_CORE
  `undef TB_IC_LOCKSTEP_CORE
`endif

`endif // !RV_TRIPLE_MODULAR_REDUNDANCY_ENABLE
`endif // !GATELEVEL_DUT

endmodule : tb_icache_fault_inj
