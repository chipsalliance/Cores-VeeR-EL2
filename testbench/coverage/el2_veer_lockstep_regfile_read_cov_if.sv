/*
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2026 Google LLC
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

//-----------------------------------------------------------------------------------------
// Dual-mode functional coverage interface for VCS (covergroup) and Verilator (SVA cover property)
// Target: Task 5 - Register File Read Port Comparison Coverage (el2_veer_lockstep_regfile_read_cov)
//-----------------------------------------------------------------------------------------

`include "common_defines.vh"

interface el2_veer_lockstep_regfile_read_cov_if
  import el2_pkg::*;
  import el2_mubi_pkg::*;
  import el2_lockstep_pkg::*;
#(
    `include "el2_param.vh"
) (
    input logic          clk,
    input logic          rst_n,
`ifdef RV_LOCKSTEP_REGFILE_ENABLE
    input logic          regfile_corrupted,
  `ifdef RV_LOCKSTEP_REGFILE_READ_ENABLE
    input logic [31:0]   main_gpr_rd0,
    input logic [31:0]   main_gpr_rd1,
    input logic [31:0]   shadow_gpr_rd0,
    input logic [31:0]   shadow_gpr_rd1,
  `else
    input logic [351:0]  main_gpr_pkt,
    input logic [351:0]  shadow_gpr_pkt,
  `endif
`endif
    input logic [4:0]    shadow_raddr0,
    input logic [4:0]    shadow_raddr1,
    input logic          shadow_dec_i0_decode_d,
    input logic          shadow_dec_i0_alu_decode_d,
    input logic          shadow_dec_i0_branch_d,
    input logic [31:0]   shadow_dec_i0_instr_d,
    input el2_lsu_pkt_t  shadow_lsu_p,
    input veer_outputs_t shadow_core_outputs,
    input el2_mubi_t     corruption_detected_o
);

    localparam int unsigned LockstepDelay = 32'(pt.LOCKSTEP_DELAY);
    localparam int LockstepDelayPipeStages = (LockstepDelay > 0) ? int'(LockstepDelay - 1) : 0;

`ifdef RV_LOCKSTEP_REGFILE_READ_ENABLE
    localparam bit RegfileReadEnable = 1'b1;
`else
    localparam bit RegfileReadEnable = 1'b0;
`endif

    // -------------------------------------------------------------------------
    // 1. Lockstep Delay Alignment & Read Port Divergence Tracking
    // -------------------------------------------------------------------------
    logic       rd0_divergence;
    logic       rd1_divergence;
    logic [1:0] regfile_read_port_diff_cats;
    logic [4:0] monitored_gpr_div_reg;

`ifdef RV_LOCKSTEP_REGFILE_ENABLE
  `ifdef RV_LOCKSTEP_REGFILE_READ_ENABLE
    logic [31:0] delayed_main_rd0;
    logic [31:0] delayed_main_rd1;

    if (LockstepDelay > 0) begin : gen_delayed_rd_ports
        logic [LockstepDelayPipeStages:0][31:0] delay_rd0_q;
        logic [LockstepDelayPipeStages:0][31:0] delay_rd1_q;

        always_ff @(posedge clk or negedge rst_n) begin
            if (!rst_n) begin
                delay_rd0_q[0] <= 32'h0;
                delay_rd1_q[0] <= 32'h0;
            end else begin
                delay_rd0_q[0] <= main_gpr_rd0;
                delay_rd1_q[0] <= main_gpr_rd1;
            end
        end

        for (genvar i = 0; i < LockstepDelayPipeStages; i++) begin : gen_pipe
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
                    delay_rd0_q[i+1] <= 32'h0;
                    delay_rd1_q[i+1] <= 32'h0;
                end else begin
                    delay_rd0_q[i+1] <= delay_rd0_q[i];
                    delay_rd1_q[i+1] <= delay_rd1_q[i];
                end
            end
        end

        assign delayed_main_rd0 = delay_rd0_q[LockstepDelayPipeStages];
        assign delayed_main_rd1 = delay_rd1_q[LockstepDelayPipeStages];
    end else begin : gen_raw_rd_ports
        assign delayed_main_rd0 = main_gpr_rd0;
        assign delayed_main_rd1 = main_gpr_rd1;
    end

    assign rd0_divergence        = (delayed_main_rd0 != shadow_gpr_rd0) & (shadow_raddr0 != 5'd0);
    assign rd1_divergence        = (delayed_main_rd1 != shadow_gpr_rd1) & (shadow_raddr1 != 5'd0);
    assign monitored_gpr_div_reg = 5'd0;
  `else
    logic [351:0] delayed_main_gpr_pkt;

    if (LockstepDelay > 0) begin : gen_delayed_gpr_pkt
        logic [LockstepDelayPipeStages:0][351:0] delay_gpr_pkt_q;

        always_ff @(posedge clk or negedge rst_n) begin
            if (!rst_n) begin
                delay_gpr_pkt_q[0] <= '0;
            end else begin
                delay_gpr_pkt_q[0] <= main_gpr_pkt;
            end
        end

        for (genvar i = 0; i < LockstepDelayPipeStages; i++) begin : gen_pipe
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
                    delay_gpr_pkt_q[i+1] <= '0;
                end else begin
                    delay_gpr_pkt_q[i+1] <= delay_gpr_pkt_q[i];
                end
            end
        end

        assign delayed_main_gpr_pkt = delay_gpr_pkt_q[LockstepDelayPipeStages];
    end else begin : gen_raw_gpr_pkt
        assign delayed_main_gpr_pkt = main_gpr_pkt;
    end

    function automatic logic [31:0] get_monitored_gpr_val(
        input logic [351:0] gpr_pkt,
        input logic [4:0]   reg_idx
    );
        // Packed layout in el2_regfile_if.sv: ra, sp, fp, a0, a1, a2, a3, a4, a5, a6, a7
        case (reg_idx)
            5'd1:    return gpr_pkt[351:320]; // ra (x1)
            5'd2:    return gpr_pkt[319:288]; // sp (x2)
            5'd8:    return gpr_pkt[287:256]; // s0/fp (x8)
            5'd10:   return gpr_pkt[255:224]; // a0 (x10)
            5'd11:   return gpr_pkt[223:192]; // a1 (x11)
            5'd12:   return gpr_pkt[191:160]; // a2 (x12)
            5'd13:   return gpr_pkt[159:128]; // a3 (x13)
            5'd14:   return gpr_pkt[127:96];  // a4 (x14)
            5'd15:   return gpr_pkt[95:64];   // a5 (x15)
            5'd16:   return gpr_pkt[63:32];   // a6 (x16)
            5'd17:   return gpr_pkt[31:0];    // a7 (x17)
            default: return 32'h0;
        endcase
    endfunction

    function automatic logic [4:0] get_first_diverging_monitored_gpr(
        input logic [351:0] main_pkt,
        input logic [351:0] shadow_pkt
    );
        if (main_pkt[351:320] != shadow_pkt[351:320]) return 5'd1;  // ra
        if (main_pkt[319:288] != shadow_pkt[319:288]) return 5'd2;  // sp
        if (main_pkt[287:256] != shadow_pkt[287:256]) return 5'd8;  // s0/fp
        if (main_pkt[255:224] != shadow_pkt[255:224]) return 5'd10; // a0
        if (main_pkt[223:192] != shadow_pkt[223:192]) return 5'd11; // a1
        if (main_pkt[191:160] != shadow_pkt[191:160]) return 5'd12; // a2
        if (main_pkt[159:128] != shadow_pkt[159:128]) return 5'd13; // a3
        if (main_pkt[127:96]  != shadow_pkt[127:96])  return 5'd14; // a4
        if (main_pkt[95:64]   != shadow_pkt[95:64])   return 5'd15; // a5
        if (main_pkt[63:32]   != shadow_pkt[63:32])   return 5'd16; // a6
        if (main_pkt[31:0]    != shadow_pkt[31:0])    return 5'd17; // a7
        return 5'd0;
    endfunction

    logic [31:0] main_monitored_rd0;
    logic [31:0] shadow_monitored_rd0;
    logic [31:0] main_monitored_rd1;
    logic [31:0] shadow_monitored_rd1;

    assign main_monitored_rd0    = get_monitored_gpr_val(delayed_main_gpr_pkt, shadow_raddr0);
    assign shadow_monitored_rd0  = get_monitored_gpr_val(shadow_gpr_pkt, shadow_raddr0);
    assign main_monitored_rd1    = get_monitored_gpr_val(delayed_main_gpr_pkt, shadow_raddr1);
    assign shadow_monitored_rd1  = get_monitored_gpr_val(shadow_gpr_pkt, shadow_raddr1);

    assign rd0_divergence        = (main_monitored_rd0 != shadow_monitored_rd0) & (shadow_raddr0 != 5'd0);
    assign rd1_divergence        = (main_monitored_rd1 != shadow_monitored_rd1) & (shadow_raddr1 != 5'd0);
    assign monitored_gpr_div_reg = get_first_diverging_monitored_gpr(delayed_main_gpr_pkt, shadow_gpr_pkt);
  `endif
`else
    assign rd0_divergence        = 1'b0;
    assign rd1_divergence        = 1'b0;
    assign monitored_gpr_div_reg = 5'd0;
`endif

    assign regfile_read_port_diff_cats = {rd1_divergence, rd0_divergence};

    // -------------------------------------------------------------------------
    // 2. Target Architectural Register Divergence & Instruction Type Tracking
    // -------------------------------------------------------------------------
    logic [4:0] immediate_div_reg;
    logic [4:0] last_div_reg_q;
    logic [4:0] target_reg_div;
    logic       reg_divergence_active;

    assign immediate_div_reg = rd0_divergence ? shadow_raddr0 :
                               rd1_divergence ? shadow_raddr1 :
                               monitored_gpr_div_reg;

    // Retain the diverging register index across the fault-handling window of the
    // current test case (until core reset) so instruction types executing during
    // the divergence and trap sequence are associated with the diverging register.
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            last_div_reg_q <= 5'd0;
        end else if (immediate_div_reg != 5'd0) begin
            last_div_reg_q <= immediate_div_reg;
        end
    end

    assign target_reg_div = (immediate_div_reg != 5'd0) ? immediate_div_reg : last_div_reg_q;

    assign reg_divergence_active = (target_reg_div != 5'd0) & (
        (immediate_div_reg != 5'd0)
`ifdef RV_LOCKSTEP_REGFILE_ENABLE
        | regfile_corrupted
`endif
        | mubi_check_true(corruption_detected_o)
        | (last_div_reg_q != 5'd0)
    );

    // Instruction type classification (ALU, Branch, Store, Load address)
    logic       d_stage_is_load;
    logic       d_stage_is_store;
    logic       d_stage_is_branch;
    logic       d_stage_is_alu;
    logic       wb_stage_is_load;
    logic       wb_stage_is_store;
    logic       wb_stage_is_branch;
    logic       wb_stage_is_alu;
    logic       is_alu_instr;
    logic       is_branch_instr;
    logic       is_store_instr;
    logic       is_load_instr;
    logic [3:0] instr_type_cats;

    assign d_stage_is_load   = (shadow_lsu_p.valid & shadow_lsu_p.load) |
                               (shadow_dec_i0_decode_d & (shadow_dec_i0_instr_d[6:0] == 7'b0000011));
    assign d_stage_is_store  = (shadow_lsu_p.valid & shadow_lsu_p.store) |
                               (shadow_dec_i0_decode_d & (shadow_dec_i0_instr_d[6:0] == 7'b0100011));
    assign d_stage_is_branch = (shadow_dec_i0_decode_d & shadow_dec_i0_branch_d) |
                               (shadow_dec_i0_decode_d & (shadow_dec_i0_instr_d[6:0] inside {
                                   7'b1100011, 7'b1101111, 7'b1100111
                               }));
    assign d_stage_is_alu    = (shadow_dec_i0_decode_d & shadow_dec_i0_alu_decode_d & ~shadow_dec_i0_branch_d) |
                               (shadow_dec_i0_decode_d & (shadow_dec_i0_instr_d[6:0] inside {
                                   7'b0010011, 7'b0110011, 7'b0110111, 7'b0010111, 7'b1110011
                               }));

    assign wb_stage_is_load   = shadow_core_outputs.dccm_rden |
                                shadow_core_outputs.lsu_axi_arvalid |
                                (shadow_core_outputs.trace_rv_i_valid_ip &
                                 (shadow_core_outputs.trace_rv_i_insn_ip[6:0] == 7'b0000011));
    assign wb_stage_is_store  = shadow_core_outputs.dccm_wren |
                                shadow_core_outputs.lsu_axi_awvalid |
                                (shadow_core_outputs.trace_rv_i_valid_ip &
                                 (shadow_core_outputs.trace_rv_i_insn_ip[6:0] == 7'b0100011));
    assign wb_stage_is_branch = shadow_core_outputs.trace_rv_i_valid_ip &
                                (shadow_core_outputs.trace_rv_i_insn_ip[6:0] inside {
                                    7'b1100011, 7'b1101111, 7'b1100111
                                });
    assign wb_stage_is_alu    = shadow_core_outputs.trace_rv_i_valid_ip &
                                (shadow_core_outputs.trace_rv_i_insn_ip[6:0] inside {
                                    7'b0010011, 7'b0110011, 7'b0110111, 7'b0010111, 7'b1110011
                                });

    assign is_alu_instr    = d_stage_is_alu    | wb_stage_is_alu;
    assign is_branch_instr = d_stage_is_branch | wb_stage_is_branch;
    assign is_store_instr  = d_stage_is_store  | wb_stage_is_store;
    assign is_load_instr   = d_stage_is_load   | wb_stage_is_load;

    assign instr_type_cats = {
        is_load_instr,
        is_store_instr,
        is_branch_instr,
        is_alu_instr
    };

`ifndef VERILATOR
    // -------------------------------------------------------------------------
    // VCS / IEEE 1800 Covergroup: Register File Read Port Comparison Coverage
    // -------------------------------------------------------------------------
    covergroup el2_veer_lockstep_regfile_read_cov @(posedge clk iff rst_n);
        option.per_instance = 1;

        // 1. Coverpoint regfile_read_enable_config_cp:
        // - full_regfile_mode: RV_LOCKSTEP_REGFILE_READ_ENABLE == 0 (Flop subset comparison)
        // - read_port_mode: RV_LOCKSTEP_REGFILE_READ_ENABLE == 1 (Read port rd0/rd1 comparison)
        regfile_read_enable_config_cp: coverpoint RegfileReadEnable {
            bins full_regfile_mode = {1'b0};
            bins read_port_mode    = {1'b1};
        }

        // 2. Coverpoint regfile_read_port_diff_cp:
        // - rd0_divergence: Main core rd0_data differs from shadow core rd0_data
        // - rd1_divergence: Main core rd1_data differs from shadow core rd1_data
        regfile_read_port_diff_cp: coverpoint regfile_read_port_diff_cats {
            wildcard bins rd0_divergence = {2'b?1};
            wildcard bins rd1_divergence = {2'b1?};
        }

        // 3. Coverpoint target_register_divergence_cp:
        // Individual bins tracking which architectural register differed when read
        target_register_divergence_cp: coverpoint target_reg_div iff (reg_divergence_active) {
            // Zero register x0 (hardwired to 0; must never diverge)
            illegal_bins zero_x0 = {5'd0};
            // Return address ra (x1)
            bins ra              = {5'd1};
            // Stack pointer sp (x2)
            bins sp              = {5'd2};
            // Saved registers s0/fp (x8), s1 (x9)
            bins s0_fp           = {5'd8};
            bins s1              = {5'd9};
            // Argument registers a0 through a7 (x10 to x17)
            bins a0              = {5'd10};
            bins a1              = {5'd11};
            bins a2              = {5'd12};
            bins a3              = {5'd13};
            bins a4              = {5'd14};
            bins a5              = {5'd15};
            bins a6              = {5'd16};
            bins a7              = {5'd17};
            // Temporary registers t0 through t6 (x5 to x7, x28 to x31)
            bins t0              = {5'd5};
            bins t1              = {5'd6};
            bins t2              = {5'd7};
            bins t3              = {5'd28};
            bins t4              = {5'd29};
            bins t5              = {5'd30};
            bins t6              = {5'd31};
            // Other GPRs (gp/tp x3-x4, s2-s11 x18-x27)
            ignore_bins other_gprs = {5'd3, 5'd4, [5'd18:5'd27]};
        }

        // Helper coverpoint instr_type_cp for cross coverage:
        // Instruction type (ALU, Branch, Store, Load address) executing during divergence
        instr_type_cp: coverpoint instr_type_cats iff (reg_divergence_active) {
            wildcard bins alu       = {4'b???1};
            wildcard bins branch    = {4'b??1?};
            wildcard bins store     = {4'b?1??};
            wildcard bins load_addr = {4'b1???};
        }

        // 4. Cross Coverage:
        // Cross target_register_divergence_cp with instruction type (ALU, Branch, Store, Load address)
        // executing when the divergence occurred
        target_register_x_instr_type: cross target_register_divergence_cp, instr_type_cp {
            bins ra_alu            = binsof(target_register_divergence_cp.ra)    && binsof(instr_type_cp.alu);
            bins sp_alu            = binsof(target_register_divergence_cp.sp)    && binsof(instr_type_cp.alu);
            bins s0_fp_alu         = binsof(target_register_divergence_cp.s0_fp) && binsof(instr_type_cp.alu);
            bins s1_alu            = binsof(target_register_divergence_cp.s1)    && binsof(instr_type_cp.alu);
            bins a0_alu            = binsof(target_register_divergence_cp.a0)    && binsof(instr_type_cp.alu);
            bins a1_alu            = binsof(target_register_divergence_cp.a1)    && binsof(instr_type_cp.alu);
            bins a2_alu            = binsof(target_register_divergence_cp.a2)    && binsof(instr_type_cp.alu);
            bins a3_alu            = binsof(target_register_divergence_cp.a3)    && binsof(instr_type_cp.alu);
            bins a4_alu            = binsof(target_register_divergence_cp.a4)    && binsof(instr_type_cp.alu);
            bins a5_alu            = binsof(target_register_divergence_cp.a5)    && binsof(instr_type_cp.alu);
            bins a6_alu            = binsof(target_register_divergence_cp.a6)    && binsof(instr_type_cp.alu);
            bins a7_alu            = binsof(target_register_divergence_cp.a7)    && binsof(instr_type_cp.alu);
            bins t0_alu            = binsof(target_register_divergence_cp.t0)    && binsof(instr_type_cp.alu);
            bins t1_alu            = binsof(target_register_divergence_cp.t1)    && binsof(instr_type_cp.alu);
            bins t2_alu            = binsof(target_register_divergence_cp.t2)    && binsof(instr_type_cp.alu);
            bins t3_alu            = binsof(target_register_divergence_cp.t3)    && binsof(instr_type_cp.alu);
            bins t4_alu            = binsof(target_register_divergence_cp.t4)    && binsof(instr_type_cp.alu);
            bins t5_alu            = binsof(target_register_divergence_cp.t5)    && binsof(instr_type_cp.alu);
            bins t6_alu            = binsof(target_register_divergence_cp.t6)    && binsof(instr_type_cp.alu);
            bins reg_div_branch    = binsof(instr_type_cp.branch);
            bins reg_div_store     = binsof(instr_type_cp.store);
            bins reg_div_load_addr = binsof(instr_type_cp.load_addr);
        }
    endgroup

    initial begin
        el2_veer_lockstep_regfile_read_cov el2_veer_lockstep_regfile_read_cov_cg = new();
        $display("Lockstep regfile read comparison coverage interface created");
    end
`else
    // -------------------------------------------------------------------------
    // Functional Coverage for Verilator via SystemVerilog Assertions (`cover property`)
    // -------------------------------------------------------------------------

    // 1. Regfile read enable configuration coverpoints (regfile_read_enable_config_cp)
    cov_full_regfile_mode: cover property (@(posedge clk) disable iff (!rst_n)
        (RegfileReadEnable == 1'b0));
    cov_read_port_mode: cover property (@(posedge clk) disable iff (!rst_n)
        (RegfileReadEnable == 1'b1));

    // 2. Regfile read port difference coverpoints (regfile_read_port_diff_cp)
    cov_rd0_divergence: cover property (@(posedge clk) disable iff (!rst_n)
        rd0_divergence);
    cov_rd1_divergence: cover property (@(posedge clk) disable iff (!rst_n)
        rd1_divergence);

    // 3. Target architectural register divergence coverpoints (target_register_divergence_cp)
    cov_target_reg_zero_x0_no_div: cover property (@(posedge clk) disable iff (!rst_n)
        (shadow_raddr0 == 5'd0) && !rd0_divergence);
    cov_target_reg_ra: cover property (@(posedge clk) disable iff (!rst_n)
        reg_divergence_active && (target_reg_div == 5'd1));
    cov_target_reg_sp: cover property (@(posedge clk) disable iff (!rst_n)
        reg_divergence_active && (target_reg_div == 5'd2));
    cov_target_reg_s0_fp: cover property (@(posedge clk) disable iff (!rst_n)
        reg_divergence_active && (target_reg_div == 5'd8));
    cov_target_reg_s1: cover property (@(posedge clk) disable iff (!rst_n)
        reg_divergence_active && (target_reg_div == 5'd9));
    cov_target_reg_a0: cover property (@(posedge clk) disable iff (!rst_n)
        reg_divergence_active && (target_reg_div == 5'd10));
    cov_target_reg_a1: cover property (@(posedge clk) disable iff (!rst_n)
        reg_divergence_active && (target_reg_div == 5'd11));
    cov_target_reg_a2: cover property (@(posedge clk) disable iff (!rst_n)
        reg_divergence_active && (target_reg_div == 5'd12));
    cov_target_reg_a3: cover property (@(posedge clk) disable iff (!rst_n)
        reg_divergence_active && (target_reg_div == 5'd13));
    cov_target_reg_a4: cover property (@(posedge clk) disable iff (!rst_n)
        reg_divergence_active && (target_reg_div == 5'd14));
    cov_target_reg_a5: cover property (@(posedge clk) disable iff (!rst_n)
        reg_divergence_active && (target_reg_div == 5'd15));
    cov_target_reg_a6: cover property (@(posedge clk) disable iff (!rst_n)
        reg_divergence_active && (target_reg_div == 5'd16));
    cov_target_reg_a7: cover property (@(posedge clk) disable iff (!rst_n)
        reg_divergence_active && (target_reg_div == 5'd17));
    cov_target_reg_t0: cover property (@(posedge clk) disable iff (!rst_n)
        reg_divergence_active && (target_reg_div == 5'd5));
    cov_target_reg_t1: cover property (@(posedge clk) disable iff (!rst_n)
        reg_divergence_active && (target_reg_div == 5'd6));
    cov_target_reg_t2: cover property (@(posedge clk) disable iff (!rst_n)
        reg_divergence_active && (target_reg_div == 5'd7));
    cov_target_reg_t3: cover property (@(posedge clk) disable iff (!rst_n)
        reg_divergence_active && (target_reg_div == 5'd28));
    cov_target_reg_t4: cover property (@(posedge clk) disable iff (!rst_n)
        reg_divergence_active && (target_reg_div == 5'd29));
    cov_target_reg_t5: cover property (@(posedge clk) disable iff (!rst_n)
        reg_divergence_active && (target_reg_div == 5'd30));
    cov_target_reg_t6: cover property (@(posedge clk) disable iff (!rst_n)
        reg_divergence_active && (target_reg_div == 5'd31));

    // 4. Cross Coverage: target_register_x_instr_type
    cov_cross_reg_div_x_alu: cover property (@(posedge clk) disable iff (!rst_n)
        reg_divergence_active && is_alu_instr);
    cov_cross_reg_div_x_branch: cover property (@(posedge clk) disable iff (!rst_n)
        reg_divergence_active && is_branch_instr);
    cov_cross_reg_div_x_store: cover property (@(posedge clk) disable iff (!rst_n)
        reg_divergence_active && is_store_instr);
    cov_cross_reg_div_x_load_addr: cover property (@(posedge clk) disable iff (!rst_n)
        reg_divergence_active && is_load_instr);

    initial begin
        $display("Lockstep regfile read comparison coverage interface created (Verilator SVA mode)");
    end
`endif

endinterface
