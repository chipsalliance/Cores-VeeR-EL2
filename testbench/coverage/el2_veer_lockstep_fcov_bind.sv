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

`include "common_defines.vh"

module el2_veer_lockstep_fcov_bind #(
`ifdef FCOV
  `include "el2_param.vh"
`endif
) ();
`ifdef FCOV
  bind el2_ifu_mem_ctl el2_ifu_icache_ecc_recovery_cov_if #(
    .pt(pt)
  ) el2_ifu_icache_ecc_recovery_cov_inst (
      .*
    );
  bind el2_lsu_dccm_ctl el2_lsu_dccm_wr_readback_cov_if #(
    .pt(pt)
  ) el2_lsu_dccm_wr_readback_cov_inst (
      .*
    );
  bind el2_dec_tlu_ctl el2_core_ecc_threshold_cov_if #(
    .pt(pt)
  ) el2_core_ecc_threshold_cov_inst (
      .*
    );
`ifdef RV_LOCKSTEP_ENABLE
  bind el2_veer_lockstep el2_veer_lockstep_delay_cov_if #(
    .pt(pt)
  ) el2_veer_lockstep_delay_cov_inst (
      .*
    );
  bind el2_veer_lockstep el2_veer_lockstep_debug_mode_cov_if #(
    .pt(pt)
  ) el2_veer_lockstep_debug_mode_cov_inst (
      .*
    );
  bind el2_veer_lockstep el2_veer_lockstep_mubi_sweep_cov_if #(
    .pt(pt)
  ) el2_veer_lockstep_mubi_sweep_cov_inst (
      .*
    );
  bind el2_veer_wrapper el2_veer_lockstep_address_xor_infection_cov_if #(
    .pt(pt)
  ) el2_veer_lockstep_address_xor_infection_cov_inst (
      .rst_n                    (lockstep.rst_n),
`ifdef RV_ICCM_ENABLE
      .main_iccm_rd_data        (veer.ifu.mem_ctl.iccm_rd_data),
      .shadow_iccm_rd_data      (lockstep.xshadow_core.ifu.mem_ctl.iccm_rd_data),
      .iccm_sel_red0            (mem.iccm.iccm.sel_red0),
      .iccm_sel_red1            (mem.iccm.iccm.sel_red1),
      .iccm_red_addr0_odd       (mem.iccm.iccm.redundant_address[0][2]),
      .iccm_red_addr1_odd       (mem.iccm.iccm.redundant_address[1][2]),
`else
      .main_iccm_rd_data        ('0),
      .shadow_iccm_rd_data      ('0),
      .iccm_sel_red0            ('0),
      .iccm_sel_red1            ('0),
      .iccm_red_addr0_odd       (1'b0),
      .iccm_red_addr1_odd       (1'b0),
`endif
      .shadow_ic_perr_r         (lockstep.xshadow_core.dec.tlu.ic_perr_r),
      .shadow_core_inputs_pre   (lockstep.shadow_core_inputs_pre),
      .delayed_main_core_outputs(lockstep.delayed_main_core_outputs),
      .shadow_core_outputs      (lockstep.shadow_core_outputs),
      .*
    );
  bind el2_veer_lockstep el2_veer_lockstep_regfile_read_cov_if #(
    .pt(pt)
  ) el2_veer_lockstep_regfile_read_cov_inst (
`ifdef RV_LOCKSTEP_REGFILE_ENABLE
`ifdef RV_LOCKSTEP_REGFILE_READ_ENABLE
      .main_gpr_rd0              (main_core_regfile.gpr.rd0),
      .main_gpr_rd1              (main_core_regfile.gpr.rd1),
      .shadow_gpr_rd0            (shadow_core_regfile.gpr.rd0),
      .shadow_gpr_rd1            (shadow_core_regfile.gpr.rd1),
`else
      .main_gpr_pkt              (main_core_regfile.gpr),
      .shadow_gpr_pkt            (shadow_core_regfile.gpr),
`endif
`endif
      .shadow_raddr0             (xshadow_core.dec.dec_i0_rs1_d),
      .shadow_raddr1             (xshadow_core.dec.dec_i0_rs2_d),
      .shadow_dec_i0_decode_d    (xshadow_core.dec.dec_i0_decode_d),
      .shadow_dec_i0_alu_decode_d(xshadow_core.dec.dec_i0_alu_decode_d),
      .shadow_dec_i0_branch_d    (xshadow_core.dec.dec_i0_branch_d),
      .shadow_dec_i0_instr_d     (xshadow_core.dec.dec_i0_instr_d),
      .shadow_lsu_p              (xshadow_core.dec.lsu_p),
      .*
    );
  bind el2_veer_wrapper el2_veer_lockstep_asymmetric_fault_cov_if #(
    .pt(pt)
  ) el2_veer_lockstep_asymmetric_fault_cov_inst (
      .clk                  (clk),
      .rst_n                (lockstep.rst_n),
`ifdef RV_LOCKSTEP_REGFILE_ENABLE
      .regfile_corrupted    (lockstep.regfile_corrupted),
`endif
      .outputs_corrupted    (lockstep.outputs_corrupted),
      .corruption_detected_o(corruption_detected_o),
      .extintsrc_req        (extintsrc_req),
      .main_mdccme_ce_req   (veer.dec.tlu.mdccme_ce_req),
      .main_miccme_ce_req   (veer.dec.tlu.miccme_ce_req),
      .main_mice_ce_req     (veer.dec.tlu.mice_ce_req),
      .shadow_mdccme_ce_req (lockstep.xshadow_core.dec.tlu.mdccme_ce_req),
      .shadow_miccme_ce_req (lockstep.xshadow_core.dec.tlu.miccme_ce_req),
      .shadow_mice_ce_req   (lockstep.xshadow_core.dec.tlu.mice_ce_req)
    );
  bind el2_veer_wrapper el2_veer_lockstep_internal_state_tamper_cov_if #(
    .pt(pt)
  ) el2_veer_lockstep_internal_state_tamper_cov_inst (
      .clk                  (clk),
      .rst_l                (rst_l),
      .dbg_rst_l            (dbg_rst_l),
      .rst_n                (lockstep.rst_n),
      .main_gpr_a5          (veer.dec.arf.gpr_out[15]),
      .main_q0pc            (veer.ifu.aln.q0pc),
      .main_mtvec           (veer.dec.tlu.mtvec),
      .shadow_gpr_a5        (lockstep.xshadow_core.dec.arf.gpr_out[15]),
      .shadow_q0pc          (lockstep.xshadow_core.ifu.aln.q0pc),
      .shadow_mtvec         (lockstep.xshadow_core.dec.tlu.mtvec),
      .corruption_detected_o(corruption_detected_o),
      .extintsrc_req        (extintsrc_req)
    );
`endif
`endif

endmodule : el2_veer_lockstep_fcov_bind
