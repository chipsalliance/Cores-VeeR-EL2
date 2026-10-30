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
  bind el2_veer_lockstep el2_veer_lockstep_address_xor_infection_cov_if #(
    .pt(pt)
  ) el2_veer_lockstep_address_xor_infection_cov_inst (
      .shadow_ic_perr_r(xshadow_core.dec.tlu.ic_perr_r),
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
`endif
`endif

endmodule : el2_veer_lockstep_fcov_bind
