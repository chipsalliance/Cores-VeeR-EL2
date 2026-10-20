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
`endif
`endif

endmodule : el2_veer_lockstep_fcov_bind
