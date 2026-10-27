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

module el2_veer_lockstep_fcov_bind
  import el2_pkg::*;
#(
`ifdef FCOV
    `include "el2_param.vh"
`endif
) ();
`ifdef FCOV
    bind el2_ifu_mem_ctl el2_ifu_icache_ecc_recovery_cov_if #(
         .pt(pt)
    ) el2_ifu_icache_ecc_recovery_cov_inst(
         .*
    );
    bind el2_lsu_dccm_ctl el2_lsu_dccm_wr_readback_cov_if #(
         .pt(pt)
    ) el2_lsu_dccm_wr_readback_cov_inst(
         .*
    );
    bind el2_dec_tlu_ctl el2_core_ecc_threshold_cov_if #(
         .pt(pt)
    ) el2_core_ecc_threshold_cov_inst(
         .*
    );
`ifdef RV_LOCKSTEP_ENABLE
    bind el2_veer_lockstep el2_veer_lockstep_delay_cov_if #(
         .pt(pt)
    ) el2_veer_lockstep_delay_cov_inst(
         .*
    );
    bind el2_veer_wrapper el2_veer_lockstep_asymmetric_fault_cov_if #(
         .pt(pt)
    ) el2_veer_lockstep_asymmetric_fault_cov_inst(
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
`endif
`endif

endmodule
