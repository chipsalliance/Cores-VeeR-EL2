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

module el2_veer_lockstep_fcov_bind
#(
`ifdef FCOV
    `include "el2_param.vh"
`endif
) ();
`ifdef FCOV
    bind el2_veer_lockstep el2_veer_lockstep_delay_cov_if el2_veer_lockstep_delay_cov_inst(
         .*
    );
    bind el2_ifu_mem_ctl el2_ifu_icache_ecc_recovery_cov_if el2_ifu_icache_ecc_recovery_cov_inst(
         .*
    );
    bind el2_lsu_dccm_ctl el2_lsu_dccm_wr_readback_cov_if el2_lsu_dccm_wr_readback_cov_inst(
         .*
    );
    bind el2_dec_tlu_ctl el2_core_ecc_threshold_cov_if #(
         .pt(pt)
    ) el2_core_ecc_threshold_cov_inst(
         .*
    );
    bind el2_veer_lockstep el2_veer_lockstep_asymmetric_fault_cov_if #(
         .pt(pt)
    ) el2_veer_lockstep_asymmetric_fault_cov_inst(
         .*,
         .shadow_mdccme_ce_req(xshadow_core.dec.tlu.mdccme_ce_req),
         .shadow_miccme_ce_req(xshadow_core.dec.tlu.miccme_ce_req),
         .shadow_mice_ce_req  (xshadow_core.dec.tlu.mice_ce_req)
    );
`endif

// Prevent Verilator from elaborating the VCS-only bind in
// verification/block/dcls/el2_veer_lockstep_cov_bind.sv (compiled next in testbench/flist).
`ifdef VERILATOR
    `undef FCOV
`endif

endmodule
