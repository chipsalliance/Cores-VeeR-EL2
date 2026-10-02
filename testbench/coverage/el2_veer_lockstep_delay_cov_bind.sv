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

module el2_veer_lockstep_delay_cov_bind
#(
`ifdef FCOV
    `include "el2_param.vh"
`endif
) ();
`ifdef FCOV
    bind el2_veer_lockstep el2_veer_lockstep_delay_cov_if el2_veer_lockstep_delay_cov_inst(
         .*
    );
`endif

// Prevent Verilator from elaborating the VCS-only bind in
// verification/block/dcls/el2_veer_lockstep_cov_bind.sv (compiled next in testbench/flist).
`ifdef VERILATOR
    `undef FCOV
`endif

endmodule
