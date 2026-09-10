// SPDX-License-Identifier: Apache-2.0
// Copyright lowRISC contributors.
// Copyright 2023 Antmicro, Ltd. <www.antmicro.com>
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

module el2_pmp
  import el2_pkg::*;
#(
    parameter PMP_CHANNELS = 3,
    // Granularity of NAPOT access,
    // 0 = No restriction, 1 = 8 byte, 2 = 16 byte, 3 = 32 byte, etc.
    parameter PMP_GRANULARITY = 0,  // TODO: Move to veer.config
    `include "el2_param.vh"
) (
    input logic clk,       // Top level clock
    input logic rst_l,     // Reset
    /* pragma coverage off */
    input logic scan_mode, // Scan mode
    /* pragma coverage on */

`ifdef RV_SMEPMP
    input el2_mseccfg_pkt_t mseccfg, // mseccfg CSR content, RLB, MMWP and MML bits
`endif

`ifdef RV_USER_MODE
    input logic priv_mode_ns,   // operating privilege mode (next clock cycle)
    input logic priv_mode_eff,  // operating effective privilege mode
`endif

    input el2_pmp_cfg_pkt_t        pmp_pmpcfg [pt.PMP_ENTRIES],
    input logic             [31:0] pmp_pmpaddr[pt.PMP_ENTRIES],

    input  logic              [31:0] pmp_chan_addr[PMP_CHANNELS],
    input  el2_pmp_type_pkt_t        pmp_chan_type[PMP_CHANNELS],
    output logic                     pmp_chan_err [PMP_CHANNELS]
);

  logic [                33:0]                     csr_pmp_addr_i          [pt.PMP_ENTRIES];
  logic [                33:0]                     pmp_req_addr_i          [  PMP_CHANNELS];

  logic [                33:0]                     region_start_addr       [pt.PMP_ENTRIES];
  logic [33:PMP_GRANULARITY+2]                     region_addr_mask        [pt.PMP_ENTRIES];
  logic [    PMP_CHANNELS-1:0][pt.PMP_ENTRIES-1:0] region_match_gt;
  logic [    PMP_CHANNELS-1:0][pt.PMP_ENTRIES-1:0] region_match_lt;
  logic [    PMP_CHANNELS-1:0][pt.PMP_ENTRIES-1:0] region_match_eq;
  logic [    PMP_CHANNELS-1:0][pt.PMP_ENTRIES-1:0] region_match_all;
  logic [    PMP_CHANNELS-1:0][pt.PMP_ENTRIES-1:0] region_basic_perm_check;
  logic [    PMP_CHANNELS-1:0][pt.PMP_ENTRIES-1:0] region_perm_check;

`ifdef RV_USER_MODE
  logic any_region_enabled;
`endif

  ///////////////////////
  // Functions for PMP //
  ///////////////////////

  // Flow of the PMP checking operation follows as below
  //
  // basic_perm_check ---> perm_check_wrapper ---> orig_perm_check ---/
  //                                                                  |
  // region_match_all -----------------> access_fault_check <----------
  //                                             |
  //                                             \--> pmp_chan_err

  // A wrapper function in which it is decided which form of permission check function gets called
  function automatic logic perm_check_wrapper(el2_mseccfg_pkt_t csr_pmp_mseccfg,
                                              el2_pmp_cfg_pkt_t csr_pmp_cfg,
                                              el2_pmp_type_pkt_t req_type,
                                              logic priv_mode,
                                              logic permission_check);

    return csr_pmp_mseccfg.MML ? mml_perm_check(csr_pmp_cfg,
                                                req_type,
                                                priv_mode,
                                                permission_check) :
                                 orig_perm_check(csr_pmp_cfg.lock,
                                                 priv_mode,
                                                 permission_check);
  endfunction

  // Compute permissions checks that apply when MSECCFG.MML is set. Added for Smepmp support.
  function automatic logic mml_perm_check(el2_pmp_cfg_pkt_t   csr_pmp_cfg,
                                          el2_pmp_type_pkt_t  pmp_req_type,
                                          logic               priv_mode,
                                          logic               permission_check);
    logic result;
    logic unused_cfg = |csr_pmp_cfg.mode;

    if (!csr_pmp_cfg.read && csr_pmp_cfg.write) begin
      // Special-case shared regions where R = 0, W = 1
      unique case ({csr_pmp_cfg.lock, csr_pmp_cfg.execute})
        // Read/write in M, read only in U
        2'b00: result =
             (pmp_req_type == READ) |
            ((pmp_req_type == WRITE) & ~priv_mode);
        // Read/write in M/U
        2'b01: result =
             (pmp_req_type == READ) |
             (pmp_req_type == WRITE);
        // Execute only on M/U
        2'b10: result = (pmp_req_type == EXEC);
        // Read/execute in M, execute only on U
        2'b11: result =
             (pmp_req_type == EXEC) |
            ((pmp_req_type == READ) & ~priv_mode);
        /* pragma coverage off */
        default: ;
        /* pragma coverage on */
      endcase
    end else begin
      if (csr_pmp_cfg.read & csr_pmp_cfg.write & csr_pmp_cfg.execute & csr_pmp_cfg.lock) begin
        // Special-case shared read only region when R = 1, W = 1, X = 1, L = 1
        result = (pmp_req_type == READ);
      end else begin
        // Otherwise use basic permission check. Permission is always denied if in U mode and
        // L is set or if in M mode and L is unset.
        result = permission_check & (priv_mode ? ~csr_pmp_cfg.lock : csr_pmp_cfg.lock);
      end
    end
    return result;
  endfunction

  // Compute permissions checks that apply when MSECCFG.MML is unset. This is the original PMP
  // behaviour before Smepmp was added.
  function automatic logic orig_perm_check(logic pmp_cfg_lock,
                                           logic priv_mode,
                                           logic permission_check);
    // For M-mode, any region which matches with the L-bit clear, or with sufficient
    // access permissions will be allowed.
    // For other modes, the lock bit doesn't matter
    return priv_mode ? (permission_check) : (~pmp_cfg_lock | permission_check);
  endfunction

  // Access fault determination / prioritization
  function automatic logic access_fault_check(el2_mseccfg_pkt_t          csr_pmp_mseccfg,
                                              el2_pmp_type_pkt_t         req_type,
                                              logic [pt.PMP_ENTRIES-1:0] match_all,
                                              logic any_region_enabled,
                                              logic priv_mode,
                                              logic [pt.PMP_ENTRIES-1:0] final_perm_check);

`ifdef RV_USER_MODE
  `ifdef RV_SMEPMP
    // When MSECCFG.MMWP is set default deny always, otherwise allow for M-mode, deny for other
    // modes. Also deny unmatched for M-mode when MSECCFG.MML is set and request type is EXEC.
    logic access_fail = csr_pmp_mseccfg.MMWP | priv_mode |
                       (csr_pmp_mseccfg.MML && (req_type == EXEC));
  `else
    // When in user mode and at least one PMP region is enabled deny access by default.
    logic access_fail = any_region_enabled & priv_mode;
  `endif
`else
    logic access_fail = 1'b0;
`endif

    logic matched = 1'b0;

    // PMP entries are statically prioritized, from 0 to N-1
    // The lowest-numbered PMP entry which matches an address determines accessibility
    for (int r = 0; r < pt.PMP_ENTRIES; r++) begin
      if (!matched && match_all[r]) begin
        access_fail = ~final_perm_check[r];
        matched = 1'b1;
      end
    end
    return access_fail;
  endfunction

  // ---------------
  // Access checking
  // ---------------

`ifdef RV_USER_MODE
  logic [pt.PMP_ENTRIES-1:0] region_enabled;
  for (genvar r = 0; r < pt.PMP_ENTRIES; r++) begin : g_reg_ena
    assign region_enabled[r] = pmp_pmpcfg[r].mode != OFF;
  end
  assign any_region_enabled = |region_enabled;
`endif

  for (genvar r = 0; r < pt.PMP_ENTRIES; r++) begin : g_addr_exp
    assign csr_pmp_addr_i[r] = {
      pmp_pmpaddr[r], 2'b00
    };  // addr conv.: word @ 32-bit -> byte @ 34-bit
    // Start address for TOR matching
    if (r == 0) begin : g_entry0
      assign region_start_addr[r] = (pmp_pmpcfg[r].mode == TOR) ? 34'h000000000 : csr_pmp_addr_i[r];
    end else begin : g_oth
      assign region_start_addr[r] = (pmp_pmpcfg[r].mode == TOR) ? csr_pmp_addr_i[r-1] :
                                                                  csr_pmp_addr_i[r];
    end
    // Address mask for NA matching
    for (genvar b = PMP_GRANULARITY + 2; b < 34; b++) begin : g_bitmask
      if (b == 2) begin : g_bit0
        // Always mask bit 2 for NAPOT
        assign region_addr_mask[r][b] = (pmp_pmpcfg[r].mode != NAPOT);
      end else begin : g_others
        // We will mask this bit if it is within the programmed granule
        // i.e. addr = yyyy 0111
        //                  ^
        //                  | This bit pos is the top of the mask, all lower bits set
        // thus mask = 1111 0000
        if (PMP_GRANULARITY == 0) begin : g_region_addr_mask_zero_granularity
          assign region_addr_mask[r][b] = (pmp_pmpcfg[r].mode != NAPOT) |
                                          ~&csr_pmp_addr_i[r][b-1:2];
        end else begin : g_region_addr_mask_other_granularity
          assign region_addr_mask[r][b] = (pmp_pmpcfg[r].mode != NAPOT) |
                                          ~&csr_pmp_addr_i[r][b-1:PMP_GRANULARITY+1];
        end
      end
    end
  end

`ifdef RV_USER_MODE
  logic [PMP_CHANNELS-1:0] pmp_priv_mode_eff;
  for (genvar c = 0; c < PMP_CHANNELS; c++) begin : g_priv_mode_eff
    assign pmp_priv_mode_eff[c] = (
      ((pmp_chan_type[c] == EXEC) & priv_mode_ns) |
      ((pmp_chan_type[c] != EXEC) & priv_mode_eff)); // RW affected by mstatus.MPRV
  end
`endif

  for (genvar c = 0; c < PMP_CHANNELS; c++) begin : g_access_check
    assign pmp_req_addr_i[c] = {2'b00, pmp_chan_addr[c]};  // addr. widening: 32-bit -> 34-bit
    for (genvar r = 0; r < pt.PMP_ENTRIES; r++) begin : g_regions
      // Comparators are sized according to granularity
      assign region_match_eq[c][r] = (pmp_req_addr_i[c][33:PMP_GRANULARITY+2] &
                                      region_addr_mask[r]) ==
                                     (region_start_addr[r][33:PMP_GRANULARITY+2] &
                                      region_addr_mask[r]);
      assign region_match_gt[c][r] = pmp_req_addr_i[c][33:PMP_GRANULARITY+2] >
                                     region_start_addr[r][33:PMP_GRANULARITY+2];
      assign region_match_lt[c][r] = pmp_req_addr_i[c][33:PMP_GRANULARITY+2] <
                                     csr_pmp_addr_i[r][33:PMP_GRANULARITY+2];

      always_comb begin
        region_match_all[c][r] = 1'b0;
        unique case (pmp_pmpcfg[r].mode)
          OFF:     region_match_all[c][r] = 1'b0;
          NA4:     region_match_all[c][r] = region_match_eq[c][r];
          NAPOT:   region_match_all[c][r] = region_match_eq[c][r];
          TOR: begin
            region_match_all[c][r] = (region_match_eq[c][r] | region_match_gt[c][r]) &
                                     region_match_lt[c][r];
          end
          default: region_match_all[c][r] = 1'b0;
        endcase
      end

      // Basic permission check compares cfg register only.
      assign region_basic_perm_check[c][r] =
          ((pmp_chan_type[c] == EXEC)  & pmp_pmpcfg[r].execute) |
          ((pmp_chan_type[c] == WRITE) & pmp_pmpcfg[r].write) |
          ((pmp_chan_type[c] == READ)  & pmp_pmpcfg[r].read);

      // Check specific required permissions since the behaviour is different
      // between Smepmp implementation and original PMP.
      assign region_perm_check[c][r] = perm_check_wrapper(
`ifdef RV_SMEPMP
          mseccfg,
`else
          3'b000,
`endif
          pmp_pmpcfg[r],
          pmp_chan_type[c],
`ifdef RV_USER_MODE
          pmp_priv_mode_eff[c],
`else
          1'b0,
`endif
          region_basic_perm_check[c][r]
      );

      // Address bits below PMP granularity (which starts at 4 byte) are deliberately unused.
      logic unused_sigs;
      assign unused_sigs = ^{region_start_addr[r][PMP_GRANULARITY+2-1:0],
                             pmp_req_addr_i[c][PMP_GRANULARITY+2-1:0]};
    end

    // Once the permission checks of the regions are done, decide if the access is
    // denied by figuring out the matching region and its permission check.
    assign pmp_chan_err[c] = access_fault_check(
`ifdef RV_SMEPMP
        mseccfg,
`else
        3'b000,
`endif
        pmp_chan_type[c],
        region_match_all[c],
`ifdef RV_USER_MODE
        any_region_enabled,
        pmp_priv_mode_eff[c],
`else
        1'b0,
        1'b0,
`endif
        region_perm_check[c]);

  end

endmodule  // el2_pmp
