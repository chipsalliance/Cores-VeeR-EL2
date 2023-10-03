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
    input logic scan_mode, // Scan mode

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
  function automatic logic perm_check_wrapper(el2_pmp_cfg_pkt_t csr_pmp_cfg,
                                              logic permission_check);
    return orig_perm_check(csr_pmp_cfg.lock, permission_check);
  endfunction

  // Compute permissions checks that apply when MSECCFG.MML is unset. This is the original PMP
  // behaviour before Smepmp was added.
  function automatic logic orig_perm_check(logic pmp_cfg_lock, logic permission_check);
    return (~pmp_cfg_lock | permission_check);
    // For M-mode, any region which matches with the L-bit clear, or with sufficient
    // access permissions will be allowed
  endfunction

  // Access fault determination / prioritization
  function automatic logic access_fault_check(logic [pt.PMP_ENTRIES-1:0] match_all,
                                              logic [pt.PMP_ENTRIES-1:0] final_perm_check);


    // When MSECCFG.MMWP is set default deny always, otherwise allow for M-mode, deny for other
    // modes. Also deny unmatched for M-mode whe MSECCFG.MML is set and request type is EXEC.
    logic access_fail = 1'b0;
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
          pmp_pmpcfg[r], region_basic_perm_check[c][r]
      );

      // Address bits below PMP granularity (which starts at 4 byte) are deliberately unused.
      logic unused_sigs;
      assign unused_sigs = ^{region_start_addr[r][PMP_GRANULARITY+2-1:0],
                             pmp_req_addr_i[c][PMP_GRANULARITY+2-1:0]};
    end

    // Once the permission checks of the regions are done, decide if the access is
    // denied by figuring out the matching region and its permission check.
    assign pmp_chan_err[c] = access_fault_check(region_match_all[c], region_perm_check[c]);
  end

endmodule  // el2_pmp
