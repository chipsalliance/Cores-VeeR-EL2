// SPDX-License-Identifier: Apache-2.0
// Copyright 2023 Antmicro <www.antmicro.com>
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


//********************************************************************************
// el2_dec_pmp_ctl.sv
//
//
// Function: Physical Memory Protection CSRs
// Comments:
//
//********************************************************************************

module el2_dec_pmp_ctl
  import el2_pkg::*;
#(
`include "el2_param.vh"
 )
  (
   input logic clk,
   input logic free_l2clk,
   input logic csr_wr_clk,
   input logic rst_l,
   input logic        dec_csr_wen_r_mod,  // csr write enable at wb
   input logic [11:0] dec_csr_wraddr_r,   // write address for csr
   input logic [31:0] dec_csr_wrdata_r,   // csr write data at wb
   input logic [11:0] dec_csr_rdaddr_d,   // read address for csr

   input logic csr_pmpcfg,
   input logic csr_pmpaddr0,
   input logic csr_pmpaddr16,
   input logic csr_pmpaddr32,
   input logic csr_pmpaddr48,

   input logic dec_pause_state, // Paused
   input logic dec_tlu_pmu_fw_halted, // pmu/fw halted
   input logic internal_dbg_halt_timers, // debug halted

`ifdef RV_SMEPMP
   input el2_mseccfg_pkt_t mseccfg,
`endif

   output logic [31:0] dec_pmp_rddata_d,  // pmp CSR read data
   output logic        dec_pmp_read_d,    // pmp CSR address match

   output el2_pmp_cfg_pkt_t pmp_pmpcfg  [pt.PMP_ENTRIES],
   output logic [31:0]      pmp_pmpaddr [pt.PMP_ENTRIES],

   // Excluding scan_mode from coverage as its usage is determined by the integrator of the VeeR core.
   /*pragma coverage off*/
   input  logic        scan_mode
   /*pragma coverage on*/
   );

   logic wr_pmpcfg_r;
   logic [3:0] wr_pmpcfg_group;

   logic wr_pmpaddr0_sel;
   logic wr_pmpaddr16_sel;
   logic wr_pmpaddr32_sel;
   logic wr_pmpaddr48_sel;
   logic wr_pmpaddr_r;
   logic [1:0] wr_pmpaddr_quarter;
   logic [5:0] wr_pmpaddr_address;

   logic [3:0] pmp_quarter_rdaddr;
   logic [31:0] pmp_pmpcfg_rddata;

   // ----------------------------------------------------------------------

   logic [pt.PMP_ENTRIES-1:0] entry_lock_eff;  // Effective entry lock
   for (genvar r = 0; r < pt.PMP_ENTRIES; r++) begin : g_pmpcfg_lock
`ifdef RV_SMEPMP
   // Smepmp allow modifying locked entries when mseccfg.RLB is set
   assign entry_lock_eff[r] = pmp_pmpcfg[r].lock & ~mseccfg.RLB;
`else
   assign entry_lock_eff[r] = pmp_pmpcfg[r].lock;
`endif
   end

   // ----------------------------------------------------------------------
   // PMPCFGx (RW)
   // [31:24] : PMP entry (x*4 + 3) configuration
   // [23:16] : PMP entry (x*4 + 2) configuration
   // [15:8] : PMP entry (x*4 + 1) configuration
   //  [7:0] : PMP entry (x*4 + 0) configuration

   localparam PMPCFG       = 12'h3a0;
   localparam PMP_ENTRIES_WIDTH = $clog2(pt.PMP_ENTRIES);

   assign wr_pmpcfg_r = dec_csr_wen_r_mod & (dec_csr_wraddr_r[11:4] == PMPCFG[11:4]);
   assign wr_pmpcfg_group = dec_csr_wraddr_r[3:0]; // selects group of 4 pmpcfg entries (group 1 -> entries 4-7; up to 16 groups)

   for (genvar entry_idx = 0; entry_idx < pt.PMP_ENTRIES; entry_idx++) begin : gen_pmpcfg_ff
      logic [7:0] raw_wdata;
      logic [7:0] csr_wdata;

      // PMPCFG fields are WARL. Mask out bits 6:5 during write.
      // When Smepmp is disabled R=0 and W=1 combination is illegal mask out W
      // when R is cleared.
      assign raw_wdata = dec_csr_wrdata_r[(entry_idx[1:0]*8)+7:(entry_idx[1:0]*8)+0];
`ifdef RV_SMEPMP
      assign csr_wdata = raw_wdata & 8'b10011111;
`else
      assign csr_wdata = raw_wdata[0] ? (raw_wdata & 8'b10011111) : (raw_wdata & 8'b10011101);
`endif

      rvdffe #(8) pmpcfg_ff (.*, .clk(free_l2clk),
                          .en(wr_pmpcfg_r & (wr_pmpcfg_group == entry_idx[5:2]) & (~entry_lock_eff[entry_idx])),
                          .din(csr_wdata),
                          .dout(pmp_pmpcfg[entry_idx]));
   end

   // ----------------------------------------------------------------------
   // PMPADDRx (RW)
   // [31:0] : PMP entry (x) address selector (word addressing)
   //
   // NOTE: VeeR-EL2 uses 32-bit physical addressing, register bits 31:30 mapping
   //       to bits 33:32 of the physical address are always set to 0. (WARL)

   localparam  PMPADDR0      = 12'h3b0;
   localparam PMPADDR16      = 12'h3c0;
   localparam PMPADDR32      = 12'h3d0;
   localparam PMPADDR48      = 12'h3e0;

   assign wr_pmpaddr0_sel  = dec_csr_wraddr_r[11:4] ==  PMPADDR0[11:4];
   assign wr_pmpaddr16_sel = dec_csr_wraddr_r[11:4] == PMPADDR16[11:4];
   assign wr_pmpaddr32_sel = dec_csr_wraddr_r[11:4] == PMPADDR32[11:4];
   assign wr_pmpaddr48_sel = dec_csr_wraddr_r[11:4] == PMPADDR48[11:4];
   assign wr_pmpaddr_r = dec_csr_wen_r_mod & (wr_pmpaddr0_sel | wr_pmpaddr16_sel | wr_pmpaddr32_sel | wr_pmpaddr48_sel);

   assign wr_pmpaddr_quarter[0] = wr_pmpaddr16_sel | wr_pmpaddr48_sel;
   assign wr_pmpaddr_quarter[1] = wr_pmpaddr32_sel | wr_pmpaddr48_sel;
   assign wr_pmpaddr_address = {wr_pmpaddr_quarter, dec_csr_wraddr_r[3:0]}; // entry address

   for (genvar entry_idx = 0; entry_idx < pt.PMP_ENTRIES; entry_idx++) begin : gen_pmpaddr_ff
      logic pmpaddr_lock;
      logic pmpaddr_lock_next;
      if (entry_idx+1 < pt.PMP_ENTRIES)
         assign pmpaddr_lock_next = entry_lock_eff[entry_idx+1] & pmp_pmpcfg[entry_idx+1].mode == TOR;
      else
         assign pmpaddr_lock_next = 1'b0;
      assign pmpaddr_lock = entry_lock_eff[entry_idx] | pmpaddr_lock_next;
      assign pmp_pmpaddr[entry_idx][31:30] = 2'b00;
      rvdffe #(30) pmpaddr_ff (.*, .clk(free_l2clk),
                          .en(wr_pmpaddr_r & (wr_pmpaddr_address == entry_idx)
                              & (~pmpaddr_lock)),
                          .din(dec_csr_wrdata_r[29:0]),
                          .dout(pmp_pmpaddr[entry_idx][29:0]));
   end

   // CSR read mux
   logic [5:0] pmp_pmpcfg_rdata_selector [4];
   logic [5:0] dec_pmp_rdata_selector [4];

   assign pmp_quarter_rdaddr     = dec_csr_rdaddr_d[3:0];
   for (genvar i = 0; i < 4; i++) begin: gen_csr_selector
      assign pmp_pmpcfg_rdata_selector[i] = {pmp_quarter_rdaddr, 2'(i)};
      assign dec_pmp_rdata_selector[i] = {2'(i), pmp_quarter_rdaddr};
   end

   assign pmp_pmpcfg_rddata      = { pmp_pmpcfg[pmp_pmpcfg_rdata_selector[3][PMP_ENTRIES_WIDTH-1:0]],
                                     pmp_pmpcfg[pmp_pmpcfg_rdata_selector[2][PMP_ENTRIES_WIDTH-1:0]],
                                     pmp_pmpcfg[pmp_pmpcfg_rdata_selector[1][PMP_ENTRIES_WIDTH-1:0]],
                                     pmp_pmpcfg[pmp_pmpcfg_rdata_selector[0][PMP_ENTRIES_WIDTH-1:0]]
                                   };
   assign dec_pmp_read_d         = csr_pmpcfg | csr_pmpaddr0 | csr_pmpaddr16 | csr_pmpaddr32 | csr_pmpaddr48;
   assign dec_pmp_rddata_d[31:0] = ( ({32{csr_pmpcfg}}    & pmp_pmpcfg_rddata) |
                                     ({32{csr_pmpaddr0}}  & pmp_pmpaddr[dec_pmp_rdata_selector[0][PMP_ENTRIES_WIDTH-1:0]]) |
                                     ({32{csr_pmpaddr16}} & pmp_pmpaddr[dec_pmp_rdata_selector[1][PMP_ENTRIES_WIDTH-1:0]]) |
                                     ({32{csr_pmpaddr32}} & pmp_pmpaddr[dec_pmp_rdata_selector[2][PMP_ENTRIES_WIDTH-1:0]]) |
                                     ({32{csr_pmpaddr48}} & pmp_pmpaddr[dec_pmp_rdata_selector[3][PMP_ENTRIES_WIDTH-1:0]])
                                     );
endmodule // dec_pmp_ctl
