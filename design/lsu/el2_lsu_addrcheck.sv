// SPDX-License-Identifier: Apache-2.0
// Copyright 2020 Western Digital Corporation or its affiliates.
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
// $Id$
//
//
// Owner:
// Function: Checks the memory map for the address
// Comments:
//
//********************************************************************************
module el2_lsu_addrcheck
import el2_pkg::*;
#(
`include "el2_param.vh"
 )(
   input logic          lsu_c2_m_clk,              // clock
   input logic          rst_l,                     // reset

   input logic [31:0]   start_addr_d,              // start address for lsu
   input logic [31:0]   end_addr_d,                // end address for lsu
   input el2_lsu_pkt_t lsu_pkt_d,                 // packet in d
   input logic [31:0]   dec_tlu_mrac_ff,           // CSR read
   input logic [3:0]    rs1_region_d,              // address rs operand [31:28]

   input logic [31:0]   rs1_d,                     // address rs operand

   output logic         is_sideeffects_m,          // is sideffects space
   output logic         addr_in_dccm_d,            // address in dccm
   output logic         addr_in_pic_d,             // address in pic
   output logic         addr_external_d,           // address in external

   output logic         access_fault_d,            // access fault
   output logic         misaligned_fault_d,        // misaligned
   output logic [3:0]   exc_mscause_d,             // mscause for access/misaligned faults

   output logic         fir_dccm_access_error_d,   // Fast interrupt dccm access error
   output logic         fir_nondccm_access_error_d,// Fast interrupt dccm access error

    input logic lsu_pmp_error_start,
    input logic lsu_pmp_error_end,

   input  logic         scan_mode                  // Scan mode
);


   logic        non_dccm_access_ok;
   logic        is_sideeffects_d, is_aligned_d;
   logic        start_addr_in_dccm_d, end_addr_in_dccm_d;
   logic        start_addr_in_dccm_region_d, end_addr_in_dccm_region_d;
   logic        start_addr_in_pic_d, end_addr_in_pic_d;
   logic        start_addr_in_pic_region_d, end_addr_in_pic_region_d;
   logic [4:0]  csr_idx;
   logic        addr_in_iccm;
   logic        start_addr_dccm_or_pic;
   logic        base_reg_dccm_or_pic;
   logic        unmapped_access_fault_d, mpu_access_fault_d, picm_access_fault_d, regpred_access_fault_d;
   logic        regcross_misaligned_fault_d, sideeffect_misaligned_fault_d;
   logic [3:0]  access_fault_mscause_d;
   logic [3:0]  misaligned_fault_mscause_d;

   if (pt.DCCM_ENABLE == 1) begin: Gen_dccm_enable
      // Start address check
      rvrangecheck #(.CCM_SADR(pt.DCCM_SADR),
                     .CCM_SIZE(pt.DCCM_SIZE)) start_addr_dccm_rangecheck (
         .addr(start_addr_d[31:0]),
         .in_range(start_addr_in_dccm_d),
         .in_region(start_addr_in_dccm_region_d)
      );

      // End address check
      rvrangecheck #(.CCM_SADR(pt.DCCM_SADR),
                     .CCM_SIZE(pt.DCCM_SIZE)) end_addr_dccm_rangecheck (
         .addr(end_addr_d[31:0]),
         .in_range(end_addr_in_dccm_d),
         .in_region(end_addr_in_dccm_region_d)
      );
   end else begin: Gen_dccm_disable // block: Gen_dccm_enable
      assign start_addr_in_dccm_d = '0;
      assign start_addr_in_dccm_region_d = '0;
      assign end_addr_in_dccm_d = '0;
      assign end_addr_in_dccm_region_d = '0;
   end

   if (pt.ICCM_ENABLE == 1) begin : check_iccm
      assign addr_in_iccm =  (start_addr_d[31:28] == pt.ICCM_REGION);
   end else begin
     assign addr_in_iccm = 1'b0;
   end

   // PIC memory check
   // Start address check
   rvrangecheck #(.CCM_SADR(pt.PIC_BASE_ADDR),
                  .CCM_SIZE(pt.PIC_SIZE)) start_addr_pic_rangecheck (
      .addr(start_addr_d[31:0]),
      .in_range(start_addr_in_pic_d),
      .in_region(start_addr_in_pic_region_d)
   );

   // End address check
   rvrangecheck #(.CCM_SADR(pt.PIC_BASE_ADDR),
                  .CCM_SIZE(pt.PIC_SIZE)) end_addr_pic_rangecheck (
      .addr(end_addr_d[31:0]),
      .in_range(end_addr_in_pic_d),
      .in_region(end_addr_in_pic_region_d)
   );

   assign start_addr_dccm_or_pic  = start_addr_in_dccm_region_d | start_addr_in_pic_region_d;
   assign base_reg_dccm_or_pic    = ((rs1_region_d[3:0] == pt.DCCM_REGION) & pt.DCCM_ENABLE) | (rs1_region_d[3:0] == pt.PIC_REGION);
   assign addr_in_dccm_d          = (start_addr_in_dccm_d & end_addr_in_dccm_d);
   assign addr_in_pic_d           = (start_addr_in_pic_d & end_addr_in_pic_d);

   assign addr_external_d   = ~(start_addr_in_dccm_region_d | start_addr_in_pic_region_d);
   assign csr_idx[4:0]       = {start_addr_d[31:28], 1'b1};
   assign is_sideeffects_d = dec_tlu_mrac_ff[csr_idx] & ~(start_addr_in_dccm_region_d | start_addr_in_pic_region_d | addr_in_iccm) & lsu_pkt_d.valid & (lsu_pkt_d.store | lsu_pkt_d.load);  //every region has the 2 LSB indicating ( 1: sideeffects/no_side effects, and 0: cacheable ). Ignored in internal regions
   assign is_aligned_d    = (lsu_pkt_d.word & (start_addr_d[1:0] == 2'b0)) |
                                                            (lsu_pkt_d.half & (start_addr_d[0] == 1'b0)) |
                                                            lsu_pkt_d.by;

  if (pt.PMP_ENTRIES == 0) begin
   assign non_dccm_access_ok = (~(|{pt.DATA_ACCESS_ENABLE0,pt.DATA_ACCESS_ENABLE1,pt.DATA_ACCESS_ENABLE2,pt.DATA_ACCESS_ENABLE3,pt.DATA_ACCESS_ENABLE4,pt.DATA_ACCESS_ENABLE5,pt.DATA_ACCESS_ENABLE6,pt.DATA_ACCESS_ENABLE7})) |
                               (((pt.DATA_ACCESS_ENABLE0 & ((start_addr_d[31:0] | pt.DATA_ACCESS_MASK0)) == (pt.DATA_ACCESS_ADDR0 | pt.DATA_ACCESS_MASK0)) |
                                 (pt.DATA_ACCESS_ENABLE1 & ((start_addr_d[31:0] | pt.DATA_ACCESS_MASK1)) == (pt.DATA_ACCESS_ADDR1 | pt.DATA_ACCESS_MASK1)) |
                                 (pt.DATA_ACCESS_ENABLE2 & ((start_addr_d[31:0] | pt.DATA_ACCESS_MASK2)) == (pt.DATA_ACCESS_ADDR2 | pt.DATA_ACCESS_MASK2)) |
                                 (pt.DATA_ACCESS_ENABLE3 & ((start_addr_d[31:0] | pt.DATA_ACCESS_MASK3)) == (pt.DATA_ACCESS_ADDR3 | pt.DATA_ACCESS_MASK3)) |
                                 (pt.DATA_ACCESS_ENABLE4 & ((start_addr_d[31:0] | pt.DATA_ACCESS_MASK4)) == (pt.DATA_ACCESS_ADDR4 | pt.DATA_ACCESS_MASK4)) |
                                 (pt.DATA_ACCESS_ENABLE5 & ((start_addr_d[31:0] | pt.DATA_ACCESS_MASK5)) == (pt.DATA_ACCESS_ADDR5 | pt.DATA_ACCESS_MASK5)) |
                                 (pt.DATA_ACCESS_ENABLE6 & ((start_addr_d[31:0] | pt.DATA_ACCESS_MASK6)) == (pt.DATA_ACCESS_ADDR6 | pt.DATA_ACCESS_MASK6)) |
                                 (pt.DATA_ACCESS_ENABLE7 & ((start_addr_d[31:0] | pt.DATA_ACCESS_MASK7)) == (pt.DATA_ACCESS_ADDR7 | pt.DATA_ACCESS_MASK7)))   &
                                ((pt.DATA_ACCESS_ENABLE0 & ((end_addr_d[31:0]   | pt.DATA_ACCESS_MASK0)) == (pt.DATA_ACCESS_ADDR0 | pt.DATA_ACCESS_MASK0)) |
                                 (pt.DATA_ACCESS_ENABLE1 & ((end_addr_d[31:0]   | pt.DATA_ACCESS_MASK1)) == (pt.DATA_ACCESS_ADDR1 | pt.DATA_ACCESS_MASK1)) |
                                 (pt.DATA_ACCESS_ENABLE2 & ((end_addr_d[31:0]   | pt.DATA_ACCESS_MASK2)) == (pt.DATA_ACCESS_ADDR2 | pt.DATA_ACCESS_MASK2)) |
                                 (pt.DATA_ACCESS_ENABLE3 & ((end_addr_d[31:0]   | pt.DATA_ACCESS_MASK3)) == (pt.DATA_ACCESS_ADDR3 | pt.DATA_ACCESS_MASK3)) |
                                 (pt.DATA_ACCESS_ENABLE4 & ((end_addr_d[31:0]   | pt.DATA_ACCESS_MASK4)) == (pt.DATA_ACCESS_ADDR4 | pt.DATA_ACCESS_MASK4)) |
                                 (pt.DATA_ACCESS_ENABLE5 & ((end_addr_d[31:0]   | pt.DATA_ACCESS_MASK5)) == (pt.DATA_ACCESS_ADDR5 | pt.DATA_ACCESS_MASK5)) |
                                 (pt.DATA_ACCESS_ENABLE6 & ((end_addr_d[31:0]   | pt.DATA_ACCESS_MASK6)) == (pt.DATA_ACCESS_ADDR6 | pt.DATA_ACCESS_MASK6)) |
                                 (pt.DATA_ACCESS_ENABLE7 & ((end_addr_d[31:0]   | pt.DATA_ACCESS_MASK7)) == (pt.DATA_ACCESS_ADDR7 | pt.DATA_ACCESS_MASK7))));
  end

   // Access fault logic
   // 0. Unmapped local memory : Addr in dccm region but not in dccm offset OR Addr in picm region but not in picm offset OR DCCM -> PIC cross when DCCM/PIC in same region
   // 1. Uncorrectable (double bit) ECC error
   // 3. Address is not in a populated non-dccm region
   // 5. Region predication access fault: Base Address in DCCM/PIC and Final address in non-DCCM/non-PIC region or vice versa
   // 6. Ld/St access to picm are not word aligned or word size
   assign regpred_access_fault_d  = (start_addr_dccm_or_pic ^ base_reg_dccm_or_pic);                   // 5. Region predication access fault: Base Address in DCCM/PIC and Final address in non-DCCM/non-PIC region or vice versa
   assign picm_access_fault_d     = (addr_in_pic_d & ((start_addr_d[1:0] != 2'b0) | ~lsu_pkt_d.word));                                               // 6. Ld/St access to picm are not word aligned or word size

   if (pt.DCCM_ENABLE & (pt.DCCM_REGION == pt.PIC_REGION)) begin
      assign unmapped_access_fault_d = ((start_addr_in_dccm_region_d & ~(start_addr_in_dccm_d | start_addr_in_pic_d)) |   // 0. Addr in dccm/pic region but not in dccm/pic offset
                                        (end_addr_in_dccm_region_d & ~(end_addr_in_dccm_d | end_addr_in_pic_d))       |   // 0. Addr in dccm/pic region but not in dccm/pic offset
                                        (start_addr_in_dccm_d & end_addr_in_pic_d)                                    |   // 0. DCCM -> PIC cross when DCCM/PIC in same region
                                        (start_addr_in_pic_d  & end_addr_in_dccm_d));                                     // 0. DCCM -> PIC cross when DCCM/PIC in same region
    if (pt.PMP_ENTRIES > 0) begin
      assign mpu_access_fault_d   = (lsu_pmp_error_start | lsu_pmp_error_end);                                         // X. Address is in blocked region
    end else begin
      assign mpu_access_fault_d   = (~start_addr_in_dccm_region_d & ~non_dccm_access_ok);                              // 3. Address is not in a populated non-dccm region
    end
   end else begin
      assign unmapped_access_fault_d = ((start_addr_in_dccm_region_d & ~start_addr_in_dccm_d)                              |   // 0. Addr in dccm region but not in dccm offset
                                        (end_addr_in_dccm_region_d & ~end_addr_in_dccm_d)                                  |   // 0. Addr in dccm region but not in dccm offset
                                        (start_addr_in_pic_region_d & ~start_addr_in_pic_d)                                |   // 0. Addr in picm region but not in picm offset
                                        (end_addr_in_pic_region_d & ~end_addr_in_pic_d));                                      // 0. Addr in picm region but not in picm offset
    if (pt.PMP_ENTRIES > 0) begin
      assign mpu_access_fault_d   = (lsu_pmp_error_start | lsu_pmp_error_end);                                              // X. Address is in blocked region
    end else begin
      assign mpu_access_fault_d   = (~start_addr_in_pic_region_d & ~start_addr_in_dccm_region_d & ~non_dccm_access_ok);     // 3. Address is not in a populated non-dccm region
    end
   end

   assign access_fault_d = (unmapped_access_fault_d | mpu_access_fault_d | picm_access_fault_d | regpred_access_fault_d) & lsu_pkt_d.valid & ~lsu_pkt_d.dma;
   assign access_fault_mscause_d[3:0] = unmapped_access_fault_d ? 4'h2 : mpu_access_fault_d ? 4'h3 : regpred_access_fault_d ? 4'h5 : picm_access_fault_d ? 4'h6 : 4'h0;

   // Misaligned happens due to 2 reasons
   // 0. Region cross
   // 1. sideeffects access which are not aligned
   assign regcross_misaligned_fault_d = (start_addr_d[31:28] != end_addr_d[31:28]);
   assign sideeffect_misaligned_fault_d = (is_sideeffects_d & ~is_aligned_d);
   assign misaligned_fault_d = (regcross_misaligned_fault_d | (sideeffect_misaligned_fault_d & addr_external_d)) & lsu_pkt_d.valid & ~lsu_pkt_d.dma;
   assign misaligned_fault_mscause_d[3:0] = regcross_misaligned_fault_d ? 4'h2 : sideeffect_misaligned_fault_d ? 4'h1 : 4'h0;

   assign exc_mscause_d[3:0] = misaligned_fault_d ? misaligned_fault_mscause_d[3:0] : access_fault_mscause_d[3:0];

   // Fast interrupt error logic
   assign fir_dccm_access_error_d    = ((start_addr_in_dccm_region_d & ~start_addr_in_dccm_d) |
                                                                                (end_addr_in_dccm_region_d   & ~end_addr_in_dccm_d)) & lsu_pkt_d.valid & lsu_pkt_d.fast_int;
   assign fir_nondccm_access_error_d = ~(start_addr_in_dccm_region_d & end_addr_in_dccm_region_d) & lsu_pkt_d.valid & lsu_pkt_d.fast_int;

   rvdff #(.WIDTH(1))   is_sideeffects_mff (.din(is_sideeffects_d), .dout(is_sideeffects_m), .clk(lsu_c2_m_clk), .*);

endmodule // el2_lsu_addrcheck
