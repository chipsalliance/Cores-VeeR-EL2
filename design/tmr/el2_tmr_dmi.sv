// Copyright 2026 Antmicro <www.antmicro.com>
// //
// // SPDX-License-Identifier: Apache-2.0
//
`ifdef RV_TRIPLE_MODULAR_REDUNDANCY_ENABLE
module el2_tmr_dmi
  import el2_mubi_pkg::*;
(
    input  logic clk,
    input  logic rst_l,

    // DMI
    input  logic        dmi_reg_en,
    input  logic        dmi_reg_wr_en,
    input  logic [6:0]  dmi_reg_addr,
    input  logic [31:0] dmi_reg_wdata,
    output logic [31:0] dmi_reg_rdata,

    // DMI TMR
    output logic        dmi_reg_en_veer[3],
    output logic        dmi_reg_wr_en_veer[3],
    output logic [ 6:0] dmi_reg_addr_veer[3],
    output logic [31:0] dmi_reg_wdata_veer[3],
    input  logic [31:0] dmi_reg_rdata_veer[3],

    // Fault inputs
    input  el2_mubi_pkg::el2_mubi_t dmi_fault_d[3],
    // Fault outputs
    output el2_mubi_pkg::el2_mubi_t dmi_fault_q[3],
    // Fault clear inputs
    input  el2_mubi_pkg::el2_mubi_t dmi_fault_clr[3]
);

  // ......................................................

  el2_mubi_t enable[3];

  el2_mubi_t fault_dmi_reg_rdata[3];
  el2_mubi_t crit_dmi_reg_rdata_nc;

  // ......................................................

  el2_tmr_voter #(.Width($bits(dmi_reg_rdata))) u_voter_dmi_reg_rdata (
    .in_a     (dmi_reg_rdata_veer[0]),
    .in_b     (dmi_reg_rdata_veer[1]),
    .in_c     (dmi_reg_rdata_veer[2]),

    .en_a     (enable[0]),
    .en_b     (enable[1]),
    .en_c     (enable[2]),

    .out      (dmi_reg_rdata),

    .fault_a  (fault_dmi_reg_rdata[0]),
    .fault_b  (fault_dmi_reg_rdata[1]),
    .fault_c  (fault_dmi_reg_rdata[2]),

    .critical (crit_dmi_reg_rdata_nc)
  );

  // ......................................................

  // Fault aggregation and registers
  for (genvar i=0; i<3; i=i+1) begin : fault
    el2_mubi_t fault_any;

    assign fault_any = mubi_or(fault_dmi_reg_rdata[i], dmi_fault_d[i]);

    always_ff @(posedge clk or negedge rst_l) begin
      if (!rst_l) begin
        dmi_fault_q[i] <= El2MuBiFalse;
      end else begin
        if (mubi_check_true(dmi_fault_clr[i])) begin
          dmi_fault_q[i] <= El2MuBiFalse;
        end else begin
          dmi_fault_q[i] <= mubi_or(dmi_fault_q[i], fault_any);
        end
      end
    end

    assign enable[i] = mubi_not(dmi_fault_q[i]);

  end

  // Propagate response to Cores
  for (genvar i=0; i < 3; i+=1) begin : resp
    assign dmi_reg_en_veer[i]    = dmi_reg_en;
    assign dmi_reg_addr_veer[i]  = dmi_reg_addr;
    assign dmi_reg_wr_en_veer[i] = dmi_reg_wr_en;
    assign dmi_reg_wdata_veer[i] = dmi_reg_wdata;
  end

endmodule
`endif
