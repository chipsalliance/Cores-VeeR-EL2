// Copyright 2026 Antmicro <www.antmicro.com>
// //
// // SPDX-License-Identifier: Apache-2.0
//
`ifdef RV_TRIPLE_MODULAR_REDUNDANCY_ENABLE
module el2_tmr_dmi
  import el2_pkg::*;
  import el2_mubi_pkg::*;
  import el2_lockstep_pkg::*;
#(
    `include "el2_param.vh"
) (
    // DMI
    input  logic        dmi_reg_en,
    input  logic [6:0]  dmi_reg_addr,
    input  logic        dmi_reg_wr_en,
    input  logic [31:0] dmi_reg_wdata,
    output logic [31:0] dmi_reg_rdata,

    // DMI TMR
    output logic        dmi_reg_en_veer[3],
    output logic        dmi_reg_wr_en_veer[3],
    output logic [ 6:0] dmi_reg_addr_veer[3],
    output logic [31:0] dmi_reg_wdata_veer[3],
    input  logic [31:0] dmi_reg_rdata_veer[3]
);

  //TODO: Change it to use voters

  always_comb begin
    // Propagate response to Cores
    for (int i=0;i < 3; i+=1) begin
      dmi_reg_en_veer[i] = dmi_reg_en;
      dmi_reg_addr_veer[i] = dmi_reg_addr;
      dmi_reg_wr_en_veer[i] = dmi_reg_wr_en;
      dmi_reg_wdata_veer[i] = dmi_reg_wdata;
    end
    // Get value from Core 0 for the time being
    dmi_reg_rdata = dmi_reg_rdata_veer[0];
  end

endmodule
`endif
