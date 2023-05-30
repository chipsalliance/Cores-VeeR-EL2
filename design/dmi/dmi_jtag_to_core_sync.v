// SPDX-License-Identifier: Apache-2.0
// Copyright 2018 Western Digital Corporation or it's affiliates.
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
//------------------------------------------------------------------------------------
//
//  Copyright Western Digital, 2019
//  Owner : Alex Grobman
//  Description:  
//                This module Synchronizes the signals between JTAG (TCK) and
//                processor (Core_clk)
//
//-------------------------------------------------------------------------------------

module dmi_jtag_to_core_sync (
// JTAG signals
input       rd_en,      // 1 bit  Read Enable from JTAG
input       wr_en,      // 1 bit  Write enable from JTAG

// Processor Signals
input       rst_n,      // Core reset
input       clk,        // Core clock

output      reg_en,     // 1 bit  Write interface bit to Processor
output      reg_wr_en   // 1 bit  Write enable to Processor
);
  
wire        c_rd_en;
wire        c_wr_en;
reg [2:0]   rden, wren;
 

// Outputs
assign reg_en    = c_wr_en | c_rd_en;
assign reg_wr_en = c_wr_en;

// synchronizers
wire rden_s;
wire wren_s;

`ifdef TECH_SPECIFIC_RV_SYNC
    `USER_RV_SYNC sync_rd
        .clk    (clk),
        .rst_n  (rst_n),
        .d      (rd_en),
        .q      (rden_s)
    );
    `USER_RV_SYNC sync_wr
        .clk    (clk),
        .rst_n  (rst_n),
        .d      (wr_en),
        .q      (wren_s)
    );
`else
    reg [1:0] rden_r;
    reg [1:0] wren_r;
    always @ ( posedge clk or negedge rst_n) begin
        if(!rst_n) begin
            rden_r <= '0;
            wren_r <= '0;
        end
        else begin
            rden_r <= {rden_r[0], rd_en};
            wren_r <= {wren_r[0], wr_en};
        end
    end
    assign rden_s = rden_r[1];
    assign wren_s = wren_r[1];
`endif

// edge detectors
reg prv_rden;
reg prv_wren;

always @ ( posedge clk or negedge rst_n) begin
    if(!rst_n) begin
        prv_rden <= 1'b0;
        prv_wren <= 1'b0;
    end else begin
        prv_rden <= rden_s;
        prv_wren <= wren_s;
    end
end

assign c_rd_en = prv_rden & ~rden_s;
assign c_wr_en = prv_wren & ~wren_s;

endmodule
