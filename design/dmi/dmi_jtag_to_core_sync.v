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
always @ ( posedge clk or negedge rst_n) begin
    if(!rst_n) begin
        rden <= '0;
        wren <= '0;
    end
    else begin
        rden <= {rden[1:0], rd_en};
        wren <= {wren[1:0], wr_en};
    end
end

assign c_rd_en = rden[1] & ~rden[2];
assign c_wr_en = wren[1] & ~wren[2];


endmodule
