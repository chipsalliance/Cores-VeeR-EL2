module el2_btb_tag_hash
import el2_pkg::*;
#(
`include "el2_param.vh"
 ) (
                       input logic [pt.BTB_ADDR_HI+pt.BTB_BTAG_SIZE+pt.BTB_BTAG_SIZE+pt.BTB_BTAG_SIZE:pt.BTB_ADDR_HI+1] pc,
                       output logic [pt.BTB_BTAG_SIZE-1:0] hash
                       );

    assign hash = {(pc[pt.BTB_ADDR_HI+pt.BTB_BTAG_SIZE+pt.BTB_BTAG_SIZE+pt.BTB_BTAG_SIZE:pt.BTB_ADDR_HI+pt.BTB_BTAG_SIZE+pt.BTB_BTAG_SIZE+1] ^
                   pc[pt.BTB_ADDR_HI+pt.BTB_BTAG_SIZE+pt.BTB_BTAG_SIZE:pt.BTB_ADDR_HI+pt.BTB_BTAG_SIZE+1] ^
                   pc[pt.BTB_ADDR_HI+pt.BTB_BTAG_SIZE:pt.BTB_ADDR_HI+1])};
endmodule

module el2_btb_tag_hash_fold
import el2_pkg::*;
#(
`include "el2_param.vh"
 )(
                       input logic [pt.BTB_ADDR_HI+pt.BTB_BTAG_SIZE+pt.BTB_BTAG_SIZE:pt.BTB_ADDR_HI+1] pc,
                       output logic [pt.BTB_BTAG_SIZE-1:0] hash
                       );

    assign hash = {(
                   pc[pt.BTB_ADDR_HI+pt.BTB_BTAG_SIZE+pt.BTB_BTAG_SIZE:pt.BTB_ADDR_HI+pt.BTB_BTAG_SIZE+1] ^
                   pc[pt.BTB_ADDR_HI+pt.BTB_BTAG_SIZE:pt.BTB_ADDR_HI+1])};

endmodule

module el2_btb_addr_hash
import el2_pkg::*;
#(
`include "el2_param.vh"
 )(
                        input logic [pt.BTB_INDEX3_HI:pt.BTB_INDEX1_LO] pc,
                        output logic [pt.BTB_ADDR_HI:pt.BTB_ADDR_LO] hash
                        );


if(pt.BTB_FOLD2_INDEX_HASH) begin : fold2
   assign hash[pt.BTB_ADDR_HI:pt.BTB_ADDR_LO] = pc[pt.BTB_INDEX1_HI:pt.BTB_INDEX1_LO] ^
                                                pc[pt.BTB_INDEX3_HI:pt.BTB_INDEX3_LO];
end
   else begin
   assign hash[pt.BTB_ADDR_HI:pt.BTB_ADDR_LO] = pc[pt.BTB_INDEX1_HI:pt.BTB_INDEX1_LO] ^
                                                pc[pt.BTB_INDEX2_HI:pt.BTB_INDEX2_LO] ^
                                                pc[pt.BTB_INDEX3_HI:pt.BTB_INDEX3_LO];
end

endmodule

module el2_btb_ghr_hash
import el2_pkg::*;
#(
`include "el2_param.vh"
 )(
                       input logic [pt.BTB_ADDR_HI:pt.BTB_ADDR_LO] hashin,
                       input logic [pt.BHT_GHR_SIZE-1:0] ghr,
                       output logic [pt.BHT_ADDR_HI:pt.BHT_ADDR_LO] hash
                       );

   // The hash function is too complex to write in verilog for all cases.
   // The config script generates the logic string based on the bp config.
   if(pt.BHT_GHR_HASH_1) begin : ghrhash_cfg1
     assign hash[pt.BHT_ADDR_HI:pt.BHT_ADDR_LO] = { ghr[pt.BHT_GHR_SIZE-1:pt.BTB_INDEX1_HI-1], hashin[pt.BTB_INDEX1_HI:2]^ghr[pt.BTB_INDEX1_HI-2:0]};
   end
   else begin : ghrhash_cfg2
     assign hash[pt.BHT_ADDR_HI:pt.BHT_ADDR_LO] = { hashin[pt.BHT_GHR_SIZE+1:2]^ghr[pt.BHT_GHR_SIZE-1:0]};
   end


endmodule
