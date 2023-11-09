interface dccm_interface (
    input logic clk,
    reset
);

  `include "el2_param.vh"
  ;

  logic [pt.DCCM_BITS-1:0] addr;
  logic wr_en;
  logic rd_en;
  logic [pt.DCCM_FDATA_WIDTH-1:0] wdata;
  logic [pt.DCCM_FDATA_WIDTH-1:0] rdata;

endinterface
