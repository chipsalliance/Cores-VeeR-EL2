module ahb_to_axi4_wrapper
#(
   TAG = 1,
   `include "el2_param.vh"
)
(
    input                   clk,
    input                   rst_l,
    input                   scan_mode,
    input                   bus_clk_en,
    input                   clk_override,

    output logic            axi_awvalid,
    input  logic            axi_awready,
    output logic [TAG-1:0]  axi_awid,
    output logic [31:0]     axi_awaddr,
    output logic [2:0]      axi_awsize,
    output logic [2:0]      axi_awprot,
    output logic [7:0]      axi_awlen,
    output logic [1:0]      axi_awburst,

    output logic            axi_wvalid,
    input  logic            axi_wready,
    output logic [63:0]     axi_wdata,
    output logic [7:0]      axi_wstrb,
    output logic            axi_wlast,

    input  logic            axi_bvalid,
    output logic            axi_bready,
    input  logic [1:0]      axi_bresp,
    input  logic [TAG-1:0]  axi_bid,

    output logic            axi_arvalid,
    input  logic            axi_arready,
    output logic [TAG-1:0]  axi_arid,
    output logic [31:0]     axi_araddr,
    output logic [2:0]      axi_arsize,
    output logic [2:0]      axi_arprot,
    output logic [7:0]      axi_arlen,
    output logic [1:0]      axi_arburst,

    input  logic            axi_rvalid,
    output logic            axi_rready,
    input  logic [TAG-1:0]  axi_rid,
    input  logic [63:0]     axi_rdata,
    input  logic [1:0]      axi_rresp,

    input logic [31:0]      ahb_haddr,
    input logic [2:0]       ahb_hburst,
    input logic             ahb_hmastlock,
    input logic [3:0]       ahb_hprot,
    input logic [2:0]       ahb_hsize,
    input logic [1:0]       ahb_htrans,
    input logic             ahb_hwrite,
    input logic [63:0]      ahb_hwdata,
    input logic             ahb_hsel,
    input logic             ahb_hreadyin,

    output logic [63:0]      ahb_hrdata,
    output logic             ahb_hreadyout,
    output logic             ahb_hresp
);
    // set CHECK_RANGES(0), the rest remains default.
    // this allows working with the full range of addresses.
    ahb_to_axi4 #(.pt(pt),.CHECK_RANGES(0)) inst (
        .*
    );
endmodule // ahb_to_axi4_wrapper
