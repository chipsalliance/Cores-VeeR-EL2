// DMI core aperture ranges from 0x00 to 0x4F. Addresses starting from 0x50
// and above are considered uncore.

module dmi_mux (

    // Uncore access enable
    input wire uncore_enable,

    // DMI upstream
    input  wire        dmi_en,
    input  wire        dmi_wr_en,
    input  wire [ 6:0] dmi_addr,
    input  wire [31:0] dmi_wdata,
    output wire [31:0] dmi_rdata,

    // DMI downstream for core
    output wire        dmi_core_en,
    output wire        dmi_core_wr_en,
    output wire [ 6:0] dmi_core_addr,
    output wire [31:0] dmi_core_wdata,
    input  wire [31:0] dmi_core_rdata,

    // DMI downstream for uncore
    output wire        dmi_uncore_en,
    output wire        dmi_uncore_wr_en,
    output wire [ 6:0] dmi_uncore_addr,
    output wire [31:0] dmi_uncore_wdata,
    input  wire [31:0] dmi_uncore_rdata
);
  logic is_uncore_aperture;

  // Uncore address decoder
  assign is_uncore_aperture = (dmi_addr[6] & (dmi_addr[5] | dmi_addr[4]));

  // Core signals
  assign dmi_core_en        = dmi_en & ~is_uncore_aperture;
  assign dmi_core_wr_en     = dmi_wr_en & ~is_uncore_aperture;
  assign dmi_core_addr      = dmi_addr;
  assign dmi_core_wdata     = dmi_wdata;

  // Uncore signals
  assign dmi_uncore_en      = dmi_en & is_uncore_aperture & uncore_enable;
  assign dmi_uncore_wr_en   = dmi_wr_en & is_uncore_aperture & uncore_enable;
  assign dmi_uncore_addr    = dmi_addr;
  assign dmi_uncore_wdata   = dmi_wdata;

  // Read mux
  assign dmi_rdata          = is_uncore_aperture ? dmi_uncore_rdata : dmi_core_rdata;

endmodule
