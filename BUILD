load("@rules_hdl//gds_write:build_defs.bzl", "gds_write")
load("@rules_hdl//place_and_route:build_defs.bzl", "place_and_route")
load("@rules_hdl//synthesis:build_defs.bzl", "synthesize_rtl")
load("@rules_hdl//synthesis:defs.bzl", "sdc_library")
load("@rules_hdl//verilog:providers.bzl", "verilog_library")
load(
    "//common:openroad_warnings.bzl",
    "ASAP7_SUPPRESSED_WARNINGS",
)
load("//design:defs.bzl", "veer_el2")

############################# AXI config ##############################
# Generate verilog_library with VeeR EL2 config and RTL files
veer_el2(
  name = "veer_el2_axi4",
  sets = [
    "build_axi4",
  ],
  target = "default",
)

verilog_library(
    name = "veer_el2_axi4_verilog_lib",
    deps = [
        ":veer_el2_axi4",
    ],
)

synthesize_rtl(
    name = "veer_el2_synth_asap7_axi",
    standard_cells = "@org_theopenroadproject_asap7sc7p5t_28//:asap7-sc7p5t_rev28_rvt",
    top_module = "el2_veer_wrapper",
    deps = [
        ":veer_el2_axi4_verilog_lib",
    ],
    synth_tcl = "synth.tcl",
)

############################# AHB Lite config ##############################
veer_el2(
  name = "veer_el2_ahb_lite",
  sets = [
    "build_ahb_lite",
  ],
  target = "default_ahb",
)

verilog_library(
    name = "veer_el2_ahb_lite_verilog_lib",
    deps = [
        ":veer_el2_ahb_lite",
    ],
)

synthesize_rtl(
    name = "veer_el2_synth_asap7_ahb_lite",
    standard_cells = "@org_theopenroadproject_asap7sc7p5t_27//:asap7-sc7p5t_rev27_rvt",
    top_module = "el2_veer_wrapper",
    deps = [
        ":veer_el2_ahb_lite_verilog_lib",
    ],
    synth_tcl = "synth.tcl",
)

sdc_library(
    name = "constraint",
    srcs = ["//design:el2_constraints.sdc"],
)
