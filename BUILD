load("@bazel-orfs//:openroad.bzl", "orfs_flow")
load("@rules_hdl//verilog:defs.bzl", "verilog_library")
load("//design:defs.bzl", "veer_el2", "verilog_files")

# Skip the slow, sign-off-oriented parts of the flow. Every setting here
# is an ORFS variable; drop this dict for a real tapeout-grade run.
FAST_SETTINGS = {
    "FILL_CELLS": "",
    "GND_NETS_VOLTAGES": "",
    "GPL_ROUTABILITY_DRIVEN": "0",
    "GPL_TIMING_DRIVEN": "0",
    "PWR_NETS_VOLTAGES": "",
    "REMOVE_ABC_BUFFERS": "1",
    "SKIP_CTS_REPAIR_TIMING": "1",
    "SKIP_INCREMENTAL_REPAIR": "1",
    "SKIP_REPORT_METRICS": "1",
    "TAPCELL_TCL": "",
}

############################# AXI config ##############################
# Generate verilog_library with VeeR EL2 config and RTL files
veer_el2(
  name = "veer_el2_axi4",
  sets = [
    "build_axi4",
  ],
  target = "default",
)

verilog_files(
  name = "el2_axi4_files",
  deps = [":veer_el2_axi4"],
)

orfs_flow(
    name = "veer_el2_axi4_orfs",
    top = "el2_veer_wrapper",
    arguments = FAST_SETTINGS | {
        "CORE_UTILIZATION": "40",
        "PLACE_DENSITY": "0.65",
        "SYNTH_SLANG_ARGS": "--std latest --single-unit --allow-toplevel-iface-ports --allow-hierarchical-const --no-implicit-memories",
    },
    sources = {
        "SDC_FILE": ["//design:el2_constraints.sdc"],
        "VERILOG_INCLUDE_DIRS": [":el2_axi4_files_includes"],
    },
    verilog_files = [":el2_axi4_files"],
)

############################# AHB Lite config ##############################
veer_el2(
  name = "veer_el2_ahb_lite",
  sets = [
    "build_ahb_lite",
  ],
  target = "default_ahb",
)

verilog_files(
  name = "el2_ahb_lite_files",
  deps = [":veer_el2_ahb_lite"],
)

orfs_flow(
    name = "veer_el2_ahb_lite_orfs",
    top = "el2_veer_wrapper",
    arguments = FAST_SETTINGS | {
        "CORE_UTILIZATION": "40",
        "PLACE_DENSITY": "0.65",
        "SYNTH_SLANG_ARGS": "--std latest --single-unit --allow-toplevel-iface-ports --allow-hierarchical-const --no-implicit-memories",
    },
    sources = {
        "SDC_FILE": ["//design:el2_constraints.sdc"],
        "VERILOG_INCLUDE_DIRS": [":el2_ahb_lite_files_includes"],
    },
    verilog_files = [":el2_ahb_lite_files"],
)
