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
exports_files(["bazel_patches/rules_hdl_asap7_visibility.patch"])

# Collect ASAP7 v28 RVT behavioral cell models for gate-level simulation.
# Use the same PDK module as the synthesis rule above.
ASAP7_SIM_CELL_MODELS = [
    "@org_theopenroadproject_asap7sc7p5t_28//:asap7-cells-sc7p5t_rev28_rvt-v",
]

filegroup(
    name = "asap7_sim_cell_model_files",
    srcs = ASAP7_SIM_CELL_MODELS,
)

# Concatenate all ASAP7 PDK cell simulation models into the bazel-bin/asap7_sim_cell_models.v file
genrule(
    name = "asap7_sim_cell_models",
    srcs = [":asap7_sim_cell_model_files", "//tools:replace_async_ff.py"],
    outs = ["asap7_sim_cell_models.v"],
    cmd = """
      set -eu
      tmp=$@.tmp
      : > $$tmp
      for src in $(SRCS); do
        case "$$src" in
          */replace_async_ff.py) ;;
          */dff.v) ;;
          *) cat "$$src" >> $$tmp ;;
        esac
      done
      python3 $(location //tools:replace_async_ff.py) $$tmp
      mv $$tmp $@
    """,
)

# Place ASAP7 LEF files under bazel-bin for subsequent OpenROAD runs.
genrule(
    name = "asap7_pdk_lef",
    srcs = [
        "@org_theopenroadproject_asap7sc7p5t_28//:asap7-cells-sc7p5t_rev28_rvt-lef",
        "@org_theopenroadproject_asap7sc7p5t_28//:techlef_misc/asap7_tech_1x_201209.lef",
    ],
    outs = [
        "asap7sc7p5t_28_R_1x_220121a.lef",
        "asap7_tech_1x_201209.lef",
    ],
    cmd = """
      set -eu
      cp "$(location @org_theopenroadproject_asap7sc7p5t_28//:asap7-cells-sc7p5t_rev28_rvt-lef)" "$(@D)/asap7sc7p5t_28_R_1x_220121a.lef"
      cp "$(location @org_theopenroadproject_asap7sc7p5t_28//:techlef_misc/asap7_tech_1x_201209.lef)" "$(@D)/asap7_tech_1x_201209.lef"
    """,
)

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
    name = "veer_el2_synth_asap7_axi4",
    standard_cells = "@org_theopenroadproject_asap7sc7p5t_28//:asap7-sc7p5t_rev28_rvt",
    top_module = "el2_veer_wrapper",
    deps = [
        ":veer_el2_axi4_verilog_lib",
    ],
    target_clock_period_pico_seconds = 2000, # 500MHz
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
    standard_cells = "@org_theopenroadproject_asap7sc7p5t_28//:asap7-sc7p5t_rev28_rvt",
    top_module = "el2_veer_wrapper",
    deps = [
        ":veer_el2_ahb_lite_verilog_lib",
    ],
    target_clock_period_pico_seconds = 2000, # 500MHz
    synth_tcl = "synth.tcl",
)

sdc_library(
    name = "constraint",
    srcs = ["//design:el2_constraints.sdc"],
)
