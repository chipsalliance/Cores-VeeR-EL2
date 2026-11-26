load("@rules_hdl//autotuner:build_defs.bzl", "run_autotuner_tune")
load("@rules_hdl//gds_write:build_defs.bzl", "gds_write")
load("@rules_hdl//place_and_route:build_defs.bzl", "place_and_route", "custom_openroad_script")
load("@rules_hdl//static_timing:build_defs.bzl", "run_opensta")
load("@rules_hdl//synthesis:build_defs.bzl", "synthesize_rtl")
load("@rules_hdl//synthesis:defs.bzl", "sdc_library")
load("@rules_hdl//verilog:providers.bzl", "verilog_library")
load(
    "//common:openroad_warnings.bzl",
    "ASAP7_SUPPRESSED_WARNINGS",
)
load("//design:defs.bzl", "veer_el2")
exports_files(["bazel_patches/rules_hdl_asap7_visibility.patch"])
package(
    default_visibility = ["//visibility:public"],
)


load("@rules_hdl//power_analysis:build_defs.bzl", "post_sim_power_analysis")
load("@rules_hdl//macros:sim_genrules.bzl", "sim_genrules")

load("@rules_hdl//pli:defs.bzl", "pli_library")
load("//tools:defs.bzl", "build_el2_test_program")

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
    srcs = [
        ":asap7_sim_cell_model_files",
        "@rules_hdl//power_analysis/tests:replace_async_ff.py",
    ],
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
      python3 $(location @rules_hdl//power_analysis/tests:replace_async_ff.py) $$tmp
      mv $$tmp $@
    """,
)

CLK_PERIOD_NS = 4                                   # single source of truth (250 MHz)
CLK_PERIOD_PS = CLK_PERIOD_NS * 1000
HALF_PERIOD = CLK_PERIOD_NS * 1000 // 2             # picoseconds

# config -> (config name, target, axi_core_if)
CONFIGS = {
    "axi4"     : ("axi4"    , "default",     "1"),
    "ahb_lite" : ("ahb_lite", "default_ahb", "0"),
}

# Update constraints file
[genrule(
    name = "el2_constraints_%s" % c,
    srcs = ["//design:el2_constraints.sdc"],
    outs = ["el2_constraints_%s.sdc" % c],
    cmd = " && ".join([
        "grep -q '^set axi_core_if ' $(location //design:el2_constraints.sdc)",
        "sed 's/^set axi_core_if .*/set axi_core_if %s/' $(location //design:el2_constraints.sdc) > $@" % CONFIGS[c][2],
    ]),
) for c in CONFIGS]

[sdc_library(
    name = "constraint_%s" % c,
    srcs = [":el2_constraints_%s" % c],
) for c in CONFIGS]

# Generate verilog_library with VeeR EL2 config and RTL files
[veer_el2(
    name = "veer_el2_%s" % c,
    sets = [
        "build_%s" % CONFIGS[c][0],
    ],
    target = CONFIGS[c][1],
) for c in CONFIGS]

[verilog_library(
    name = "veer_el2_%s_verilog_lib" % c,
    deps = [
        ":veer_el2_%s" % c,
    ],
) for c in CONFIGS]

[synthesize_rtl(
    name = "veer_el2_synth_asap7_%s" % c,
    frontend = "slang",
    parser_extra_commands = [
        "--std latest",
        "--single-unit",
        "--allow-toplevel-iface-ports",
        "--allow-hierarchical-const",
        "--libraries-inherit-macros",
        "--no-implicit-memories",
    ],
    standard_cells = "@org_theopenroadproject_asap7sc7p5t_28//:asap7-sc7p5t_rev28_rvt-ccs_tt",
    top_module = "el2_veer_wrapper",
    deps = [
        ":veer_el2_%s_verilog_lib" % c,
    ],
    target_clock_period_pico_seconds = CLK_PERIOD_PS,
    verilog_defines = [
        "TEC_RV_TMR=tmr",
        "TEC_RV_ICG=clockhdr",
    ],
) for c in CONFIGS]

[run_opensta(
    name = "veer_el2_synth_sta_asap7_%s" % c,
    synth_target = ":veer_el2_synth_asap7_%s" % c,
    sdc = ":constraint_%s" % c,
) for c in CONFIGS]

[place_and_route(
    name = "veer_el2_place_and_route_asap7_%s" % c,
    clock_period = str(CLK_PERIOD_PS),
    core_padding_microns = 20,
    die_height_microns = 400,
    die_width_microns = 400,
    min_pin_distance = "0.2",
    placement_density = "0.35",
    suppress_warnings = ASAP7_SUPPRESSED_WARNINGS,
    sdc = ":constraint_%s" % c,
    synthesized_rtl = ":veer_el2_synth_asap7_%s" % c,
    qt_qpa_platform = "offscreen",
    custom_post_step_scripts = [custom_openroad_script(
        "veer_el2_die_shot_%s" % c,
        post_step = "global_routing",
        inputs = ["//tools:die_shot.tcl"],
        outputs = ["veer_el2_die_shot_%s.png" % c],
        script = """
            source $(location //tools:die_shot.tcl)
            die_shot ${veer_el2_die_shot_%s.png}
        """ % c
    )]
) for c in CONFIGS]

[gds_write(
    name = "veer_el2_gds_asap7_%s" % c,
    implemented_rtl = ":veer_el2_place_and_route_asap7_%s" % c,
) for c in CONFIGS]

[run_autotuner_tune(
    name = "veer-el2_tune_%s" % c,
    cells = "@org_theopenroadproject_asap7sc7p5t_28//:asap7-sc7p5t_rev28_rvt-ccs_tt",
    config = "//:autotuner_%s.json" % c,
    iterations = 1,
    jobs = 2,
    samples = 2,
    sdc = "//:constraint_%s" % c,
    stop_after_step = "global_routing",
    frontend = "slang",
    top = "el2_veer_wrapper",
    deps = [
        "//:veer_el2_%s_verilog_lib" % c,
    ],
) for c in CONFIGS]

# build and run Verilator gatelevel simulation
# TODO: temporary until Bazel itself carries gcc-riscv
build_el2_test_program(
    name = "el2_test_program",
    test = "dhry",
    make_args = [
        "DHRY_RUNS=1000",
    ],
)

pli_library(
    name = "tb_dpi_jtag",
    srcs = [
        "testbench/jtagdpi/jtagdpi.cc",
    ],
    hdrs = [
        "testbench/jtagdpi/jtagdpi.c",
        "testbench/jtagdpi/jtagdpi.h",
    ],
)

pli_library(
    name = "tb_dpi_tcp_server",
    srcs = [
        "testbench/tcp_server/tcp_server.cc",
    ],
    hdrs = [
        "testbench/tcp_server/tcp_server.c",
        "testbench/tcp_server/tcp_server.h",
    ],
)

verilog_library(
    name = "asap7_sim_cells",
    srcs = [":asap7_sim_cell_models"],   # the genrule's asap7_sim_cell_models.v
)

[verilog_library(
    name = "el2_gate_tb_%s_lib" % c,
    srcs = [
        "testbench/axi_lsu_dma_bridge.sv",
        "testbench/el2_veer_wrapper_gate_level.sv",
        "testbench/veer_wrapper.sv",
        # TB files from Makefile
        "testbench/tb_top_if.sv",
        "testbench/tb_top_pkg.sv",
        "testbench/tb_top.sv",
        "testbench/ahb_sif.sv",
        "testbench/axi_sif.sv",
        "testbench/jtagdpi/jtagdpi.sv",
        "testbench/ahb_lite_2to1_mux.sv",
        "testbench/ahb_lsu_dma_bridge.sv",
    ] + glob(["testbench/axi4_mux/*.v"]),
    hdrs = [
        "testbench/ccm_macros.svh",
        "testbench/icache_macros.svh",
        "testbench/dasm.svi",
    ],
    deps = [
        "//design:el2_gate_support",
        "//design:mem_lib",
        ":veer_el2_%s_config" % c,        # EL2 config dependency
        ":veer_el2_synth_asap7_%s" % c,   # synth netlist
        ":asap7_sim_cells",
    ],
    plis = [
        ":tb_dpi_jtag",
        ":tb_dpi_tcp_server",
    ],
) for c in CONFIGS]

[sim_genrules(
    module = ":el2_gate_tb_%s_lib" % c,
    top = "tb_top",
    name = "tb_gatelevel_%s_sim" % c,
    trace = "saif",
    extra_verilator_run_args = [
        "+test_halt",
        "+program_hex=$(execpath :el2_test_program_hex)",
        "+symbols=$(execpath :el2_test_program_sym)",
    ],
    extra_verilator_run_data = [
        ":el2_test_program_hex",
        ":el2_test_program_sym",
    ],
    extra_verilator_binary_vopts = [
        "--timescale", "1ns/10ps",
        "--assert",
        "--autoflush",
        "--trace-underscore",
        "--no-trace-params",
        "-fno-table",
        "+define+GATELEVEL_DUT",
        "+define+GATELEVEL_TRACE_SAIF",
        "-GMAX_CYCLES=2000000",
        "-GHALF_PERIOD=%d" % HALF_PERIOD,
        "-Wno-IMPLICITSTATIC",
        "-Wno-ASCRANGE",
        "-Wno-CASEINCOMPLETE",
        "-Wno-INITIALDLY",
        "-Wno-WIDTH",
        "-Wno-UNOPTFLAT",
        "-Wno-SIDEEFFECT",
        "-Wno-LATCH",
        "-Wno-SPECIFYIGN",
    ],
) for c in CONFIGS]

# power analysis using OpenROAD
[post_sim_power_analysis(
    name = "veer_el2_%s_power_analysis" % c,
    clock_period = str(CLK_PERIOD_PS),
    clock_port = "clk",
    synthesized_rtl = ":veer_el2_synth_asap7_%s" %c,
    saif_file = ":tb_gatelevel_%s_sim_verilator_run" % c,
    saif_scope = "tb_top/rvtop_wrapper/rvtop_synth_wrapper/rvtop_synth",
) for c in CONFIGS]
