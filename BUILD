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


# config -> (config name, target, axi_core_if)
CONFIGS = {
    "axi"      : ("axi4"    , "default",     "1"),
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
    standard_cells = "@org_theopenroadproject_asap7sc7p5t_28//:asap7-sc7p5t_rev28_rvt-ccs_tt",
    top_module = "el2_veer_wrapper",
    deps = [
        ":veer_el2_%s_verilog_lib" % c,
    ],
    synth_tcl = "synth.tcl",
    target_clock_period_pico_seconds = 4000, # 250 MHz
    synth_additional_args = "-booth", # run booth pass to rebuild multipliers before mapping
) for c in CONFIGS]

[place_and_route(
    name = "veer_el2_place_and_route_asap7_%s" % c,
    clock_period = "4000", # in ps
    core_padding_microns = 20,
    die_height_microns = 400,
    die_width_microns = 400,
    min_pin_distance = "0.2",
    placement_density = "0.35",
    suppress_warnings = ASAP7_SUPPRESSED_WARNINGS,
    sdc = ":constraint_%s" % c,
    synthesized_rtl = ":veer_el2_synth_asap7_%s" % c,
    stop_after_step = "global_routing",
) for c in CONFIGS]

[gds_write(
    name = "veer_el2_gds_asap7_%s" % c,
    implemented_rtl = ":veer_el2_place_and_route_asap7_%s" % c,
) for c in CONFIGS]
