load("@rules_hdl//verilog:defs.bzl", "verilog_library")
load("//configs:defs.bzl", "el2_config")

_EL2_SV_FILES = [Label("//design:el2_srcs")]
_EL2_SV_INC = [Label("//design:el2_inc")]

def veer_el2(
        name,
        target = "default",
        sets = [],
        unsets = []):
    """Generates a VeeR EL2 core verilog_library, with the provided config."""

    # Internal, unexported config target — private to this instantiation.
    el2_config(
        name = "%s_config" % name,
        sets = sets,
        target = target,
        unsets = unsets,
    )

    verilog_library(
        name = name,
        srcs = _EL2_SV_FILES,
        visibility = ["//visibility:public"],
        deps = [
            ":%s_config" % name,
            Label("//design:beh_lib"),
            Label("//design:mem_lib"),
        ],
        hdrs = _EL2_SV_INC,
    )
