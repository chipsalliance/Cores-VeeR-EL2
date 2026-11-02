load("@rules_hdl//verilog:defs.bzl", "verilog_library")
load(":files.bzl", "EL2_CONFIG_FILES", "EL2_CONFIG_HDRS", "EL2_CONFIG_SRCS")

_GEN_CONFIG_BIN = Label("//configs:gen_config_bin")
_GEN_PICMAP = Label("//tools:picmap")

def el2_config(
        name,
        target = "default",
        sets = [],
        unsets = []):
    """Generates VeeR EL2 config headers and wraps them in a verilog_library.

    Args:
        name: target name for the resulting verilog_library.
        target: baseline settings : default, default_ahb, high_perf, typical_pd
        sets: list of "key=value" strings, one -set=... per entry.
        unsets: list of "key" strings, one -unset=... per entry.
    """
    set_flags = " ".join(["-set=%s" % s for s in sets])
    unset_flags = " ".join(["-unset=%s" % u for u in unsets])
    snapshot_dir = "snapshots/%s" % target

    native.genrule(
        name = "%s_gen" % name,
        srcs = [],
        outs = ["%s/%s" % (snapshot_dir, filename) for filename in EL2_CONFIG_FILES],
        cmd = (
            "BUILD_PATH=$(RULEDIR)/snapshots/{target} " +
            "RV_ROOT=$(location {gen_bin}).runfiles/{picmap} " +
            "$(location {gen_bin}) " +
            "-target={target} -snapshot={target} {sets} {unsets}"
        ).format(
            gen_bin = _GEN_CONFIG_BIN,
            picmap = _GEN_PICMAP.repo_name,
            sets = set_flags,
            target = target,
            unsets = unset_flags,
        ),
        tools = [_GEN_CONFIG_BIN],
    )

    verilog_library(
        name = name,
        # Compile configuration definitions before the RTL that consumes them.
        srcs = ["%s/%s" % (snapshot_dir, filename) for filename in EL2_CONFIG_SRCS],
        hdrs = [
            "%s/%s" % (snapshot_dir, filename)
            for filename in EL2_CONFIG_HDRS
        ],
        visibility = ["//visibility:public"],
    )
