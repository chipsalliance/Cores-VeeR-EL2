load("@rules_hdl//verilog:defs.bzl", "verilog_library", "VerilogInfo")
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


# ---------------------------------------------------------------------------------------
# verilog_files: verilog_library -> flat list of files for the orfs_flow rule
# ---------------------------------------------------------------------------------------

def _list(x):
    """A depset or a list/tuple as a plain list; None as empty."""
    if x == None:
        return []
    if type(x) == "depset":
        return x.to_list()
    return list(x)

def _libraries(info):
    """The libraries of a VerilogInfo, dependencies first."""
    if hasattr(info, "dag"):
        return info.dag.to_list()
    return _list(getattr(info, "deps", None)) + [info]

def _walk(deps):
    """(srcs, hdrs) of the whole graph, dependencies first, deduplicated."""
    srcs = []
    hdrs = []
    seen = {}
    for dep in deps:
        for lib in _libraries(dep[VerilogInfo]):
            for f in _list(getattr(lib, "srcs", None)):
                if f.path not in seen:
                    seen[f.path] = True
                    srcs.append(f)
            for f in _list(getattr(lib, "hdrs", None)):
                if f.path not in seen:
                    seen[f.path] = True
                    hdrs.append(f)
    return srcs, hdrs

def _srcs_impl(ctx):
    srcs, _ = _walk(ctx.attr.deps)
    flist = ctx.actions.declare_file(ctx.label.name + ".flist") # Filelist for debugging purposes
    ctx.actions.write(flist, "".join([f.short_path + "\n" for f in srcs]))
    return [
        DefaultInfo(files = depset(srcs)),
        OutputGroupInfo(flist = depset([flist])),
    ]

_verilog_srcs = rule(
    implementation = _srcs_impl,
    attrs = {"deps": attr.label_list(providers = [VerilogInfo], mandatory = True)},
    doc = "The srcs of a verilog_library graph, in dependency order.",
)

def _hdrs_impl(ctx):
    srcs, hdrs = _walk(ctx.attr.deps)
    include_files = hdrs + [f for f in srcs if f.extension in ["vh", "svh"]]
    out = ctx.actions.declare_directory(ctx.label.name)
    args = ctx.actions.args()
    args.add(out.path)
    args.add_all(include_files)
    # Copy all include files on the generated `name`_includes directory
    ctx.actions.run_shell(
        inputs = include_files,
        outputs = [out],
        arguments = [args],
        mnemonic = "VerilogIncludeDir",
        command = 'out="$1"; shift; mkdir -p "$out"; for f in "$@"; do cp -L "$f" "$out/"; done',
    )
    return [DefaultInfo(files = depset([out]))]

_verilog_hdrs = rule(
    implementation = _hdrs_impl,
    attrs = {"deps": attr.label_list(providers = [VerilogInfo], mandatory = True)},
    doc = "One directory holding every hdrs file of a verilog_library graph.",
)

def verilog_files(name, deps):
    """Flattens verilog_library targets into files for orfs_flow.

    Args:
      name: the compile list target; the include directory is <name>_includes.
      deps: verilog_library targets.
    """
    _verilog_srcs(name = name, deps = deps)
    _verilog_hdrs(name = name + "_includes", deps = deps)
