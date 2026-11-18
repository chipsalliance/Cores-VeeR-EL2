"""Rules for transforming VeeR EL2 sources."""

load("@rules_hdl//verilog:providers.bzl", "VerilogInfo", "make_dag_entry", "make_verilog_info")
load("//configs:files.bzl", "EL2_CONFIG_FILES")

def _design_path(file):
    marker = "/design/"
    marker_index = file.short_path.find(marker)
    if marker_index >= 0:
        return file.short_path[marker_index + len(marker):]
    if file.short_path.startswith("design/"):
        return file.short_path[len("design/"):]
    return None

def _file_paths(ctx, file):
    design_path = _design_path(file)
    if design_path != None:
        directory, separator, basename = design_path.rpartition("/")
        if file.extension in ["sv", "svh", "v", "vh"]:
            basename = "%s%s" % (ctx.attr.prefix, basename)
        if separator:
            output_path = "design/%s/%s" % (directory, basename)
        else:
            output_path = "design/%s" % basename
        return ("design/%s" % design_path, output_path)

    if file.basename in EL2_CONFIG_FILES:
        snapshot_directory = "snapshots/%s" % file.dirname.rpartition("/")[2]
        return (
            "%s/%s" % (snapshot_directory, file.basename),
            "%s/%s%s" % (snapshot_directory, ctx.attr.prefix, file.basename),
        )

    fail("File is neither a VeeR design source nor a config output: %s" % file.short_path)

def _prefix_veer_sources_impl(ctx):
    if not ctx.attr.prefix:
        fail("prefix must not be empty")
    if "/" in ctx.attr.prefix:
        fail("prefix must not contain '/'")

    dag_entries = ctx.attr.library[VerilogInfo].dag.to_list()
    source_inputs = depset([file for entry in dag_entries for file in entry.srcs])
    header_inputs = depset([file for entry in dag_entries for file in entry.hdrs])
    data_inputs = depset([file for entry in dag_entries for file in entry.data])
    inputs = depset(transitive = [source_inputs, header_inputs, data_inputs])

    source_outputs = []
    header_outputs = []
    data_outputs = []

    output_root = ctx.bin_dir.path
    if ctx.label.package:
        output_root += "/%s" % ctx.label.package
    output_root += "/%s" % ctx.label.name

    staged_inputs = []
    snapshot_directory = ""

    for input_set, output_list in [
        (source_inputs, source_outputs),
        (header_inputs, header_outputs),
        (data_inputs, data_outputs),
    ]:
        for input_file in input_set.to_list():
            staging_path, relative_output = _file_paths(ctx, input_file)
            output_file = ctx.actions.declare_file("%s/%s" % (ctx.label.name, relative_output))
            output_list.append(output_file)
            staged_inputs.extend([input_file.path, staging_path])
            if input_file.basename in EL2_CONFIG_FILES:
                snapshot_directory = staging_path.rpartition("/")[0]

    outputs = source_outputs + header_outputs + data_outputs

    args = ctx.actions.args()
    args.add(ctx.executable._prefix_macros.path)
    args.add(output_root)
    args.add(ctx.attr.prefix)
    args.add(snapshot_directory)
    args.add_all(staged_inputs)

    ctx.actions.run(
        executable = ctx.executable._runner,
        arguments = [args],
        inputs = inputs,
        mnemonic = "PrefixVeerEl2Sources",
        outputs = outputs,
        progress_message = "Prefixing VeeR EL2 sources for %{label}",
        tools = [ctx.executable._prefix_macros],
    )

    verilog_info = make_verilog_info(
        new_entries = [make_dag_entry(
            srcs = source_outputs,
            hdrs = header_outputs,
            data = data_outputs,
            plis = [],
            deps = [],
            label = ctx.label,
            tags = [],
        )],
    )

    return [
        DefaultInfo(files = depset(outputs)),
        verilog_info,
    ]

prefix_veer_sources = rule(
    implementation = _prefix_veer_sources_impl,
    attrs = {
        "library": attr.label(
            mandatory = True,
            providers = [VerilogInfo],
        ),
        "prefix": attr.string(default = "veer0_"),
        "_prefix_macros": attr.label(
            default = Label("//tools:prefix_macros"),
            cfg = "exec",
            executable = True,
        ),
        "_runner": attr.label(
            default = Label("//tools:prefix_veer_sources_runner"),
            cfg = "exec",
            executable = True,
        ),
    },
    provides = [VerilogInfo],
)

# TODO: This should be replaced with a proper gcc-riscv compilation within Bazel
def build_el2_test_program(name, test, make_args = []):
    """Builds <test> with the host RISC-V toolchain.

    Produces :<name>_hex (program.hex) and :<name>_sym (program.sym).
    """
    hex_out = "%s/program.hex" % name
    sym_out = "%s/program.sym" % name
    native.genrule(
        name = name,
        srcs = [
            "//tools:Makefile",
            "//configs:veer.config",
            "testbench/link.ld",
        ] + native.glob([
            "testbench/asm/**",
            "testbench/tests/**",
        ]),
        outs = [hex_out, sym_out],
        tools = ["testbench/build_test_hex.sh"],
        tags = [
            "local",
            "no-remote-cache"
        ],
        cmd = """
            set -euo pipefail
            # Toolchain: default to /opt/riscv, override with --action_env=RISCV_ROOT=...
            export PATH="$${RISCV_ROOT:-/opt/riscv}/bin:$$PATH"
            if ! command -v riscv64-unknown-elf-gcc >/dev/null 2>&1; then
                echo "ERROR: riscv64-unknown-elf-gcc not found." >&2
                echo "PATH=$$PATH" >&2
                echo "Install it, or pass --action_env=RISCV_ROOT=<toolchain root>" >&2
                echo "(or --action_env=PATH). Refusing to fall back to canned hex files." >&2
                exit 1
            fi
            tmp="$$(mktemp -d)"
            PROGRAM_OUTPUT_DIR="$$tmp" bash $(execpath testbench/build_test_hex.sh) %s %s
            cp "$$tmp/%s.hex" $(execpath %s)
            if [ -f "$$tmp/%s.sym" ]; then cp "$$tmp/%s.sym" $(execpath %s); else : > $(execpath %s); fi
            rm -rf "$$tmp"
        """ % (
            test, " ".join(["'%s'" % a for a in make_args]),
            test, hex_out,
            test, test, sym_out, sym_out,
        ),
    )
    native.filegroup(name = name + "_hex", srcs = [hex_out])
    native.filegroup(name = name + "_sym", srcs = [sym_out])
