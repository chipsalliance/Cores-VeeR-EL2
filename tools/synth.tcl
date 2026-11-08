# Yosys synthesis script for el2_veer_wrapper
# Run with: yosys -c synth.tcl
#
# Required environment variables:
#   BUILD_DIR     output directory (log + netlist.v)
#   LIB_FILES     whitespace-separated list of .lib files
#   LIB_ARGS      liberty args for dfflibmap/abc (e.g. "-liberty a.lib")
#   RV_ROOT       repo root (contains yosys-abc-copy and design/flist)
#   NETLIST_JSON  path of the JSON netlist
# Optional:
#   TOP           top module (default: el2_veer_wrapper)
#   DEFINES       space-separated slang define args, passed verbatim
#   INCLUDES      space-separated slang include args, passed verbatim

proc env_req {name} {
    if {![info exists ::env($name)] || $::env($name) eq ""} {
        error "Environment variable $name is not set"
    }
    return $::env($name)
}

proc env_opt {name default} {
    if {[info exists ::env($name)] && $::env($name) ne ""} {
        return $::env($name)
    }
    return $default
}

set build_dir    [env_req BUILD_DIR]
set lib_files    [env_req LIB_FILES]
set lib_args     [env_req LIB_ARGS]
set rv_root      [env_req RV_ROOT]
set netlist_json [env_req NETLIST_JSON]
set top          [env_opt TOP el2_veer_wrapper]
set defines      [env_opt DEFINES ""]
set includes     [env_opt INCLUDES ""]

set slang_args [list \
    --top $top \
    --std latest --single-unit \
    --best-effort-hierarchy \
    --allow-toplevel-iface-ports \
    --allow-hierarchical-const \
    --libraries-inherit-macros \
    --no-implicit-memories \
    {*}$defines \
    {*}$includes \
    -F $rv_root/design/flist \
]

file mkdir $build_dir
set log $build_dir/synth.log

# Truncate the log once; every step below appends (replaces "tee -o" on the first line)
close [open $log w]

# Quiet step: output goes to the log only
proc step_quiet {args} {
    yosys tee -q -a $::log {*}$args
}

# Loud step: output goes to the log and stdout
proc step_loud {args} {
    yosys tee -a $::log {*}$args
}

# {*} expands the whitespace-separated env strings into separate arguments
step_quiet read_liberty -overwrite -setattr liberty_cell -lib {*}$lib_files
step_quiet read_slang {*}$slang_args
step_quiet synth -noabc -top $top
step_quiet clean
step_quiet rename -wire
step_quiet dfflibmap {*}$lib_args
step_quiet abc {*}$lib_args

step_loud write_verilog $build_dir/netlist.v
step_loud write_json $netlist_json
step_loud check -assert -mapped
