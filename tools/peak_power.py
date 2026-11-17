#!/usr/bin/env python3

# Copyright 2025 Antmicro
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
"""Per-clock-cycle (peak) and glitch power analysis with OpenROAD.

Takes the base activity and the per-cycle activity files written by trace2power,
runs OpenROAD/OpenSTA `report_power` for each of them and
reports the peak-power cycle. Every cycle is an independent OpenROAD run, so the
runs are executed in parallel.
"""

import argparse
import csv
import os
import re
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed


def read_lines(path):
    with open(path, "r", encoding="utf8") as f:
        return f.readlines()


def total_power(report_lines):
    """Sum of the first three numbers (internal, switching, leakage) on the 'Total' line."""
    for line in report_lines:
        if line.startswith("Total"):
            nums = re.findall(r"\d*\.\d+(?:[eE][-+]?\d+)?", line)
            return float(nums[0]) + float(nums[1]) + float(nums[2])
    return 0.0


def abspath(p):
    return os.path.abspath(p) if p else p


def tcl_path(p):
    # Brace-quote so spaces and brackets in paths are safe in Tcl.
    return "{" + p + "}"


def natural_key(path):
    """Sort 2.saif before 10.saif."""
    name = os.path.basename(path)
    return [int(t) if t.isdigit() else t for t in re.split(r"(\d+)", name)]


def list_inputs(path):
    """A directory -> its files in natural order; a single file -> [file]."""
    if os.path.isdir(path):
        files = [os.path.join(path, f) for f in os.listdir(path)
                 if os.path.isfile(os.path.join(path, f))]
        return sorted(files, key=natural_key)
    return [path]


def activity_commands(path, fmt, saif_scope):
    """Tcl commands that annotate activity from a trace2power output file."""
    if fmt == "saif":
        return [f"read_saif -scope {tcl_path(saif_scope)} {tcl_path(path)}"]
    return [f"source {tcl_path(path)}", "set_pin_activity_and_duty"]


def main():
    ap = argparse.ArgumentParser(allow_abbrev=False, description=__doc__)
    ap.add_argument("--base", required=True, help="base activity file from trace2power")
    ap.add_argument("--total", required=True,
                    help="directory with the per-cycle total activity files")
    ap.add_argument("--glitch", help="directory with the per-cycle glitch activity files")
    ap.add_argument("--cycles", type=int, help="number of cycles to process (default: all)")
    ap.add_argument("--format", choices=("saif", "tcl"), default="saif",
                    help="format of all activity files (default: saif)")
    ap.add_argument("--saif-scope",
                    help="design hierarchy scope that the SAIF top maps to (required for saif)")

    d = ap.add_argument_group("design")
    d.add_argument("--odb", help="OpenROAD database (e.g. 1_synth.odb)")
    d.add_argument("--netlist", help="gate-level Verilog netlist (alternative to --odb)")
    d.add_argument("--top", help="top module name (required with --netlist)")
    d.add_argument("--tech-lef", help="technology LEF, read before linking a netlist")
    d.add_argument("--cell-lef", action="append", default=[],
                   help="cell LEF; repeat for more files")
    d.add_argument("--sdc", help="SDC file (optional when --clock-period-ns is given)")
    d.add_argument("--clock-period-ns", type=float,
                   help="create a clock on the --clock-port port with this period in ns")
    d.add_argument("--clock-port", default="clk",
                   help="name of the top-level clock port used with --clock-period-ns "
                        "(default: clk)")
    d.add_argument("--lib", action="append", default=[], required=True,
                   help="Liberty file; repeat for each (.lib or .lib.gz)")

    o = ap.add_argument_group("outputs / tools")
    o.add_argument("--out-dir", required=True,
                   help="where the generated Tcl, logs and reports go")
    o.add_argument("--csv", help="write results to this CSV file")
    o.add_argument("--plot", help="plot PNG (needs matplotlib); default: <out-dir>/report.png")
    o.add_argument("--no-plot", action="store_true", help="skip plotting")
    o.add_argument("--openroad", default=os.environ.get("OPENROAD_EXE", "openroad"),
                   help="openroad executable (default: $OPENROAD_EXE or 'openroad')")
    o.add_argument("--jobs", type=int, default=os.cpu_count(),
                   help="OpenROAD processes to run in parallel; each loads the whole "
                        "design, so mind the memory (default: min(cpus, 4))")
    o.add_argument("--tcl-only", action="store_true",
                   help="only write the Tcl scripts, do not run OpenROAD")
    args = ap.parse_args()

    if args.format == "saif" and not args.saif_scope:
        ap.error("--saif-scope is required with --format saif")
    if bool(args.odb) == bool(args.netlist):
        ap.error("give exactly one of --odb or --netlist")
    if args.netlist and not args.top:
        ap.error("--netlist needs --top")
    if not args.sdc and args.clock_period_ns is None:
        ap.error("provide --sdc and/or --clock-period-ns")
    if args.clock_period_ns is not None and args.clock_period_ns <= 0:
        ap.error("--clock-period-ns must be greater than zero")
    if args.jobs < 1:
        ap.error("--jobs must be at least 1")

    out = abspath(args.out_dir)
    total_out = os.path.join(out, "total")
    glitch_out = os.path.join(out, "glitch")
    os.makedirs(total_out, exist_ok=True)
    if args.glitch:
        os.makedirs(glitch_out, exist_ok=True)

    base_file = abspath(args.base)
    total_files = list_inputs(abspath(args.total))
    if args.cycles:
        total_files = total_files[: args.cycles]
    glitch_files = list_inputs(abspath(args.glitch)) if args.glitch else []
    if args.glitch:
        if len(glitch_files) < len(total_files):
            print(f"warning: only {len(glitch_files)} glitch files for {len(total_files)} cycles")
        glitch_files = glitch_files[: len(total_files)]

    # ---- design setup shared by every run (each run loads a fresh design) ----
    design_tcl = []
    if args.tech_lef:
        design_tcl.append(f"read_lef {tcl_path(abspath(args.tech_lef))}")
    for lef in args.cell_lef:
        design_tcl.append(f"read_lef {tcl_path(abspath(lef))}")
    for lib in args.lib:
        design_tcl.append(f"read_liberty {tcl_path(abspath(lib))}")
    if args.odb:
        design_tcl.append(f"read_db {tcl_path(abspath(args.odb))}")
    else:
        design_tcl.append(f"read_verilog {tcl_path(abspath(args.netlist))}")
        design_tcl.append(f"link_design {args.top}")
    if args.sdc:
        design_tcl.append(f"read_sdc {tcl_path(abspath(args.sdc))}")
    if args.clock_period_ns is not None:
        design_tcl.append(
            f"create_clock -name core_clock -period {args.clock_period_ns:g} "
            f"[get_ports {tcl_path(args.clock_port)}]")

    # ---- one independent job per cycle; total and glitch of a cycle share a run ----
    base_report = os.path.join(out, "base.rpt")
    jobs = [{"name": "base", "activities": [(base_file, base_report)]}]
    for i in range(len(total_files)):
        acts = [(total_files[i], os.path.join(total_out, os.path.basename(total_files[i])))]
        if i < len(glitch_files):
            acts.append((glitch_files[i],
                         os.path.join(glitch_out, os.path.basename(glitch_files[i]))))
        jobs.append({"name": f"cycle_{i:06d}", "activities": acts})

    job_tcl = {}
    for job in jobs:
        lines = list(design_tcl)
        for activity_file, report_file in job["activities"]:
            lines += activity_commands(activity_file, args.format, args.saif_scope)
            lines.append(f"report_power > {tcl_path(report_file)}")
        path = os.path.join(out, f"{job['name']}.tcl")
        with open(path, "w") as f:
            f.write("\n".join(lines) + "\n")
        job_tcl[job["name"]] = path
    print(f"wrote {len(jobs)} OpenROAD scripts for {len(total_files)} cycles")
    if args.tcl_only:
        return 0

    print(f"Will launch {args.jobs} parallel OpenROAD processes")
    # ---- run OpenROAD in parallel ----
    def run_openroad(job):
        name = job["name"]
        reports = [r for _, r in job["activities"]]
        log_file = os.path.join(out, f"{name}.log")
        with open(log_file, "w") as log:
            rc = subprocess.run([args.openroad, "-no_splash", "-exit", job_tcl[name]],
                                stdout=log, stderr=subprocess.STDOUT, text=True).returncode
        missing = [r for r in reports if not os.path.exists(r)]
        if rc != 0 or missing:
            tail = "".join(read_lines(log_file)[-25:])
            raise RuntimeError(f"OpenROAD job {name} failed (rc={rc}, {len(missing)} missing "
                               f"reports). See {log_file}\n{tail}")

    failures = []
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = [pool.submit(run_openroad, job) for job in jobs]
        for fut in as_completed(futures):
            try:
                fut.result()
            except RuntimeError as err:
                failures.append(str(err))
    if failures:
        sys.exit("\n\n".join(failures))

    # ---- post-process ----
    base_power = total_power(read_lines(base_report))
    totals = [total_power(read_lines(os.path.join(total_out, os.path.basename(f))))
              for f in total_files]
    glitches = [total_power(read_lines(os.path.join(glitch_out, os.path.basename(f)))) - base_power
                for f in glitch_files]
    cycles = list(range(len(totals)))

    peak = max(totals) if totals else 0.0
    peak_cycle = totals.index(peak) if totals else 0
    print(f"Base power: {base_power} W")
    print(f"Maximum power consumption of a single clock cycle is {peak} Watts "
          f"and occurred in clock cycle #{peak_cycle}")

    if not args.no_plot:
        try:
            import matplotlib
            matplotlib.use("Agg")
            import matplotlib.pyplot as plt
        except ImportError:
            print("matplotlib not available: skipping plot (use --no-plot to silence)")
        else:
            plt.plot(cycles, totals, marker="o", linestyle="-", color="g", label="total")
            if glitches:
                plt.plot(cycles[: len(glitches)], glitches, marker="o", linestyle="-",
                         color="r", label="glitch")
            plt.title("Power consumption over time")
            plt.xlabel("Clock cycle")
            plt.ylabel("Power consumption (Watts)")
            plt.grid(True)
            plt.savefig(abspath(args.plot) if args.plot else os.path.join(out, "report.png"))

    if args.csv:
        with open(abspath(args.csv), "w", newline="") as f:
            w = csv.writer(f)
            w.writerow(["Clock cycle index", "Total power"] + (["Glitch power"] if glitches else []))
            for i, tp in enumerate(totals):
                w.writerow([i, tp] + ([glitches[i] if i < len(glitches) else ""] if glitches else []))
    return 0


if __name__ == "__main__":
    sys.exit(main())
