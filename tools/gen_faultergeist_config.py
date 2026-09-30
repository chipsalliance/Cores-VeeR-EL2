#!/usr/bin/env python3
"""
Generate a fault campaign JSON config from command-line parameters.

Every flag has a default, so running the script with no arguments produces
the default config. Examples:
    python3 gen_config.py
    python3 gen_config.py --seed 42 --liberty-paths "a.lib b.lib" -o config.json
"""
import argparse
import json
import re
import sys


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Generate a fault campaign JSON config.",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )

    model = parser.add_argument_group("model")
    model.add_argument("--model-name", default="random", help="fault model name")

    params = parser.add_argument_group("params")
    params.add_argument("--num-of-events", type=int, default=10000, help="Number of events to generate")
    params.add_argument("--simulation-time", default="1000ps", help="Simulation time")
    params.add_argument("--seed", type=int, default=67, help="Seed for RNG")
    params.add_argument("--sig-path-prefix", default="tb_top_tmr.rvtop_wrapper",
                        help="Hierarchical prefix of signal paths")
    params.add_argument("--top-module", default="el2_veer_wrapper", help="Top module name")
    params.add_argument("--top-instance", default="rvtop", help="Top instance name")
    params.add_argument("--netlist-path", default="netlist.json", help="netlist JSON path")
    params.add_argument("--fault-campaign-out", default="fault_campaign_out.csv",
                        help="fault campaign output CSV")
    params.add_argument("--thread-count", type=int, default=1, help="Number of threads to run in parallel")
    params.add_argument("--collect-wires", default=False, help="Whether wires are included in generated campaigns.")
    params.add_argument("--liberty-paths", nargs="*", default=[], metavar="LIB",
                        help='liberty files; either separate args or one space-separated '
                             'string, e.g. --liberty-paths "a.lib b.lib"')
    params.add_argument("--vlt-config", default="config.vlt", help="Verilator config file")

    parser.add_argument("-o", "--output", type=argparse.FileType("w"), default=sys.stdout,
                        help="output file (default: stdout)")
    parser.add_argument("--indent", type=int, default=2, help="JSON indent")

    return parser


def split_paths(items: list[str]) -> list[str]:
    """Accept both `--liberty-paths a.lib b.lib` and `--liberty-paths "a.lib b.lib"`."""
    return [path for item in items for path in re.split(r"[,\s]+", item) if path]


def main() -> None:
    args = build_parser().parse_args()

    config = {
        "model": {
            "name": args.model_name,
            "params": {},
        },
        "params": {
            "num_of_events": args.num_of_events,
            "simulation_time": args.simulation_time,
            "seed": args.seed,
            "sig_path_prefix": args.sig_path_prefix,
            "top_module": args.top_module,
            "top_instance": args.top_instance,
            "netlist_path": args.netlist_path,
            "collect_wires": args.collect_wires,
            "fault_campaign_out": args.fault_campaign_out,
            "thread_number": args.thread_count,
            "liberty_paths": split_paths(args.liberty_paths),
            "vlt_config": args.vlt_config,
        },
    }

    json.dump(config, args.output, indent=args.indent)
    args.output.write("\n")


if __name__ == "__main__":
    main()
