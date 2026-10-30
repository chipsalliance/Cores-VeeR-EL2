#!/usr/bin/env python3

# Merge metrics files into the dashboard's columnar data file:
#   {"runs": [{"id", "source"}], "metrics": [{"path", "unit", "values"}]}
# where values[i] belongs to runs[i] (null if the run lacks the metric).
# Values are validated and normalized to the config's target units.

import argparse
import hashlib
import json
import os
import shutil
import sys
from pathlib import Path
import re

from units import normalize
from validate_metrics import RESERVED, CAT_SEPARATOR, load, schema_errors, validate

SCRIPT_DIR = Path(__file__).resolve().parent
DATA_FILE = "data.json"
CONFIG_FILE = "config.json"
# Precision for the unit conversion (number of digits after '.')
PRECISION = 12


def load_json(path, default=None):
    if default is not None and not os.path.exists(path):
        return default
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def write_file(path, content):
    tmp = f"{path}.tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        f.write(content)
    os.replace(tmp, path)


def source_id(content):
    # Re-adding the same file is a no-op, 48 bits so that ID is a JS number
    return int.from_bytes(hashlib.sha256(content).digest()[:6], "big")


# Yield (path, value) for every leaf metric
def flatten(node, prefix=()):
    for key, val in node.items():
        path = (*prefix, key)
        if isinstance(val, dict):
            yield from flatten(val, path)
        else:
            yield path, val


def join(path):
    return CAT_SEPARATOR.join(path)


# Stored columns follow the target units, convert them if the config changed
def renormalize(metrics, units, errors):
    for path, metric in metrics.items():
        target = units.get(path[-1])
        if target is not None and metric["unit"] != target:
            try:
                metric["values"] = [None if v is None else normalize(v, metric["unit"], target, PRECISION) for v in metric["values"]]
                metric["unit"] = target
            except ValueError as e:
                errors.append(f"{DATA_FILE}: {join(path)}: {e}")


def read_run(input_file, schema, units, errors, verbose):
    content = Path(input_file).read_bytes()
    data = json.loads(content)

    errs, warnings, infos = validate(data, schema)
    errors += [f"{input_file}: {m}" for m in errs]
    if verbose:
        for level, msgs in (("Warning", warnings), ("Info", infos)):
            for m in msgs:
                print(f"{level}: {input_file}: {m}", file=sys.stderr)
    if errs:
        return None, content, None

    src_units = data.get("units", {})
    values = {}
    for path, value in flatten({k: v for k, v in data.items() if k not in RESERVED}):
        name = path[-1]
        if name not in src_units and name not in units:
            # No conversion needed
            values[path] = value
        elif name not in units:
            errors.append(f"{input_file}: {join(path)}: no target unit in the config")
        else:
            try:
                values[path] = normalize(value, src_units[name], units[name], PRECISION)
            except ValueError as e:
                errors.append(f"{input_file}: {join(path)}: {e}")

    src_metadata = data.get("metadata")
    if not src_metadata.get("is_pr"):
        node_name = "branch/" + src_metadata.get("source_branch")
    else:
        node_name = "pr/" + str(src_metadata.get("pr_number"))
    return node_name, content, values


def check_config(metrics, config, errors):
    paths = {join(p) for p in metrics}

    for field in ("date", "commit"):
        if config[field] not in paths:
            errors.append(f"config {field}: '{config[field]}' is not a metric in the data")

    for key in config.get("summary", []):
        if key not in paths:
            errors.append(f"config summary: '{key}' is not a metric in the data")

    names = {name for p in metrics for name in p}
    categories = {join(p[:i]) for p in metrics for i in range(1, len(p))}
    for entry in config.get("unplottable", []):
        known = entry in paths | categories if CAT_SEPARATOR in entry else entry in names
        if not known:
            print(f"Warning: config unplottable: '{entry}' matches nothing in the data", file=sys.stderr)

def check_paths(metrics, errors):
    categories = {p[:i] for p in metrics for i in range(1, len(p))}
    for path in sorted(categories & metrics.keys()):
        errors.append(f"'{join(path)}' is both a metric and a category")

def serialize_json(output_dir, input_files, config, schema, verbose=False):
    errors = []

    os.makedirs(output_dir, exist_ok=True)
    data_path = os.path.join(output_dir, DATA_FILE)
    data = load_json(data_path, [])
    if not isinstance(data, list) or not all(isinstance(n, dict) and "ref" in n for n in data):
        raise ValueError(f"{DATA_FILE}: expected an array of objects with a 'ref' key")
    nodes = {n["ref"]: n for n in data}
    if len(nodes) != len(data):
        raise ValueError(f"{DATA_FILE}: duplicate 'ref' values")
    units = config["units"]

    num_new_runs = 0
    for input_file in input_files:
        try:
            node_name, content, values = read_run(input_file, schema, units, errors, verbose)
        except Exception as e:
            errors.append(f"{input_file}: {e}")
            continue

        node = nodes.get(node_name) or {"ref": node_name, "metrics": [], "runs": []}
        runs = node["runs"]
        metrics = {tuple(m["path"]): m for m in node["metrics"]}
        sources = {r["id"]: r["source"] for r in runs}

        renormalize(metrics, units, errors)

        idx = source_id(content)
        if idx in sources:
            print(f"Skipping {input_file}: already merged as {sources[idx]}", file=sys.stderr)
            continue

        if values is None:
            continue

        num_new_runs += 1
        for path in values:
            if path not in metrics:
                metrics[path] = {"path": list(path), "unit": units[path[-1]] if path[-1] in units else "", "values": [None] * len(runs)}
        runs.append({"id": idx, "source": str(input_file)})

        for path, metric in metrics.items():
            metric["values"].append(values.get(path))

        check_paths(metrics, errors)
        check_config(metrics, config, errors)

        node["metrics"] = list(metrics.values())
        node["runs"] = runs
        nodes[node_name] = node

    # Nothing is written unless every input was processed successfully
    if errors:
        for e in errors:
            print(f"Error: {e}", file=sys.stderr)
        raise ValueError("Couldn't process some of the input files.")

    write_file(data_path, json.dumps(list(nodes.values()), separators=(",", ":")))
    print(f"{num_new_runs} run(s) merged into {data_path}", file=sys.stderr)

def main():
    parser = argparse.ArgumentParser(description="Validate, normalize and append metrics.")

    parser.add_argument(
        "-o", "--output",
        required=True,
        type=Path,
        help="Destination directory for the dashboard data"
    )

    parser.add_argument(
        "-c", "--config",
        required=True,
        type=Path,
        help="Dashboard configuration (labels, target units, ...)"
    )

    parser.add_argument(
        "-i", "--inputs",
        required=True,
        nargs="+",
        type=Path,
        help="Input JSON metrics files (one or more)"
    )

    parser.add_argument(
        "--metrics-schema",
        default=SCRIPT_DIR / "metrics.schema.json",
        type=Path,
        help="Metrics JSON Schema (default: %(default)s)"
    )

    parser.add_argument(
        "--config-schema",
        default=SCRIPT_DIR / "config.schema.json",
        type=Path,
        help="Config JSON Schema (default: %(default)s)"
    )

    parser.add_argument(
        "-v", "--verbose",
        action="store_true",
        help="Print validation warnings"
    )

    args = parser.parse_args()

    if os.path.exists(args.output) and not os.path.isdir(args.output):
        parser.error("Output is not a directory.")

    try:
        config = load(args.config)
        metrics_schema = load(args.metrics_schema)
        errors = schema_errors(config, load(args.config_schema), "config")
        if errors:
            raise ValueError("; ".join(errors))
        serialize_json(args.output, args.inputs, config, metrics_schema, args.verbose)
    except (OSError, ValueError) as e:
        sys.exit(f"Error: {e}")

    shutil.copy2(args.config, args.output / CONFIG_FILE)

if __name__ == "__main__":
    main()
