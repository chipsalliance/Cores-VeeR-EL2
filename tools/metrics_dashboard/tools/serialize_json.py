#!/usr/bin/env python3

# Merge runs (metrics file '<name>.json' + metadata file '<name>.metadata.json') into the dashboard's columnar data file:
#   {"metrics": [{"path", "unit"}],
#    "refs": [{"kind": "branch", "name"} | {"kind": "pr", "number"},
#             "runs": [{"id", "metadata"}],
#             "values": [per metric: null if the ref lacks it, else [per run: value or null]]}]}

import argparse
import hashlib
import json
import os
import sys
from pathlib import Path

from messages import Messages, add_message_arguments
from unit_sources import join, match_unit_type
from units import convert
from validate_metrics import (
    add_schema_arguments, category_paths, cross_check_config, is_metadata_file, load, load_setup, metadata_path,
    target_unit, validate_run
)

DATA_FILE = "data.json"
CONFIG_FILE = "config.json"
DASHBOARD_KEYS = ("labels", "units", "summary", "overview", "unplottable")


def write_file(path, content):
    tmp = f"{path}.tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        f.write(content)
    os.replace(tmp, path)


def source_id(*contents):
    # Re-adding the same run is a no-op, 48 bits so that ID is a JS number
    digest = hashlib.sha256()
    for content in contents:
        digest.update(hashlib.sha256(content).digest())
    return int.from_bytes(digest.digest()[:6], "big")


def ref_key(ref):
    return (ref["kind"], ref["number"] if ref["kind"] == "pr" else ref["name"])


def ref_of(metadata):
    return {"kind": "pr", "number": metadata["pr_number"]} if metadata["is_pr"] else {"kind": "branch", "name": metadata["source_branch"]}


def ref_name(ref):
    return f"PR #{ref['number']}" if ref["kind"] == "pr" else f"branch '{ref['name']}'"


# ({path: unit}, {ref key: ref with its runs and {path: column}}) of the serialized data
def read_data(data_path):
    if not os.path.exists(data_path):
        return {}, {}

    raw = load(data_path)
    try:
        paths = [tuple(m["path"]) for m in raw["metrics"]]
        units = {p: m["unit"] for p, m in zip(paths, raw["metrics"])}
        refs = {}
        for r in raw["refs"]:
            ref = {k: r[k] for k in ("kind", "name", "number") if k in r}
            ref.update(runs=r["runs"], columns={p: v for p, v in zip(paths, r["values"]) if v is not None})
            refs[ref_key(ref)] = ref
    except (KeyError, TypeError) as e:
        raise ValueError(f"{DATA_FILE}: unexpected structure ({e!r}), remove it to serialize from scratch") from e

    return units, refs


# Every metric in units has a column in some ref
def dump_data(units, refs):
    return {
        "metrics": [{"path": list(p), "unit": u} for p, u in units.items()],
        "refs": [
            {**{k: v for k, v in r.items() if k not in ("runs", "columns")}, "runs": r["runs"], "values": [r["columns"].get(p) for p in units]}
            for r in refs.values()
        ],
    }


# Removes the closed PRs along with the metrics only they had
def remove_closed_prs(units, refs, open_prs):
    for key, ref in list(refs.items()):
        if ref["kind"] == "pr" and ref["number"] not in open_prs:
            del refs[key]
            print(f"Removed {ref_name(ref)}: not open", file=sys.stderr)

    present = {p for ref in refs.values() for p in ref["columns"]}
    for path in set(units) - present:
        del units[path]


# Converts the serialized data to the config's target units
def renormalize(units, refs, config, msgs):
    for path, unit in units.items():
        try:
            target = target_unit(config, match_unit_type(config.patterns, path))
            if target is None or unit == target:
                continue
            for ref in refs.values():
                if path in ref["columns"]:
                    ref["columns"][path] = [None if v is None else convert(v, unit, target)[0] for v in ref["columns"][path]]
            units[path] = target
        except ValueError as e:
            msgs.errors.append(f"{DATA_FILE}: {join(path)}: {e}")


# (ref, run ID, {path: (value, unit)}, metadata) of the run, None if it's invalid
def read_run(input_file, validators, config, msgs):
    content = Path(input_file).read_bytes()
    metadata_content = metadata_path(input_file).read_bytes()
    metadata = json.loads(metadata_content)

    run_msgs = Messages()
    values = validate_run(json.loads(content), metadata, validators, config, run_msgs)
    msgs.add(run_msgs, prefix=f"{input_file}: ")
    if run_msgs.errors:
        return None

    return ref_of(metadata), source_id(content, metadata_content), values, metadata


# A path can be a metric in one run and a category in another, a single metrics file can't have such a clash
def check_paths(units, msgs):
    paths = set(units)
    for path in sorted(category_paths(paths) & paths):
        msgs.errors.append(f"'{join(path)}' is both a metric and a category")


def write_config(output_dir, config):
    data = {k: config.data[k] for k in DASHBOARD_KEYS if k in config.data}
    write_file(os.path.join(output_dir, CONFIG_FILE), json.dumps(data, indent=2) + "\n")


def serialize_json(output_dir, input_files, config, validators, verbose=False, open_prs=None):
    msgs = Messages()

    os.makedirs(output_dir, exist_ok=True)
    data_path = os.path.join(output_dir, DATA_FILE)
    units, refs = read_data(data_path)

    if open_prs is not None:
        remove_closed_prs(units, refs, open_prs)

    # Covers config changes even when no runs are added
    renormalize(units, refs, config, msgs)

    num_new_runs = 0
    for input_file in input_files:
        # Metadata files are read along with their metrics file (e.g. when matched by a glob)
        if is_metadata_file(input_file):
            continue
        try:
            run = read_run(input_file, validators, config, msgs)
        except (OSError, ValueError) as e:
            msgs.errors.append(f"{input_file}: {e}")
            continue
        if run is None:
            continue
        run_ref, run_id, values, metadata = run
        if open_prs is not None and run_ref["kind"] == "pr" and run_ref["number"] not in open_prs:
            print(f"Skipping {input_file}: {ref_name(run_ref)} is not open", file=sys.stderr)
            continue

        ref = refs.setdefault(ref_key(run_ref), {**run_ref, "runs": [], "columns": {}})
        runs, columns = ref["runs"], ref["columns"]
        if any(r["id"] == run_id for r in runs):
            print(f"Skipping {input_file}: already merged (run {run_id} of {ref_name(ref)})", file=sys.stderr)
            continue

        for path, (_, unit) in values.items():
            stored = units.setdefault(path, unit)
            if stored != unit:
                # Units without a target in the config (e.g. custom ones) that differ between runs
                msgs.errors.append(f"{input_file}: {join(path)}: unit '{unit}' differs from the stored '{stored}'")
            columns.setdefault(path, [None] * len(runs))
        runs.append({"id": run_id, "metadata": metadata})
        for path, column in columns.items():
            column.append(values[path][0] if path in values else None)
        num_new_runs += 1

    check_paths(units, msgs)

    # Once, against all the serialized data
    metadata = [r["metadata"] for ref in refs.values() for r in ref["runs"]]
    if metadata:
        cross_check_config(list(units), metadata, config, msgs)

    msgs.print(verbose)

    # Nothing is written unless every input was processed successfully
    if msgs.errors:
        raise ValueError("Couldn't process some of the input files.")

    write_file(data_path, json.dumps(dump_data(units, refs), separators=(",", ":")))
    write_config(output_dir, config)
    print(f"{num_new_runs} run(s) merged into {data_path}", file=sys.stderr)


def main():
    parser = argparse.ArgumentParser(description="Validate, normalize and append metrics.", allow_abbrev=False)
    parser.add_argument("-o", "--output", required=True, type=Path, help="destination directory for the serialized data")
    parser.add_argument("-c", "--config", required=True, type=Path, help="dashboard configuration")
    parser.add_argument("-i", "--inputs", nargs="*", default=[], type=Path, help="metrics files, each with a '<name>.metadata.json' next to it")
    parser.add_argument("--open-prs", type=int, nargs="+", metavar="PR", help="open PRs; PRs not on this list are removed from the serialized data")
    add_schema_arguments(parser)
    add_message_arguments(parser)
    args = parser.parse_args()

    if args.output.exists() and not args.output.is_dir():
        parser.error("Output is not a directory.")

    try:
        config, validators = load_setup(args)
        serialize_json(args.output, args.inputs, config, validators, args.verbose, args.open_prs)
    except (OSError, ValueError) as e:
        sys.exit(f"Error: {e}")


if __name__ == "__main__":
    main()
