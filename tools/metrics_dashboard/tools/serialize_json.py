#!/usr/bin/env python3

# Merge runs (metrics file '<name>.json' + metadata file '<name>.metadata.json') into the dashboard's columnar data file:
#   {"metrics": [{"path", "unit"}],
#    "refs": [{"kind": "branch", "name"} | {"kind": "pr", "number"},
#             "runs": [{"id", "metadata"}],
#             "values": [per metric: null if the ref lacks it, else [per run: value or null]]}]}

import argparse
import hashlib
import json
import logging
import os
import sys
import warnings
from pathlib import Path

from unit_sources import join, match_unit_type
from units import convert
from validate_metrics import (
    add_schema_arguments,
    category_paths,
    cross_check_config,
    is_metadata_file,
    load,
    load_setup,
    metadata_path,
    target_unit,
    validate_run,
)

DATA_FILE = "data.json"
CONFIG_FILE = "config.json"
DASHBOARD_KEYS = ("main_branch", "labels", "units", "summary", "overview", "unplottable")

log = logging.getLogger(__name__)


def setup_logging(verbosity: int) -> None:
    level = {0: logging.ERROR, 1: logging.WARNING, 2: logging.INFO}.get(verbosity, logging.DEBUG)
    logging.basicConfig(level=level, format="%(levelname)s: %(message)s")
    logging.captureWarnings(True)  # Captures warnings.warn-reported warnings


def load_json_content(bytes):
    content = {}
    try:
        content = json.loads(bytes)
    except Exception as e:
        warnings.warn(f"Cannot load contents into JSON: {e}", stacklevel=2)
    return content


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


def ref_key(ref, no_strict=False):
    ref_key = None
    try:
        ref_key = (ref["kind"], ref["number"] if ref["kind"] == "pr" else ref["name"])
    except (KeyError, TypeError) as e:
        error_msg = f"Cannot associate metrics with any ref. Missing kind or number/name: {e!r}"
        if no_strict:
            warnings.warn(error_msg, stacklevel=2)
        else:
            raise ValueError(error_msg)
    return ref_key


def ref_of(metadata):
    ref = None
    try:
        ref = (
            {"kind": "pr", "number": metadata["pr_number"]}
            if metadata["is_pr"]
            else {"kind": "branch", "name": metadata["source_branch"]}
        )
    except Exception as e:
        warnings.warn(f"Missing metadata keys. Cannot assign metrics. {e}", stacklevel=2)
    return ref


def ref_name(ref):
    name = None
    try:
        name = f"PR #{ref['number']}" if ref["kind"] == "pr" else f"branch '{ref['name']}'"
    except (KeyError, TypeError) as e:
        warnings.warn(
            f"Cannot associate metrics with any ref. Missing kind or number/name: {e!r}",
            stacklevel=2,
        )
    return name


# Ref with its runs and {path: column}, None if it's invalid. Invalid runs and columns are dropped.
# paths: the path of each metric (None if it's invalid), aligned with the values of the ref
def read_ref(raw, paths, no_strict=False):
    if not (
        isinstance(raw, dict) and all(isinstance(raw.get(k), list) for k in ("runs", "values"))
    ):
        return None
    ref = {k: raw[k] for k in ("kind", "name", "number") if k in raw}

    runs = raw["runs"]
    kept = [
        i
        for i, run in enumerate(runs)
        if isinstance(run, dict) and "id" in run and isinstance(run.get("metadata"), dict)
    ]
    invalid_run_msg = f"{len(runs) - len(kept)} invalid run(s) of {ref}"
    if len(kept) < len(runs) and no_strict:
        warnings.warn(f"{DATA_FILE}: dropped {invalid_run_msg}", stacklevel=2)
    elif len(kept) < len(runs):
        raise ValueError(f"{DATA_FILE}: {invalid_run_msg}")

    columns = {}
    for path, column in zip(paths, raw["values"]):
        if path is None or column is None:
            continue
        if isinstance(column, list) and len(column) == len(runs):
            columns[path] = [column[i] for i in kept]
        else:
            invalid_value_msg = f"invalid values of '{join(path)}' of {ref}"
            if no_strict:
                warnings.warn(f"{DATA_FILE}: dropped {invalid_value_msg}", stacklevel=2)
            else:
                raise ValueError(f"{DATA_FILE}: {invalid_value_msg}")
    return {**ref, "runs": [runs[i] for i in kept], "columns": columns}


# ({path: unit}, {ref key: ref with its runs and {path: column}}) of the serialized data.
# Invalid parts are dropped with a warning, unreadable data is treated as empty.
def read_data(data_path, no_strict=False):
    def list_in(raw, key):
        value = raw.get(key, [])
        if isinstance(value, list):
            return value
        key_err_msg = f"'{key}', it isn't a list"
        if no_strict:
            warnings.warn(f"{DATA_FILE}: dropped {key_err_msg}", stacklevel=2)
            return []
        else:
            raise ValueError(f"{DATA_FILE}: {key_err_msg}")

    if not os.path.exists(data_path):
        return {}, {}

    raw = load(data_path)
    if not isinstance(raw, dict):
        obj_err_msg = "isn't an object"
        if no_strict:
            warnings.warn(f"{DATA_FILE}: dropped, {obj_err_msg}", stacklevel=2)
            return {}, {}
        else:
            raise ValueError(f"{DATA_FILE}: {obj_err_msg}")

    paths, units = [], {}
    for metric in list_in(raw, "metrics"):
        path = metric.get("path") if isinstance(metric, dict) else None
        if isinstance(path, list) and path and "unit" in metric and tuple(path) not in units:
            units[tuple(path)] = metric["unit"]
            paths.append(tuple(path))
        else:
            invalid_metric_msg = f"invalid metric {metric!r}"
            if no_strict:
                warnings.warn(f"{DATA_FILE}: dropped the {invalid_metric_msg}", stacklevel=2)
                paths.append(None)
            else:
                raise ValueError(f"{DATA_FILE}: {invalid_metric_msg}")

    refs = {}
    for raw_ref in list_in(raw, "refs"):
        ref = read_ref(raw_ref, paths, no_strict)
        invalid_ref_msg = f"invalid ref {raw_ref!r}"
        if ref is None and no_strict:
            warnings.warn(f"{DATA_FILE}: dropped the {invalid_ref_msg}", stacklevel=2)
        elif ref is None:
            raise ValueError(f"{DATA_FILE}: {invalid_ref_msg}")
        elif (key := ref_key(ref, no_strict)) is not None:
            refs[key] = ref

    present = {p for ref in refs.values() for p in ref["columns"]}
    return {p: u for p, u in units.items() if p in present}, refs


# Every metric in units has a column in some ref
def dump_data(units, refs):
    return {
        "metrics": [{"path": list(p), "unit": u} for p, u in units.items()],
        "refs": [
            {
                **{k: v for k, v in r.items() if k not in ("runs", "columns")},
                "runs": r["runs"],
                "values": [r["columns"].get(p) for p in units],
            }
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
def renormalize(units, refs, config):
    for path, unit in units.items():
        target = target_unit(config, match_unit_type(config.patterns, path))
        if target is None or unit == target:
            continue
        for ref in refs.values():
            if path in ref["columns"]:
                ref["columns"][path] = [
                    None if v is None else convert(v, unit, target)[0] for v in ref["columns"][path]
                ]
        units[path] = target


# (ref, run ID, {path: (value, unit)}, metadata) of the run, None if it's invalid
def read_run(input_file, validators, config):
    try:
        content = Path(input_file).read_bytes()
        metadata_content = metadata_path(input_file).read_bytes()
    except OSError as e:
        warnings.warn(f"Cannot read the run, skipping it: {e}", stacklevel=2)
        return None

    metadata = load_json_content(metadata_content)
    try:
        values = validate_run(load_json_content(content), metadata, validators, config)
    except ValueError as e:
        values = None
        warnings.warn(f"Cannot validate the run: {e}", stacklevel=2)

    if not values:
        return None
    ref = ref_of(metadata)
    if ref is None:
        return None
    return ref, source_id(content, metadata_content), values, metadata


# A path can be a metric in one run and a category in another, a single metrics file can't have such a clash
def check_paths(units):
    paths = set(units)
    for path in sorted(category_paths(paths) & paths):
        warnings.warn(f"'{join(path)}' is both a metric and a category", stacklevel=2)


def write_config(output_dir, config):
    data = {k: config.data[k] for k in DASHBOARD_KEYS if k in config.data}
    write_file(os.path.join(output_dir, CONFIG_FILE), json.dumps(data, indent=2) + "\n")


def serialize_json(output_dir, input_files, config, validators, open_prs=None, no_strict=False):
    os.makedirs(output_dir, exist_ok=True)
    data_path = os.path.join(output_dir, DATA_FILE)
    units, refs = read_data(data_path, no_strict)

    if open_prs is not None:
        remove_closed_prs(units, refs, open_prs)

    # Covers config changes even when no runs are added
    renormalize(units, refs, config)

    num_new_runs = 0
    for input_file in input_files:
        # Metadata files are read along with their metrics file (e.g. when matched by a glob)
        if is_metadata_file(input_file):
            continue

        run = read_run(input_file, validators, config)
        if not run:
            warnings.warn(f"Skipping run: {input_file}", stacklevel=2)
            continue

        run_ref, run_id, values, metadata = run
        if open_prs is not None and run_ref["kind"] == "pr" and run_ref["number"] not in open_prs:
            print(f"Skipping {input_file}: {ref_name(run_ref)} is not open", file=sys.stderr)
            continue

        ref = refs.setdefault(ref_key(run_ref), {**run_ref, "runs": [], "columns": {}})
        runs, columns = ref["runs"], ref["columns"]
        if any(r["id"] == run_id for r in runs):
            print(
                f"Skipping {input_file}: already merged (run {run_id} of {ref_name(ref)})",
                file=sys.stderr,
            )
            continue

        for path, (value, unit) in list(values.items()):
            stored = units.setdefault(path, unit)
            if stored != unit:
                try:
                    value, _ = convert(value, unit, stored)
                except ValueError as e:
                    value = None
                    warnings.warn(f"Skipping value for {path}: {e}", stacklevel=2)
                values[path] = (value, stored)
            columns.setdefault(path, [None] * len(runs))

        runs.append({"id": run_id, "metadata": metadata})
        for path, column in columns.items():
            column.append(values[path][0] if path in values else None)
        num_new_runs += 1

    check_paths(units)

    # Once, against all the serialized data
    metadata = [r["metadata"] for ref in refs.values() for r in ref["runs"]]
    if metadata:
        cross_check_config(list(units), metadata, config)

    write_file(data_path, json.dumps(dump_data(units, refs), separators=(",", ":")))
    write_config(output_dir, config)
    print(f"{num_new_runs} run(s) merged into {data_path}", file=sys.stderr)


def main():
    parser = argparse.ArgumentParser(
        description="Validate, normalize and append metrics.", allow_abbrev=False
    )
    parser.add_argument(
        "-o",
        "--output",
        required=True,
        type=Path,
        help="destination directory for the serialized data",
    )
    parser.add_argument("-c", "--config", required=True, type=Path, help="dashboard configuration")
    parser.add_argument(
        "-i",
        "--inputs",
        nargs="*",
        default=[],
        type=Path,
        help="metrics files, each with a '<name>.metadata.json' next to it",
    )
    parser.add_argument(
        "--open-prs",
        type=int,
        nargs="*",
        metavar="PR",
        help="open PRs; PRs not on this list are removed from the serialized data",
    )
    parser.add_argument(
        "--no-strict",
        action="store_true",
        help="When enabled, drops malformed entries from the pre-existing data.json as opposed to failing.",
    )
    parser.add_argument("-l", "--log-level", type=int, default=1)
    add_schema_arguments(parser)
    args = parser.parse_args()

    setup_logging(args.log_level)

    if args.output.exists() and not args.output.is_dir():
        parser.error("Output is not a directory.")

    try:
        config, validators = load_setup(args)
        serialize_json(args.output, args.inputs, config, validators, args.open_prs, args.no_strict)
    except OSError as e:  # Can't write the output
        sys.exit(f"Error: {e}")


if __name__ == "__main__":
    main()
