#!/usr/bin/env python3

# Validates a JSON metrics file and its metadata against the config file.

import argparse
import json
import logging
import sys
import warnings
from collections import Counter
from pathlib import Path
from typing import NamedTuple

from jsonschema.exceptions import SchemaError
from jsonschema.validators import validator_for
from referencing import Registry, Resource
from unit_sources import (
    CAT_SEPARATOR,
    compile_unit_types,
    join,
    match_unit_type,
    source_units,
)
from units import convert

log = logging.getLogger(__name__)

SCHEMA_DIR = Path(__file__).resolve().parent / "schemas"
# The metrics file's map of unit type -> unit, all the other top-level keys are categories
UNITS = "units"
# Metadata of '<name>.json' is read from '<name>.metadata.json'
METADATA_SUFFIX = ".metadata.json"
METADATA_PREFIX = "@"


def load(path):
    content = {}
    try:
        content = json.loads(Path(path).read_text(encoding="utf-8"))
    except Exception as e:
        warnings.warn(f"{path}: Cannot read JSON: {e}", stacklevel=2)
    return content


def is_metadata_file(path):
    return Path(path).name.endswith(METADATA_SUFFIX)


def metadata_path(metrics_path):
    path = Path(metrics_path)
    stem = path.name[: -len(".json")] if path.name.endswith(".json") else path.name
    return path.with_name(stem + METADATA_SUFFIX)


# Collect (path, value) for every leaf metric
def flatten(node, prefix=()):
    for key, val in node.items():
        path = (*prefix, key)
        if isinstance(val, dict):
            yield from flatten(val, path)
        else:
            yield path, val


# {path (tuple of node names): value} of every metric in a metrics file
def metric_values(data):
    return dict(flatten({k: v for k, v in data.items() if k != UNITS}))


def category_paths(paths):
    return {p[:i] for p in paths for i in range(1, len(p))}


def is_metadata(key):
    return key.startswith(METADATA_PREFIX)


def metadata_value(metadata, key):
    value = metadata
    for name in key[len(METADATA_PREFIX) :].split(CAT_SEPARATOR):
        if not isinstance(value, dict) or name not in value:
            return None
        value = value[name]
    return value


# Schemas


# Validator of the schema, '$ref's to other schemas are resolved relative to its file
def load_schema(path):
    path = Path(path)
    schema = load(path)
    cls = validator_for(schema)
    try:
        cls.check_schema(schema)
    except SchemaError as e:
        warnings.warn(f"{path}: invalid schema: {e.message}", stacklevel=2)
        # raise ValueError(f"{path}: invalid schema: {e.message}") from e
    return cls(
        schema,
        registry=Registry(retrieve=lambda uri: Resource.from_contents(load(path.parent / uri))),
    )


def schema_errors(data, validator, what):
    errors = list(validator.iter_errors(data))
    for e in errors:
        warnings.warn(
            f"{what} schema: {'/'.join(map(str, e.absolute_path)) or '<root>'}: {e.message}",
            stacklevel=2,
        )
    return errors


def add_schema_arguments(parser):
    for name in ("metrics", "metadata", "config", "unit-types"):
        default = SCHEMA_DIR / f"{name.replace('-', '_')}.schema.json"
        parser.add_argument(
            f"--{name}-schema",
            default=default,
            type=Path,
            help=f"{name} JSON Schema (default: {default.name})",
        )


# Config


class Config(NamedTuple):
    data: dict
    # Compiled patterns of the unit types file
    patterns: list


# Top-level entries with schema errors are dropped, the missing ones are treated as empty
def valid_entries(data, validator, what):
    errors = schema_errors(data, validator, what)
    if not isinstance(data, dict):
        return {}
    invalid = {e.absolute_path[0] for e in errors if e.absolute_path}
    return {key: value for key, value in data.items() if key not in invalid}


def load_config(path, config_validator, unit_types_validator):
    data = valid_entries(load(path), config_validator, "config")

    unit_types = {}
    if "unit_types_file" in data:
        unit_types_path = Path(path).parent / data["unit_types_file"]
        what = f"unit types ({unit_types_path})"
        unit_types = valid_entries(load(unit_types_path), unit_types_validator, what)
    return Config(data, compile_unit_types(unit_types))


def load_setup(args):
    config = load_config(
        args.config, load_schema(args.config_schema), load_schema(args.unit_types_schema)
    )
    return config, {
        "metrics": load_schema(args.metrics_schema),
        "metadata": load_schema(args.metadata_schema),
    }


def target_unit(config, unit_type):
    return config.data.get("unit_types", {}).get(unit_type)


# Converts the values to the config's target units: {path: (value, unit)}
def convert_values(values, sources, config):
    converted = {}
    for path, value in values.items():
        src, unit_type = sources[path]
        converted[path] = convert(value, src, target_unit(config, unit_type))
    return converted


# Checks the config against the metric paths and the metadata of the runs
def cross_check_config(paths, metadata, config):
    data = config.data
    joined = {join(p) for p in paths}
    names = {name for p in paths for name in p}
    categories = {join(c) for c in category_paths(paths)}

    def check_metadata_field(field, key):
        if not any(metadata_value(m, key) is not None for m in metadata):
            warnings.warn(f"config {field}: '{key}' matches no metadata field", stacklevel=2)

    # Check if specified labels exist in the metrics
    for key in sorted(data.get("labels", {})):
        if is_metadata(key):
            check_metadata_field("labels", key)
        elif key not in names:
            warnings.warn(f"config labels: '{key}' is not a category or metric", stacklevel=2)

    # Check if specified metrics exist in the metrics file
    for field in ("summary", "overview"):
        for key in data.get(field, []):
            if is_metadata(key):
                check_metadata_field(field, key)
            elif key not in joined:
                warnings.warn(f"config {field}: '{key}' is not a metric in the data", stacklevel=2)

    # Check if specified unplottable metrics exist in the metrics file
    for key in data.get("unplottable", []):
        if is_metadata(key):
            warnings.warn(
                f"config unplottable: '{key}' has no effect, metadata is never plotted",
                stacklevel=2,
            )
        elif key not in (joined | categories if CAT_SEPARATOR in key else names):
            warnings.warn(f"config unplottable: '{key}' matches nothing in the data", stacklevel=2)

    for key in sorted(data.get("units", {})):
        check_metadata_field("units", key)

    # Unit types of the data with and without a target unit
    # Type conflicts (None) are reported along with the metrics
    used = {match_unit_type(config.patterns, path) for path in paths}
    used.discard(None)
    for key in sorted(used - set(data.get("unit_types", {}))):
        warnings.warn(
            f"config unit_types: '{key}' has no target unit, its values are kept in their source units",
            stacklevel=2,
        )

    for key in sorted(set(data.get("unit_types", {})) - used):
        log.info(f"config unit_types: '{key}' is not used by any metric in the data")


# Runs


# (values, sources) of the metrics file, None if it doesn't match the schema
def validate_metrics_file(data, validator, patterns):
    fail = schema_errors(data, validator, "metrics")

    if fail:
        return None

    values = metric_values(data)
    paths = list(values)
    n_metric = Counter(p[-1] for p in paths)
    n_cat = Counter(c[-1] for c in category_paths(paths))

    for name in sorted(n_metric.keys() | n_cat.keys()):
        if CAT_SEPARATOR in name:
            warnings.warn(
                f"name '{name}' contains the path separator '{CAT_SEPARATOR}'", stacklevel=2
            )
        if is_metadata(name):
            warnings.warn(
                f"name '{name}' starts with '{METADATA_PREFIX}', reserved for metadata references",
                stacklevel=2,
            )

        total = n_metric[name] + n_cat[name]

        if total > 1:
            log.info(f"name '{name}' occurs {total}x (shares one label)")

    return values, source_units(data.get(UNITS, {}), paths, patterns)


# Runs come from the config's repository: branches pushed to it, PRs targeting it (possibly from forks)
def check_repository(metadata, config):
    field = "target_repository" if metadata["is_pr"] else "source_repository"
    repository = config.data.get("repository")
    if repository is not None and metadata[field] != repository:
        warnings.warn(
            f"metadata: {field} '{metadata[field]}' is not the config's repository '{repository}'",
            stacklevel=2,
        )


# Run: a metrics file and its metadata. Checks the run against the config, converting its values to the target units:
# {path: (value, unit)}, None if the metrics file doesn't match the schema
def validate_run(data, metadata, validators, config):
    fail = schema_errors(metadata, validators["metadata"], "metadata")

    if not fail:
        check_repository(metadata, config)

    metrics = validate_metrics_file(data, validators["metrics"], config.patterns)
    return None if not metrics else convert_values(*metrics, config)


def main():
    parser = argparse.ArgumentParser(
        description="Validate a JSON metrics file and its metadata against the config.",
        allow_abbrev=False,
    )
    parser.add_argument("file", type=Path, help="metrics file")
    parser.add_argument(
        "--metadata",
        type=Path,
        help=f"metadata file (default: the metrics file name with '{METADATA_SUFFIX}')",
    )
    parser.add_argument("-c", "--config", required=True, type=Path, help="dashboard configuration")
    add_schema_arguments(parser)
    args = parser.parse_args()

    config, validators = load_setup(args)
    data = load(args.file)
    metadata = load(args.metadata or metadata_path(args.file))

    values = validate_run(data, metadata, validators, config)
    if values is not None:
        cross_check_config(list(values), [metadata], config)

    return 0


if __name__ == "__main__":
    sys.exit(main())
