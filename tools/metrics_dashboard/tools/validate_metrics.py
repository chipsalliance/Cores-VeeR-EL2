#!/usr/bin/env python3

# Validates a JSON metrics file and its metadata against the config file.

import argparse
import json
import sys
from collections import Counter
from pathlib import Path
from typing import NamedTuple

from jsonschema.exceptions import SchemaError
from jsonschema.validators import validator_for
from referencing import Registry, Resource

from messages import Messages, add_message_arguments
from unit_sources import CAT_SEPARATOR, compile_unit_types, join, match_unit_type, source_units
from units import convert

SCHEMA_DIR = Path(__file__).resolve().parent / "schemas"
# The metrics file's map of unit type -> unit, all the other top-level keys are categories
UNITS = "units"
# Metadata of '<name>.json' is read from '<name>.metadata.json'
METADATA_SUFFIX = ".metadata.json"
METADATA_PREFIX = "@"


def load(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


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
    for name in key[len(METADATA_PREFIX):].split(CAT_SEPARATOR):
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
        raise ValueError(f"{path}: invalid schema: {e.message}") from e
    return cls(schema, registry=Registry(retrieve=lambda uri: Resource.from_contents(load(path.parent / uri))))


def schema_errors(data, validator, what):
    return [f"{what} schema: {'/'.join(map(str, e.absolute_path)) or '<root>'}: {e.message}" for e in validator.iter_errors(data)]


def add_schema_arguments(parser):
    for name in ("metrics", "metadata", "config", "unit-types"):
        default = SCHEMA_DIR / f"{name.replace('-', '_')}.schema.json"
        parser.add_argument(f"--{name}-schema", default=default, type=Path, help=f"{name} JSON Schema (default: {default.name})")


# Config

class Config(NamedTuple):
    data: dict
    # Compiled patterns of the unit types file
    patterns: list


def load_config(path, config_validator, unit_types_validator):
    data = load(path)
    errors = schema_errors(data, config_validator, "config")
    if errors:
        raise ValueError("; ".join(errors))
    unit_types_path = Path(path).parent / data["unit_types_file"]
    unit_types = load(unit_types_path)
    errors = schema_errors(unit_types, unit_types_validator, f"unit types ({unit_types_path})")
    if errors:
        raise ValueError("; ".join(errors))
    return Config(data, compile_unit_types(unit_types))


def load_setup(args):
    config = load_config(args.config, load_schema(args.config_schema), load_schema(args.unit_types_schema))
    return config, {"metrics": load_schema(args.metrics_schema), "metadata": load_schema(args.metadata_schema)}


def target_unit(config, unit_type):
    return config.data["unit_types"].get(unit_type)


# Converts the values to the config's target units: {path: (value, unit)}
def convert_values(values, sources, config, msgs):
    converted = {}
    for path, value in values.items():
        src, unit_type = sources[path]
        try:
            converted[path] = convert(value, src, target_unit(config, unit_type))
        except ValueError as e:
            msgs.errors.append(f"{join(path)}: {e}")
    return converted


# Checks the config against the metric paths and the metadata of the runs
def cross_check_config(paths, metadata, config, msgs):
    data = config.data
    joined = {join(p) for p in paths}
    names = {name for p in paths for name in p}
    categories = {join(c) for c in category_paths(paths)}

    def check_metadata_field(field, key):
        if not any(metadata_value(m, key) is not None for m in metadata):
            msgs.warnings.append(f"config {field}: '{key}' matches no metadata field")

    # Check if specified labels exist in the metrics
    for key in sorted(data["labels"]):
        if is_metadata(key):
            check_metadata_field("labels", key)
        elif key not in names:
            msgs.warnings.append(f"config labels: '{key}' is not a category or metric")

    # Check if specified metrics exist in the metrics file
    for field in ("summary", "overview"):
        for key in data.get(field, []):
            if is_metadata(key):
                check_metadata_field(field, key)
            elif key not in joined:
                msgs.warnings.append(f"config {field}: '{key}' is not a metric in the data")

    # Check if specified unplottable metrics exist in the metrics file
    for key in data.get("unplottable", []):
        if is_metadata(key):
            msgs.warnings.append(f"config unplottable: '{key}' has no effect, metadata is never plotted")
        elif key not in (joined | categories if CAT_SEPARATOR in key else names):
            msgs.warnings.append(f"config unplottable: '{key}' matches nothing in the data")

    for key in sorted(data.get("units", {})):
        check_metadata_field("units", key)

    # Unit types of the data with and without a target unit
    used = set()
    for path in paths:
        try:
            used.add(match_unit_type(config.patterns, path))
        except ValueError:
            pass  # Reported along with the metrics
    used.discard(None)
    for key in sorted(used - set(data["unit_types"])):
        msgs.warnings.append(f"config unit_types: '{key}' has no target unit, its values are kept in their source units")
    for key in sorted(set(data["unit_types"]) - used):
        msgs.infos.append(f"config unit_types: '{key}' is not used by any metric in the data")


# Runs

# (values, sources) of the metrics file, None if it doesn't match the schema
def validate_metrics_file(data, validator, patterns, msgs):
    errors = schema_errors(data, validator, "metrics")
    if errors:
        msgs.errors += errors
        return None

    values = metric_values(data)
    paths = list(values)
    n_metric = Counter(p[-1] for p in paths)
    n_cat = Counter(c[-1] for c in category_paths(paths))

    for name in sorted(n_metric.keys() | n_cat.keys()):
        if CAT_SEPARATOR in name:
            msgs.errors.append(f"name '{name}' contains the path separator '{CAT_SEPARATOR}'")
        if is_metadata(name):
            msgs.errors.append(f"name '{name}' starts with '{METADATA_PREFIX}', reserved for metadata references")

        total = n_metric[name] + n_cat[name]
        if total > 1:
            msgs.infos.append(f"name '{name}' occurs {total}x (shares one label)")

    return values, source_units(data.get(UNITS, {}), paths, patterns, msgs)


# Runs come from the config's repository: branches pushed to it, PRs targeting it (possibly from forks)
def check_repository(metadata, config, msgs):
    field = "target_repository" if metadata["is_pr"] else "source_repository"
    repository = config.data["repository"]
    if metadata[field] != repository:
        msgs.errors.append(f"metadata: {field} '{metadata[field]}' is not the config's repository '{repository}'")


# Run: a metrics file and its metadata. Checks the run against the config, converting its values to the target units:
# {path: (value, unit)}, None if the metrics file doesn't match the schema
def validate_run(data, metadata, validators, config, msgs):
    metadata_errors = schema_errors(metadata, validators["metadata"], "metadata")
    msgs.errors += metadata_errors
    if not metadata_errors:
        check_repository(metadata, config, msgs)

    metrics = validate_metrics_file(data, validators["metrics"], config.patterns, msgs)
    return None if metrics is None else convert_values(*metrics, config, msgs)


def main():
    parser = argparse.ArgumentParser(description="Validate a JSON metrics file and its metadata against the config.", allow_abbrev=False)
    parser.add_argument("file", type=Path, help="metrics file")
    parser.add_argument("--metadata", type=Path, help=f"metadata file (default: the metrics file name with '{METADATA_SUFFIX}')")
    parser.add_argument("-c", "--config", required=True, type=Path, help="dashboard configuration")
    add_schema_arguments(parser)
    add_message_arguments(parser)
    args = parser.parse_args()

    try:
        config, validators = load_setup(args)
        data = load(args.file)
        metadata = load(args.metadata or metadata_path(args.file))
    except (OSError, ValueError) as e:
        sys.exit(f"Error: {e}")

    msgs = Messages()
    values = validate_run(data, metadata, validators, config, msgs)
    if values is not None:
        cross_check_config(list(values), [metadata], config, msgs)

    msgs.print(args.verbose)
    return 1 if msgs.errors else 0


if __name__ == "__main__":
    sys.exit(main())
