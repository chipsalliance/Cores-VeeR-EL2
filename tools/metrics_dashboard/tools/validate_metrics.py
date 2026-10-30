#!/usr/bin/env python3

# Validate a metrics JSON file.
# Optionally validates a companion config file (labels, target units) against the metrics file.

import argparse
import json
import sys
from collections import Counter
from pathlib import Path
from jsonschema.validators import validator_for

SCRIPT_DIR = Path(__file__).resolve().parent
RESERVED = {"units"}
# Joins node names into metric paths
CAT_SEPARATOR = "/"


def load(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


# Collect category names (dict values) and leaf names (metric names).
def walk(node, cats, metrics):
    for key, val in node.items():
        if isinstance(val, dict):
            cats.append(key)
            walk(val, cats, metrics)
        else:
            metrics.append(key)


def schema_errors(data, schema, what):
    cls = validator_for(schema)
    cls.check_schema(schema)
    return [
        f"{what} schema: {'/'.join(map(str, e.absolute_path)) or '<root>'}: {e.message}"
        for e in cls(schema).iter_errors(data)
    ]


def validate(data, schema, config=None, config_schema=None):
    errors, warnings, infos = [], [], []

    errors += schema_errors(data, schema, "metrics")
    if config is not None:
        errors += schema_errors(config, config_schema, "config")

    if errors:
        return errors, warnings, infos

    cats, metrics = [], []
    walk({k: v for k, v in data.items() if k not in RESERVED}, cats, metrics)
    n_metric, n_cat = Counter(metrics), Counter(cats)
    units = data.get("units", {})

    for name in sorted(n_metric.keys() | n_cat.keys()):
        if CAT_SEPARATOR in name:
            errors.append(f"name '{name}' contains the path separator '{CAT_SEPARATOR}'")

    for name in sorted(n_metric.keys() | n_cat.keys()):
        total = n_metric[name] + n_cat[name]
        if total > 1:
            kind = "metric" if n_metric[name] else "category"
            msg = f"name '{name}' occurs {total}x (shares one unit/label)"
            (warnings if kind == "metric" else infos).append(msg)

    for k in sorted(set(units) - set(n_metric)):
        errors.append(f"units: '{k}' is not a metric in the data")

    for k in sorted(set(n_metric) - set(units)):
        warnings.append(f"units: metric '{k}' has no unit")

    if config is not None:
        names = set(n_metric) | set(n_cat)
        label_map = config["labels"]

        for k in sorted(set(label_map) - names):
            errors.append(f"labels: '{k}' is not a category or metric in the data")

        for k in sorted(names - set(label_map)):
            warnings.append(f"labels: '{k}' has no label")

        for k in sorted(set(n_metric) - set(data["metadata"]) - set(config["units"])):
            errors.append(f"config units: metric '{k}' has no target unit")

    return errors, warnings, infos


def main():
    parser = argparse.ArgumentParser(description="Validate a metrics JSON file: schema check + units/labels cross-checks")
    parser.add_argument("file")
    parser.add_argument("--metrics-schema", default=SCRIPT_DIR / "metrics.schema.json", help="path to the metrics JSON Schema file")
    parser.add_argument("--config", help="path to the config JSON file (enables label and target unit checks)")
    parser.add_argument("--config-schema", default=SCRIPT_DIR / "config.schema.json", help="path to the config JSON Schema file (required with --config)")
    args = parser.parse_args()

    try:
        data = load(args.file)
        metrics_schema = load(args.metrics_schema)
        config = load(args.config) if args.config else None
        config_schema = load(args.config_schema) if args.config_schema else None
    except (OSError, json.JSONDecodeError) as e:
        print(f"ERROR: {e}", file=sys.stderr)
        return 1

    errors, warnings, infos = validate(data, metrics_schema, config, config_schema)
    for level, msgs in (("ERROR", errors), ("WARNING", warnings), ("INFO", infos)):
        for m in msgs:
            print(f"{level}: {m}")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
