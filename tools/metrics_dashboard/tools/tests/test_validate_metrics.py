import sys
from pathlib import Path

import pytest
import validate_metrics as vm
from helpers import REPOSITORY, VALIDATORS, run_metadata, write_config, write_json
from unit_sources import compile_unit_types

UNIT_TYPES = {"a.x": "time"}

CONFIG = vm.Config(
    data={
        "repository": REPOSITORY,
        "main_branch": "develop",
        "labels": {"a": "A"},
        "unit_types_file": "unit_types.json",
        "unit_types": {"time": "s"},
        "summary": ["a.x"],
    },
    patterns=compile_unit_types(UNIT_TYPES),
)


@pytest.mark.parametrize(
    "name, expected",
    [("r.json", "r.metadata.json"), ("r", "r.metadata.json"), ("r.txt", "r.txt.metadata.json")],
)
def test_metadata_path(name, expected):
    assert vm.metadata_path(Path("dir") / name) == Path("dir") / expected


def test_metric_values_flattens_categories_and_skips_units():
    data = {"a": {"x": 1, "b": {"y": "s"}}, "c": {"z": [1]}, "units": {"time": "s"}}
    assert vm.metric_values(data) == {("a", "x"): 1, ("a", "b", "y"): "s", ("c", "z"): [1]}


@pytest.mark.parametrize("key, expected", [("@a.b", 1), ("@x", None), ("@c.d", None)])
def test_metadata_value(key, expected):
    assert vm.metadata_value({"a": {"b": 1}, "c": 2}, key) == expected


# Schemas


def test_invalid_schema(tmp_path):
    with pytest.warns(UserWarning, match="invalid schema"):
        vm.load_schema(write_json(tmp_path / "s.json", {"type": 5}))


@pytest.mark.parametrize(
    "metadata, message",
    [
        ({**run_metadata(), "pipeline_status": 4}, r"^metadata schema: pipeline_status: 4 is not"),
        ({**run_metadata(), "is_pr": True}, r"^metadata schema: <root>: '\w+' is a required"),
        ({**run_metadata(), "configuration": ""}, r"^metadata schema: configuration: '' should be non-empty"),
    ],
)
def test_schema_errors(metadata, message):
    with pytest.warns(UserWarning, match=message):
        vm.schema_errors(metadata, VALIDATORS["metadata"], "metadata")


# Config


def test_load_config(tmp_path):
    path = write_config(tmp_path, CONFIG.data, UNIT_TYPES)
    assert vm.load_config(path, VALIDATORS["config"], VALIDATORS["unit_types"]) == CONFIG


@pytest.mark.filterwarnings("ignore:.*Cannot read JSON|config schema")
@pytest.mark.parametrize(
    "content, expected",
    [
        (None, {}),  # Missing file
        ([], {}),
        ({**CONFIG.data, "labels": []}, {k: v for k, v in CONFIG.data.items() if k != "labels"}),
        ({**CONFIG.data, "main_branch": ""}, {k: v for k, v in CONFIG.data.items() if k != "main_branch"}),
        # No unit types: no unit type patterns
        ({"repository": REPOSITORY}, {"repository": REPOSITORY}),
    ],
)
def test_load_config_drops_invalid_entries(tmp_path, content, expected):
    path = tmp_path / "config.json"
    if content is not None:
        write_json(path, content)
    config = vm.load_config(path, VALIDATORS["config"], VALIDATORS["unit_types"])
    assert config == vm.Config(data=expected, patterns=[])


@pytest.mark.parametrize(
    "overrides",
    [
        {"labels": {"a": "A", "x": "X", "@source_branch": "B"}},
        {"unplottable": ["a", "x", "a.x"]},
    ],
)
def test_cross_check_config_accepts(overrides):
    config = CONFIG._replace(data={**CONFIG.data, **overrides})
    vm.cross_check_config([("a", "x")], [run_metadata()], config)


@pytest.mark.parametrize(
    "overrides, message",
    [
        ({"labels": {"zz": "Z"}}, "config labels: 'zz' is not a category or metric"),
        ({"labels": {"@nope": "N"}}, "config labels: '@nope' matches no metadata field"),
        ({"summary": ["a.q"]}, "config summary: 'a.q' is not a metric in the data"),
        ({"overview": ["@nope"]}, "config overview: '@nope' matches no metadata field"),
        ({"units": {"@nope": "s"}}, "config units: '@nope' matches no metadata field"),
        ({"unplottable": ["a.zz"]}, "config unplottable: 'a.zz' matches nothing in the data"),
        ({"unplottable": ["@source_branch"]}, "config unplottable: '@source_branch' has no effect"),
        ({"unit_types": {}}, "config unit_types: 'time' has no target unit"),
    ],
)
def test_cross_check_config(overrides, message):
    config = CONFIG._replace(data={**CONFIG.data, **overrides})
    with pytest.warns(UserWarning, match=message):
        vm.cross_check_config([("a", "x")], [run_metadata()], config)


# Runs


@pytest.mark.parametrize(
    "metadata, data",
    [
        (run_metadata(), CONFIG.data),
        # A PR from a fork targets the config's repository
        ({**run_metadata(pr=5), "source_repository": "fork/repo"}, CONFIG.data),
        # No repository in the config: reported with the config
        (run_metadata(repository="other/repo"), {}),
    ],
)
def test_check_repository_accepts(metadata, data):
    vm.check_repository(metadata, CONFIG._replace(data=data))


@pytest.mark.parametrize(
    "metadata, field",
    [
        (run_metadata(repository="other/repo"), "source_repository"),
        ({**run_metadata(pr=5), "target_repository": "other/repo"}, "target_repository"),
    ],
)
def test_check_repository_mismatch(metadata, field):
    with pytest.warns(UserWarning, match=f"^metadata: {field} 'other/repo' is not the config's"):
        vm.check_repository(metadata, CONFIG)


@pytest.mark.filterwarnings("ignore:unit types. 'a.*' has no unit type")
@pytest.mark.parametrize(
    "name, message",
    [
        ("x.y", "name 'x.y' contains the path separator '.'"),
        ("@x", "name '@x' starts with '@', reserved for metadata references"),
    ],
)
def test_reserved_names(name, message):
    with pytest.warns(UserWarning, match=message):
        vm.validate_metrics_file({"a": {name: 1}}, VALIDATORS["metrics"], CONFIG.patterns)


def test_validate_run_converts_to_the_target_units():
    data = {"a": {"x": 1500}, "units": {"time": "ms"}}
    assert vm.validate_run(data, run_metadata(), VALIDATORS, CONFIG) == {("a", "x"): (1.5, "s")}


def test_validate_run_invalid_metrics():
    with pytest.warns(UserWarning, match="^metrics schema: a: 1 is not of type 'object'"):
        assert vm.validate_run({"a": 1}, run_metadata(), VALIDATORS, CONFIG) is None


def test_validate_run_invalid_metadata():
    data = {"a": {"x": 1500}, "units": {"time": "ms"}}
    with pytest.warns(UserWarning, match="metadata schema"):
        assert vm.validate_run(data, {}, VALIDATORS, CONFIG) == {("a", "x"): (1.5, "s")}


# CLI


def run_main(monkeypatch, *args):
    monkeypatch.setattr(sys, "argv", ["validate_metrics.py", *map(str, args)])
    return vm.main()


@pytest.mark.parametrize("explicit_metadata", [False, True])
def test_main(tmp_path, monkeypatch, explicit_metadata):
    config_file = write_config(tmp_path / "setup", CONFIG.data, UNIT_TYPES)
    run = write_json(tmp_path / "r.json", {"a": {"x": 1}, "units": {"time": "s"}})
    metadata_name = "m.json" if explicit_metadata else "r.metadata.json"
    metadata = write_json(tmp_path / metadata_name, run_metadata())
    args = ["--metadata", metadata] if explicit_metadata else []

    assert run_main(monkeypatch, run, "-c", config_file, *args) == 0


def test_main_without_config(tmp_path, monkeypatch):
    run = write_json(tmp_path / "r.json", {"a": {"x": 1}})
    write_json(tmp_path / "r.metadata.json", run_metadata())
    with pytest.warns(UserWarning) as record:
        assert run_main(monkeypatch, run, "-c", tmp_path / "nope.json") == 0
    assert "Cannot read JSON" in str(record[0].message)
