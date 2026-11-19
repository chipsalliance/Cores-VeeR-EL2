import json

import pytest
import serialize_json as sj
from helpers import REPOSITORY, VALIDATORS, run_metadata, write_config, write_json, write_run
from unit_sources import compile_unit_types
from validate_metrics import Config

EMPTY_DATA = {"metrics": [], "refs": []}

UNIT_TYPES = {"a.x": "time", "a.y": "time", "a.len": "length"}

CONFIG = Config(
    data={"repository": REPOSITORY, "labels": {}, "unit_types": {"time": "s"}},
    patterns=compile_unit_types(UNIT_TYPES),
)


def serialize(tmp_path, files, **kwargs):
    out = tmp_path / "out"
    sj.serialize_json(out, files, CONFIG, VALIDATORS, **kwargs)
    return json.loads((out / sj.DATA_FILE).read_text())


def make_run(tmp_path, name, a, *, pr=None, units=None):
    metrics = {"a": a, "units": units or {"time": "s"}}
    return write_run(tmp_path / "in", name, metrics, run_metadata(pr=pr))


def test_source_id():
    assert sj.source_id(b"ab", b"c") != sj.source_id(b"a", b"bc")


# Serialized data

X = {"path": ["a", "x"], "unit": "s"}
RUN = {"id": 1, "metadata": {}}
MAIN = {"kind": "branch", "name": "main"}
VALID = {"metrics": [X], "refs": [{**MAIN, "runs": [RUN], "values": [[1]]}]}


def test_read_dump(tmp_path):
    assert sj.dump_data(*sj.read_data(write_json(tmp_path / "data.json", VALID))) == VALID


@pytest.mark.parametrize("no_strict", [True, False])
@pytest.mark.parametrize(
    "raw, expected, message",
    [
        ([], EMPTY_DATA, "isn't an object"),
        ({"metrics": 1, "refs": []}, EMPTY_DATA, "isn't a list"),
        (
            {
                "metrics": [{"path": ["a", "y"]}, X],
                "refs": [{**MAIN, "runs": [RUN], "values": [[2], [1]]}],
            },
            VALID,
            "invalid metric",
        ),
        (
            {"metrics": [X], "refs": [{**MAIN, "runs": 1, "values": [[1]]}]},
            EMPTY_DATA,
            "invalid ref",
        ),
        (
            {"metrics": [X], "refs": [{"kind": "branch", "runs": [RUN], "values": [[1]]}]},
            EMPTY_DATA,
            "Cannot associate metrics",
        ),
        (
            {"metrics": [X], "refs": [{**MAIN, "runs": [{"id": 2}, RUN], "values": [[2, 1]]}]},
            VALID,
            "invalid run",
        ),
        (
            {"metrics": [X], "refs": [{**MAIN, "runs": [RUN], "values": [[1, 2]]}]},
            {"metrics": [], "refs": [{**MAIN, "runs": [RUN], "values": []}]},
            "invalid values of 'a.x'",
        ),
    ],
)
def test_read_data(tmp_path, no_strict, raw, expected, message):
    path = write_json(tmp_path / "data.json", raw)
    exp = (
        pytest.warns(UserWarning, match=message)
        if no_strict
        else pytest.raises(ValueError, match=message)
    )
    with exp:
        assert sj.dump_data(*sj.read_data(path, no_strict)) == expected


@pytest.mark.parametrize(
    "path, unit, column, expected_unit, expected_column",
    [
        (("a", "x"), "ms", [1, None, 2], "s", [0.001, None, 0.002]),
        (("a", "x"), "s", [5], "s", [5]),
        (("a", "len"), "m", [7], "m", [7]),
    ],
)
def test_renormalize(path, unit, column, expected_unit, expected_column):
    units = {path: unit}
    refs = {"main": {"columns": {path: column}}, "dev": {"columns": {}}}  # 'dev' lacks the metric
    sj.renormalize(units, refs, CONFIG)
    assert units == {path: expected_unit}
    assert refs == {"main": {"columns": {path: expected_column}}, "dev": {"columns": {}}}


def test_renormalize_unconvertible():
    units = {("a", "x"): "m"}
    refs = {"main": {"columns": {("a", "x"): [1]}}}

    with pytest.raises(ValueError, match=r"Cannot convert"):
        sj.renormalize(units, refs, CONFIG)


def test_write_config_keeps_only_dashboard_keys(tmp_path):
    dashboard = {key: [] for key in sj.DASHBOARD_KEYS}
    sj.write_config(tmp_path, Config(data={**dashboard, "repository": "r"}, patterns=[]))
    assert json.loads((tmp_path / sj.CONFIG_FILE).read_text()) == dashboard


# Merging runs


@pytest.mark.parametrize(
    "pr, expected",
    [
        # Same ref: a column per metric, a value per run
        (None, [[[1, None], [None, 2]]]),
        # Different refs: none for missing metrics
        (5, [[[1], None], [None, [2]]]),
    ],
)
def test_values_are_aligned_to_the_metrics(tmp_path, pr, expected):
    r1 = make_run(tmp_path, "r1", {"x": 1})
    r2 = make_run(tmp_path, "r2", {"y": 2}, pr=pr)
    data = serialize(tmp_path, [r1, r2])

    assert [m["path"] for m in data["metrics"]] == [["a", "x"], ["a", "y"]]
    assert [r["values"] for r in data["refs"]] == expected


def test_re_adding_the_same_run_is_a_noop(tmp_path):
    r = make_run(tmp_path, "r", {"x": 1})
    serialize(tmp_path, [r])
    assert serialize(tmp_path, [r])["refs"][0]["values"] == [[1]]


@pytest.mark.parametrize(
    "metrics, metadata, message",
    [
        ({"a": 1}, run_metadata(), "metrics schema"),  # 'a' isn't a category
        ({"a": {"x": 1}, "units": {"time": "s"}}, None, "Cannot read the run"),  # No metadata file
        ({"a": {"x": 1}, "units": {"time": "s"}}, "{not json", "Missing metadata keys"),
        ({"a": {"x": 1}, "units": {"time": "s"}}, {"is_pr": True}, "Missing metadata keys"),
    ],
)
@pytest.mark.parametrize("open_prs", [None, [5]])
def test_invalid_run_is_skipped(tmp_path, metrics, metadata, message, open_prs):
    run = write_run(tmp_path / "in", "r", metrics, metadata)
    with pytest.warns(UserWarning) as record:
        assert serialize(tmp_path, [run], open_prs=open_prs) == EMPTY_DATA
    assert any(message in str(w.message) for w in record)


@pytest.mark.parametrize(
    "open_prs, refs, metrics",
    [
        ([5], ["main", 5], [["a", "x"], ["a", "y"]]),
        # Closed PRs are dropped along with their unique metrics
        ([7], ["main"], [["a", "x"]]),
        # No open PRs
        ([], ["main"], [["a", "x"]]),
    ],
)
@pytest.mark.parametrize("already_serialized", [False, True])
def test_only_open_prs_are_kept(tmp_path, open_prs, refs, metrics, already_serialized):
    runs = [make_run(tmp_path, "m", {"x": 1}), make_run(tmp_path, "p", {"y": 2}, pr=5)]
    if already_serialized:
        serialize(tmp_path, runs)
        runs = []
    data = serialize(tmp_path, runs, open_prs=open_prs)
    assert [r.get("name", r.get("number")) for r in data["refs"]] == refs
    assert [m["path"] for m in data["metrics"]] == metrics


@pytest.mark.parametrize(
    "args, refs",
    [
        ([], ["main", 5]),
        (["--open-prs"], ["main"]),
        (["--open-prs", "5"], ["main", 5]),
    ],
)
def test_open_prs(tmp_path, monkeypatch, args, refs):
    runs = [make_run(tmp_path, "m", {"x": 1}), make_run(tmp_path, "p", {"y": 2}, pr=5)]
    serialize(tmp_path, runs)
    config = write_config(
        tmp_path / "config",
        {**CONFIG.data, "unit_types_file": "units.json"},
        UNIT_TYPES,
    )
    out = tmp_path / "out"
    monkeypatch.setattr("sys.argv", ["serialize_json.py", "-o", str(out), "-c", str(config), *args])
    sj.main()
    data = json.loads((out / sj.DATA_FILE).read_text())
    assert [r.get("name", r.get("number")) for r in data["refs"]] == refs


# Only values without a target unit can differ in units between runs
@pytest.mark.filterwarnings("ignore:config unit_types. 'length' has no target unit")
def test_unit_mismatch_converts_to_the_stored_unit(tmp_path):
    r1 = make_run(tmp_path, "r1", {"len": 1}, units={"length": "m"})
    r2 = make_run(tmp_path, "r2", {"len": 2}, units={"length": "mm"})
    data = serialize(tmp_path, [r1, r2])
    assert data["metrics"] == [{"path": ["a", "len"], "unit": "m"}]
    assert data["refs"][0]["values"] == [[1, 0.002]]


@pytest.mark.filterwarnings("ignore:unit types. 'a.x.y' has no unit type")
def test_metric_and_category_clash(tmp_path):
    r1 = make_run(tmp_path, "r1", {"x": 1})
    r2 = make_run(tmp_path, "r2", {"x": {"y": 2}})
    with pytest.warns(UserWarning, match="'a.x' is both a metric and a category"):
        serialize(tmp_path, [r1, r2])
