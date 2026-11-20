import logging
import re

import pytest
import unit_sources as us

# Matching


@pytest.mark.parametrize(
    "unit_types, path, expected",
    [
        ({"*.area": "area"}, ("x", "area"), "area"),
        ({"*.area": "area"}, ("x", "y", "area"), "area"),
        ({"*.area": "area"}, ("area",), None),
        ({"s.*.area": "area"}, ("s", "top", "area"), "area"),
        ({"s.*.area": "area"}, ("s", "top", "sub", "area"), "area"),
        ({"s.*.area": "area"}, ("s", "area"), None),
        ({"s.*": "area"}, ("s", "x"), "area"),
        ({"s.*": "area"}, ("s",), None),
    ],
)
def test_wildcard_matches_one_or_more_segments(unit_types, path, expected):
    assert us.match_unit_type(us.compile_unit_types(unit_types), path) == expected


@pytest.mark.parametrize(
    "unit_types, path, expected",
    [
        ({"s.design.area": "area", "*.area": "length"}, ("s", "design", "area"), "area"),
        ({"s.design.area": "area", "s.*.area": "length"}, ("s", "design", "area"), "area"),
        ({"s.modules.*.area": "area", "*.area": "length"}, ("s", "modules", "top", "area"), "area"),
        ({"*.modules.*.area": "area", "*.area": "length"}, ("s", "modules", "top", "area"), "area"),
        ({"*.modules.*.area": "area", "*.area": "length"}, ("s", "top", "area"), "length"),
    ],
)
def test_most_specific_pattern_wins(unit_types, path, expected):
    assert us.match_unit_type(us.compile_unit_types(unit_types), path) == expected


@pytest.mark.parametrize(
    "path, expected",
    [
        (("a", "x", "b", "y", "c"), "multi"),
        (("a", "x", "b", "y", "z", "c"), "multi"),
        (("a", "x", "y", "b", "z", "c"), "multi"),
        (("a", "b", "c"), None),
        (("a", "x", "b", "c"), None),
    ],
)
def test_several_wildcards(path, expected):
    patterns = us.compile_unit_types({"a.*.b.*.c": "multi"})
    assert us.match_unit_type(patterns, path) == expected


@pytest.mark.parametrize("patterns", [None, []])
def test_no_patterns_match_nothing(patterns):
    assert us.match_unit_type(patterns, ("s", "area")) is None


@pytest.mark.parametrize(
    "unit_types, path",
    [
        ({"*.design.n": "a", "synth.*.n": "b"}, ("synth", "design", "n")),
        ({"*.n": "a", "synth.*": "b"}, ("synth", "design", "n")),
    ],
)
def test_tie_of_different_types(unit_types, path):
    with pytest.warns(UserWarning, match="^Type conflict for matched metrics: "):
        assert us.match_unit_type(us.compile_unit_types(unit_types), path) is None


@pytest.mark.parametrize(
    "unit_types, path, expected",
    [
        ({"*.design.n": "a", "synth.*.n": "a"}, ("synth", "design", "n"), "a"),
        ({"*.n": "a", "synth.*": "a"}, ("synth", "design", "n"), "a"),
    ],
)
def test_tie_of_the_same_type(unit_types, path, expected):
    assert us.match_unit_type(us.compile_unit_types(unit_types), path) == expected


@pytest.mark.parametrize(
    "key, path, expected",
    [
        ("s.\\top+1.area", ("s", "\\top+1", "area"), "t"),
        ("s.\\top+1.area", ("s", "\\topp1", "area"), None),
        ("s.(a|b)", ("s", "(a|b)"), "t"),
        ("s.(a|b)", ("s", "a"), None),
        ("s.[x]", ("s", "x"), None),
        ("a*.b", ("a*", "b"), "t"),
        ("a*.b", ("ab", "b"), None),
    ],
)
def test_special_characters(key, path, expected):
    assert us.match_unit_type(us.compile_unit_types({key: "t"}), path) == expected


# Source units


@pytest.mark.parametrize(
    "unit_types, units",
    [
        (None, {}),
        ({}, {"area": "um^2"}),
        ({"s.other": "area"}, {"area": "um^2"}),
    ],
)
def test_path_without_unit_type(caplog, unit_types, units):
    patterns = None if unit_types is None else us.compile_unit_types(unit_types)

    with caplog.at_level(logging.INFO):
        sources = us.source_units(units, [("s", "x")], patterns)
    any(re.match(r"^unit types: 's\.x' has no unit type$", m) for m in caplog.messages)
    assert sources == {("s", "x"): us.Source("", None)}


@pytest.mark.parametrize(
    "unit_type, unit",
    [
        ("area", "1um^2"),
        ("power", "1nW"),
        ("percentage", "%"),
        ("unitless", ""),
        ("time", None),
        ("count", "cells"),
    ],
)
def test_source_unit_by_type(unit_type, unit):
    patterns = us.compile_unit_types({"s.x": unit_type})
    sources = us.source_units({unit_type: unit}, [("s", "x")], patterns)
    assert sources == {("s", "x"): us.Source(unit, unit_type)}


def test_units_of_unused_types_are_ignored():
    patterns = us.compile_unit_types({"s.x": "area"})
    sources = us.source_units({"area": "um^2", "voltage": "V"}, [("s", "x")], patterns)
    assert sources == {("s", "x"): us.Source("um^2", "area")}


@pytest.mark.parametrize("units", [{}, {"power": "nW"}])
def test_unit_type_without_unit(units):
    patterns = us.compile_unit_types({"s.x": "area"})
    with pytest.warns(UserWarning, match=r"^units: unit type 'area' of 's\.x' has no unit$"):
        sources = us.source_units(units, [("s", "x")], patterns)
    assert sources == {("s", "x"): us.Source("", "area")}


def test_each_path_gets_its_own_source():
    patterns = us.compile_unit_types({"s.x": "area", "s.y": "power"})
    sources = us.source_units({"area": "um^2", "power": "nW"}, [("s", "x"), ("s", "y")], patterns)
    assert sources == {
        ("s", "x"): us.Source("um^2", "area"),
        ("s", "y"): us.Source("nW", "power"),
    }
