#!/usr/bin/env python3

# Source units of the metrics in a metrics file: the unit types file maps metric paths to unit types,
# the metrics file's 'units' maps unit types to units.

import re
from typing import NamedTuple

from units import is_supported

# Joins node names into metric paths
CAT_SEPARATOR = "."
WILDCARD = "*"


class Source(NamedTuple):
    unit: str
    type: str | None


class Pattern(NamedTuple):
    key: str
    type: str
    regex: re.Pattern
    # Exact paths win, then the patterns with more (non-wildcard) segments
    rank: tuple[bool, int]


def join(path):
    return CAT_SEPARATOR.join(path)


def compile_unit_types(unit_types):
    patterns = []
    for key, unit_type in unit_types.items():
        segments = key.split(CAT_SEPARATOR)
        parts = [r"[^.]+(?:\.[^.]+)*" if s == WILDCARD else re.escape(s) for s in segments]
        patterns.append(Pattern(
            key=key,
            type=unit_type,
            regex=re.compile(r"\.".join(parts)),
            rank=(WILDCARD not in segments, sum(s != WILDCARD for s in segments)),
        ))
    return patterns


# Unit type of the path, None if no pattern matches
def match_unit_type(patterns, path, msgs=None):
    joined = join(path)
    matches = [p for p in patterns if p.regex.fullmatch(joined)]

    if not matches:
        return None

    best = max(matches, key=lambda p: p.rank)
    tied = [p for p in matches if p.rank == best.rank]

    if len({p.type for p in tied}) > 1:
        listed = ", ".join(f"'{p.key}' ({p.type})" for p in tied)
        raise ValueError(f"Type conflict for matched metrics: {listed}")

    if msgs is not None and (len(matches) > 1 or WILDCARD in best.key):
        over = "".join(f", over '{p.key}' ({p.type})" for p in matches if p is not best)
        msgs.infos.append(f"unit types: '{joined}' is '{best.type}' (by '{best.key}'{over})")
    return best.type


def source_units(units, paths, patterns, msgs):
    sources = {}
    for path in paths:
        try:
            unit_type = match_unit_type(patterns, path, msgs)
        except ValueError as e:
            msgs.errors.append(f"unit types: '{join(path)}': {e}")
            sources[path] = Source("", None)
            continue

        if unit_type is None:
            msgs.warnings.append(f"unit types: '{join(path)}' has no unit type")
            unit = ""
        elif unit_type in units:
            unit = units[unit_type]
        else:
            msgs.warnings.append(f"units: unit type '{unit_type}' of '{join(path)}' has no unit")
            unit = ""

        # Custom units are kept as labels
        if not is_supported(unit):
            msgs.warnings.append(f"'{join(path)}': unit '{unit}' is not supported, values are kept as is")
        sources[path] = Source(unit, unit_type)

    used = {s.type for s in sources.values()}
    for unit_type in sorted(set(units) - used):
        msgs.infos.append(f"units: unit type '{unit_type}' is not used by any metric")

    for p in patterns:
        if not any(p.regex.fullmatch(join(path)) for path in paths):
            msgs.infos.append(f"unit types: '{p.key}' matches nothing in the data")

    return sources
