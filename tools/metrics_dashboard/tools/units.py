#!/usr/bin/env python3

# Unit normalization: converts values between compatible units

import re
from functools import cache

from pint import UnitRegistry
from pint.errors import PintError
from pytimeparse2 import parse as parse_duration

ureg = UnitRegistry()

# Precision of the converted values (significant digits)
PRECISION = 12

# Source units of duration values, e.g. "h:m:s", "d:h:m:s"
DURATION_UNIT = re.compile(r"[dhms](?::[dhms])+|duration")


def is_number(value):
    return isinstance(value, (int, float)) and not isinstance(value, bool)


def is_duration(unit):
    return DURATION_UNIT.fullmatch(unit) is not None


def rounded(value):
    return float(f"{value:.{PRECISION}g}")


@cache
def quantity(unit):
    try:
        return ureg.Quantity(unit)
    except Exception:
        return None


def is_supported(unit):
    return unit == "" or is_duration(unit) or quantity(unit) is not None


def stored_unit(src, tgt):
    # No target: the source unit is kept (durations are parsed to seconds)
    if tgt is None:
        return "s" if is_duration(src) else src
    if src == "" and tgt:
        raise ValueError(f"no source unit for the target unit '{tgt}'")
    return tgt


def normalize(value, src, dst):
    # Convert duration to seconds
    if is_duration(src):
        if not isinstance(value, str):
            raise ValueError(f"Expected a duration string for unit '{src}', got {value!r}")
        seconds = parse_duration(value)
        if seconds is None:
            raise ValueError(f"Unknown duration format '{value}'")
        value, src = rounded(seconds), "s"

    # No conversion needed
    if src == dst:
        return value
    if not is_number(value):
        raise ValueError(f"Cannot convert non-numeric value {value!r} from '{src}' to '{dst}'")

    src_q = quantity(src)
    dst_q = quantity(dst) if dst else ureg.Quantity(1)

    for unit, q in ((src, src_q), (dst, dst_q)):
        if q is None:
            raise ValueError(f"Cannot convert '{src}' to '{dst}': unit '{unit}' is not supported")

    try:
        return rounded((value * src_q / dst_q).to("dimensionless").magnitude)
    except PintError as e:
        raise ValueError(f"Cannot convert unit '{src}' to '{dst or 'unitless'}': {e}") from e


def convert(value, src, tgt):
    unit = stored_unit(src, tgt)
    return normalize(value, src, unit), unit