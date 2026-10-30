#!/usr/bin/env python3

# Unit normalization: converts values between compatible units

import re

from pint import UnitRegistry
from pint.errors import PintError
from pytimeparse2 import parse as parse_duration

ureg = UnitRegistry()

# Source units of duration values, e.g. "h:m:s", "d:h:m:s"
DURATION_UNIT = re.compile(r"[dhms](?::[dhms])+|duration")


def is_number(value):
    return isinstance(value, (int, float)) and not isinstance(value, bool)


def rounded(value, precision):
    return float(f"{value:.{precision}g}")


def normalize(value, src, dst, precision):
    # Convert duration to seconds
    if DURATION_UNIT.fullmatch(src):
        if not isinstance(value, str):
            raise ValueError(f"Expected a duration string for unit '{src}', got {value!r}")
        seconds = parse_duration(value)
        if seconds is None:
            raise ValueError(f"Unknown duration format '{value}'")
        value, src = rounded(seconds, precision), "s"

    # No conversion needed
    if src == dst:
        return value
    
    if not is_number(value):
        raise ValueError(f"Cannot convert non-numeric value {value!r} from '{src}' to '{dst}'")
    try:
        return rounded(ureg.Quantity(value, src).to(dst).magnitude, precision)
    except PintError as e:
        raise ValueError(f"Cannot convert unit '{src}' to '{dst}': {e}") from e