#!/usr/bin/env python3

# Unit normalization: converts values between compatible units

import logging
import re
import warnings
from functools import cache

from pint import UnitRegistry
from pint.errors import PintError
from pytimeparse2 import parse as parse_duration

log = logging.getLogger(__name__)

ureg = UnitRegistry()

# Precision of the converted values (significant digits)
PRECISION = 12

# Source units of duration values, e.g. "h:m:s", "d:h:m:s"
DURATION_UNIT = re.compile(r"[dhms](?::[dhms])+|duration")


def is_number(value):
    return isinstance(value, (int, float)) and not isinstance(value, bool)


def is_duration(unit):
    return unit is not None and DURATION_UNIT.fullmatch(unit) is not None


def rounded(value, precision=PRECISION):
    return float(f"{value:.{precision}g}")


def parse_time(value, unit):
    if not isinstance(value, str):
        warnings.warn(f"Expected a duration string for unit '{unit}', got {value!r}", stacklevel=2)
        return None
    seconds = parse_duration(value)
    if seconds is None:
        warnings.warn(f"Unknown duration format '{value}'", stacklevel=2)
    return seconds


# Leading scale of a source unit, e.g. "1" in "1um2", "1e-9" in "1e-9W", "10^3" in "10^3 pW"
SCALE = re.compile(r"\s*(?:10(?:\^|\*\*)[+-]?\d+|[+-]?(?:\d+\.?\d*|\.\d+)(?:[eE][+-]?\d+)?)")

# Exponent written right after a unit name, e.g. "um2" (= "um^2")
BARE_EXPONENT = re.compile(r"([^\W\d_]+)(\d+)")


def canonical(unit):
    """Rewrites unit notations pint does not parse, e.g. "1um2" -> "1um^2" """
    scale = SCALE.match(unit)
    split = scale.end() if scale else 0
    return unit[:split] + BARE_EXPONENT.sub(r"\1^\2", unit[split:])


@cache
def quantity(unit):
    try:
        return ureg.Quantity(canonical(unit))
    except Exception:
        return None


def is_supported(unit):
    return unit == "" or is_duration(unit) or quantity(unit) is not None


def normalize(value, src, dst, precision=PRECISION):
    if value is None:
        return None
    # No conversion needed
    if src == dst:
        return value
    if not is_number(value):
        raise ValueError(f"Cannot convert non-numeric value {value!r} from '{src}' to '{dst}'")

    src_q = quantity(src)
    dst_q = quantity(dst) if dst else ureg.Quantity(1)

    if None in [src_q, dst_q]:
        raise ValueError(f"Cannot convert '{src}' to '{dst}'")

    try:
        return rounded((value * src_q / dst_q).to("dimensionless").magnitude, precision)
    except PintError as e:
        raise ValueError(f"Cannot convert unit '{src}' to '{dst or 'unitless'}': {e}") from e


def convert(value, src, tgt, precision=PRECISION):
    if src is None:
        src = tgt
    elif is_duration(src):
        value, src = parse_time(value, src), "s"
        if value is not None:
            value = rounded(value, precision)
    unit = src if tgt is None else tgt
    return normalize(value, src, unit, precision), unit
