import pytest
import units as u

UNKNOWN_UNIT = r"^Cannot convert '"
INCOMPATIBLE_UNITS = r"^Cannot convert unit '"
NON_NUMERIC_CONVERT = r"^Cannot convert non-numeric"

@pytest.mark.parametrize(
    "src",
    ["1nW", "1e-9 W", "1e-9W", "10^3 pW", "10**3 pW", "0.001 uW", "nW", "1E-9 W"],
)
def test_scaled_and_scientific_source_units(src):
    assert u.convert(5, src, "nW") == (5, "nW")


@pytest.mark.parametrize(
    "value, src, tgt, expected",
    [
        (1, "um", "m", 1e-6),
        (2.5, "km", "m", 2500.0),
        (1500, "ms", "s", 1.5),
        (0.1, "m", "mm", 100.0),
        (-0.5, "ns", "ps", -500.0),
        (5, "1nW", "W", 5e-9),
        (42, "%", "", 0.42),
        (1, "1e-6 mm^2", "um^2", 1),
        (2, "1us", "10ns", 200),
        # Exponent without "^", with and without a leading scale
        (3, "um2", "um^2", 3),
        (3, "1um2", "um^2", 3),
        (3, "1e6um2", "mm^2", 3),
        (3, "10^3 um2", "um^2", 3000),
        (3, "um3", "um**3", 3),
        (3, "um2", "um²", 3),
        (2, "W/um2", "W/mm^2", 2e6),
        (2, "1/um2", "1/mm^2", 2e6),
        ("1:30:00", "h:m:s", "s", 5400.0),
        ("1:01:01:01", "d:h:m:s", "s", 90061.0),
        ("1h 30m", "duration", "s", 5400.0),
        (None, "m", "mm", None),
    ],
)
def test_convert(value, src, tgt, expected):
    assert u.convert(value, src, tgt) == (expected, tgt)


@pytest.mark.parametrize(
    "value, unit",
    [("aes", ""), (3, "cells"), ("text", "foo")],
)
def test_unit_persists(value, unit):
    assert u.convert(value, unit, unit) == (value, unit)


def test_precision():
    assert u.convert(1 / 3, "m", "mm", precision=3) == (333.0, "mm")


@pytest.mark.parametrize(
    "value, src, tgt, expected",
    [
        # No target unit: the value is kept in its source unit
        (5, "foo", None, (5, "foo")),
        ("text", "foo", None, ("text", "foo")),
        ("1:30:00", "h:m:s", None, (5400.0, "s")),
        # No source unit: the value is assumed to be in the target unit
        (5, None, "foo", (5, "foo")),
        ("text", None, "foo", ("text", "foo")),
        (5, None, None, (5, None)),
    ],
)
def test_missing_src_or_tgt_unit(value, src, tgt, expected):
    assert u.convert(value, src, tgt) == expected


@pytest.mark.parametrize(
    "value, src, tgt, message",
    [
        (4.3, "", "s", UNKNOWN_UNIT),
        (3, "ns", "cells", UNKNOWN_UNIT),
        (1.2, "cells", "LUT", UNKNOWN_UNIT),
        (4, "foo", "m", UNKNOWN_UNIT),
        (6.7, "s", "", INCOMPATIBLE_UNITS),
        (111, "ns", "V", INCOMPATIBLE_UNITS),
        (1, "m", "s", INCOMPATIBLE_UNITS),
        (3, "m", "", INCOMPATIBLE_UNITS),
        ("1:00:00", "h:m:s", "m", INCOMPATIBLE_UNITS),
        ("abc", "m", "mm", NON_NUMERIC_CONVERT),
        (True, "m", "mm", NON_NUMERIC_CONVERT),
        ([1], "m", "mm", NON_NUMERIC_CONVERT),
    ],
)
def test_unconvertible(value, src, tgt, message):
    with pytest.raises(ValueError, match=message):
        assert u.convert(value, src, tgt) == (None, tgt)

@pytest.mark.parametrize(
    "value, message",
    [
        (90, "Expected a duration string"),
        ("not a duration", "Unknown duration format"),
    ],
)
@pytest.mark.parametrize("tgt, stored", [(None, "s"), ("ms", "ms")])
def test_bad_duration(value, message, tgt, stored):
    with pytest.warns(UserWarning, match=message):
        assert u.convert(value, "h:m:s", tgt) == (None, stored)
