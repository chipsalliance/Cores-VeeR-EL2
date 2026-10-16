"""Common OpenROAD warnings to suppress for different PDKs."""

ASAP7_SUPPRESSED_WARNINGS = [
    "ODB-0227",  # LEF file INFO output; excessively noisy.
    "ORD-0046",  # "-defer_connection has been deprecated."; accurate, but not relevant to the user.
    "STA-1140",  # "library ... already exists"; ASAP7 has duplicate names for some reason.
    "STA-1212",  # "timing group from output port"; ASAP7 has a lot of these warnings.
]