#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 Google LLC
#
# Convert Verilator `user` coverage (`cover property` entries in `coverage.dat`)
# into LCOV `.info` format (`*_fcov.info`) with `BRDA` records for Coverview
# Table View and `info-process`.
# Author: Samip Modi (samipmodi@google.com)
"""Convert Verilator user coverage (coverage.dat) to LCOV .info with BRDA."""

import argparse
from collections import OrderedDict
import os
import re
import sys

VERSION = "1.0.0"

DAT_ROW_RE = re.compile(r"^C\s+'(?P<payload>.*)'\s+(?P<count>\d+)\s*$")
SECTION_COMMENT_RE = re.compile(r"^\s*//\s*(?P<num>\d+)\.\s*(?P<title>.+?)\s*$")
STOP_SCAN_RE = re.compile(r"^\s*`(?:else|ifndef|ifdef)\b")


def parse_args():
    """Parse command line arguments."""
    parser = argparse.ArgumentParser(
        description=(
            "Convert Verilator user functional coverage (coverage.dat) "
            "into LCOV .info format with BRDA entries for Coverview."
        )
    )
    parser.add_argument(
        "--dat",
        required=True,
        help="Path to input Verilator coverage.dat file.",
    )
    parser.add_argument(
        "--output",
        required=True,
        help="Path to output LCOV .info file (e.g. coverage_test_fcov.info).",
    )
    parser.add_argument(
        "--repo-root",
        default=None,
        help="Optional repository root to locate .sv source files.",
    )
    parser.add_argument(
        "--test-name",
        default="verilator_coverage",
        help="Test name written to LCOV TN: header.",
    )
    return parser.parse_args()


def parse_dat_payload(payload):
    """Parse \\x01key\\x02value pairs inside a Verilator coverage.dat row."""
    fields = {}
    for item in payload.split("\x01"):
        if "\x02" in item:
            key, val = item.split("\x02", 1)
            fields[key] = val
    return fields


def resolve_source_path(source_file, repo_root):
    """Resolve source file on disk, optionally rebasing onto repo_root."""
    if os.path.isfile(source_file):
        return source_file
    if repo_root:
        for marker in ("testbench/", "verification/", "design/"):
            pos = source_file.find(marker)
            if pos != -1:
                candidate = os.path.join(repo_root, source_file[pos:])
                if os.path.isfile(candidate):
                    return candidate
    return source_file


def sanitize_group_part(text):
    """Sanitize section header text so it is safe before '.' in BRDA."""
    # Coverview splits BRDA names at the first '.' and LCOV splits fields at ','
    cleaned = text.replace(".", " -").replace(",", " /")
    cleaned = re.sub(r"\s+", " ", cleaned).strip()
    return cleaned


def find_section_group(src_lines, line_no, module_name):
    """Find the nearest preceding '// <N>. <Title>' comment above line_no."""
    if not src_lines or line_no < 1 or line_no > len(src_lines):
        return f"{module_name}::cover_properties"

    for idx in range(line_no - 2, -1, -1):
        line = src_lines[idx]
        if STOP_SCAN_RE.match(line):
            break
        m_sec = SECTION_COMMENT_RE.match(line)
        if m_sec:
            sec_num = m_sec.group("num")
            sec_title = sanitize_group_part(m_sec.group("title"))
            return f"{module_name}::{sec_num} - {sec_title}"

    return f"{module_name}::cover_properties"


def parse_verilator_user_coverage(dat_path):
    """Parse user coverage entries from coverage.dat and sum across instances."""
    # Key: (sf, line_no, module_name, label) -> hit_count
    aggregated = OrderedDict()

    with open(dat_path, "r", encoding="utf-8", errors="replace") as f:
        for raw_line in f:
            m_row = DAT_ROW_RE.match(raw_line)
            if not m_row:
                continue
            fields = parse_dat_payload(m_row.group("payload"))
            page = fields.get("page", "")
            if fields.get("t") != "user" and not page.startswith("v_user/"):
                continue

            sf = fields.get("f", "")
            line_str = fields.get("l", "0")
            if not sf or not line_str.isdigit():
                continue
            line_no = int(line_str)

            module_name = (
                page.split("/")[-1].split("__")[0]
                if "/" in page
                else os.path.splitext(os.path.basename(sf))[0]
            )
            label = fields.get("o") or f"line_{line_no}"
            # Ensure label has no commas
            label = label.replace(",", "_")
            count = int(m_row.group("count"))

            key = (sf, line_no, module_name, label)
            aggregated[key] = aggregated.get(key, 0) + count

    return aggregated


def build_lcov_records(aggregated, repo_root):
    """Build per-file DA and BRDA entries from aggregated user points."""
    file_records = OrderedDict()
    src_cache = {}

    for (sf, line_no, module_name, label), hit_count in aggregated.items():
        if sf not in src_cache:
            resolved = resolve_source_path(sf, repo_root)
            if os.path.isfile(resolved):
                with open(
                    resolved, "r", encoding="utf-8", errors="replace"
                ) as f:
                    src_cache[sf] = (resolved, f.readlines())
            else:
                src_cache[sf] = (resolved, [])

        resolved_sf, src_lines = src_cache[sf]
        group_name = find_section_group(src_lines, line_no, module_name)
        br_name = f"{group_name}.{label}"

        rec = file_records.setdefault(
            resolved_sf, {"da": OrderedDict(), "brda": []}
        )
        rec["da"][line_no] = rec["da"].get(line_no, 0) + hit_count
        rec["brda"].append((line_no, br_name, hit_count))

    return file_records


def write_lcov(file_records, output_path, test_name):
    """Write LCOV .info file with TN, SF, DA, LF, LH, BRDA, BRF, BRH."""
    out_dir = os.path.dirname(os.path.abspath(output_path))
    if out_dir:
        os.makedirs(out_dir, exist_ok=True)

    with open(output_path, "w", encoding="utf-8") as out:
        out.write(f"TN:{test_name}\n")
        for sf_path, rec in file_records.items():
            out.write(f"SF:{sf_path}\n")

            da_items = sorted(rec["da"].items(), key=lambda x: x[0])
            for line_no, hit_count in da_items:
                out.write(f"DA:{line_no},{hit_count}\n")
            lf_count = len(da_items)
            lh_count = sum(1 for _, c in da_items if c > 0)
            out.write(f"LF:{lf_count}\n")
            out.write(f"LH:{lh_count}\n")

            brda_sorted = sorted(rec["brda"], key=lambda x: (x[0], x[1]))
            block_id_by_line = {}
            for line_no, br_name, hit_count in brda_sorted:
                blk = block_id_by_line.get(line_no, 0)
                block_id_by_line[line_no] = blk + 1
                out.write(f"BRDA:{line_no},{blk},{br_name},{hit_count}\n")
            brf_count = len(brda_sorted)
            brh_count = sum(1 for _, _, c in brda_sorted if c > 0)
            out.write(f"BRF:{brf_count}\n")
            out.write(f"BRH:{brh_count}\n")
            out.write("end_of_record\n")


def main():
    """Main entry point."""
    args = parse_args()
    aggregated = parse_verilator_user_coverage(args.dat)
    file_records = build_lcov_records(aggregated, args.repo_root)
    write_lcov(file_records, args.output, args.test_name)
    return 0


if __name__ == "__main__":
    sys.exit(main())
