#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 Google LLC
#
# Convert Synopsys VCS URG functional coverage (`grpinfo.txt` / `.vdb`)
# into LCOV `.info` format (`*_fcov.info`) for Coverview and `info-process`.
# Author: Samip Modi (samipmodi@google.com)
"""Convert VCS covergroup reports (URG grpinfo.txt) to LCOV .info format."""

import argparse
from collections import OrderedDict
import itertools
import os
import re
import shutil
import subprocess
import sys
import tempfile

VERSION = "1.0.0"

SEPARATOR_RE = re.compile(r"^={40,}\s*$")
GROUP_HEADER_RE = re.compile(r"^Group\s*:\s*(?P<full_name>\S+)\s*$")
VAR_SUMMARY_RE = re.compile(r"^Summary for Variable\s+(?P<name>\S+)\s*$")
CROSS_SUMMARY_RE = re.compile(r"^Summary for Cross\s+(?P<name>\S+)\s*$")
SAMPLES_CROSSED_RE = re.compile(r"^Samples crossed:\s+(?P<samples>.+?)\s*$")
AUTO_RANGE_RE = re.compile(
    r"^\[(?P<prefix>[A-Za-z0-9_]+)\[(?P<start>\d+)\]\s*-\s*"
    r"(?P=prefix)\[(?P<end>\d+)\]\]$"
)


def tokenize_urg_row(line):
    """Split an URG table row into tokens, respecting nested [...] brackets."""
    tokens = []
    cur = []
    depth = 0
    for ch in line.strip():
        if ch == "[":
            depth += 1
            cur.append(ch)
        elif ch == "]":
            if depth > 0:
                depth -= 1
            cur.append(ch)
        elif ch.isspace() and depth == 0:
            if cur:
                tokens.append("".join(cur))
                cur = []
        else:
            cur.append(ch)
    if cur:
        tokens.append("".join(cur))
    return tokens


def parse_args():
    """Parse command line arguments."""
    parser = argparse.ArgumentParser(
        description=(
            "Convert Synopsys VCS URG covergroup reports into LCOV .info "
            "files compatible with info-process and Coverview."
        )
    )
    parser.add_argument(
        "--grpinfo",
        type=str,
        default=None,
        help="Path to an existing urgReport/grpinfo.txt file.",
    )
    parser.add_argument(
        "--vdb",
        type=str,
        default=None,
        metavar="DIR1.vdb,DIR2.vdb",
        help=(
            "Comma-separated list of VCS .vdb directories. Runs `urg` to "
            "generate grpinfo.txt in a temporary directory."
        ),
    )
    parser.add_argument(
        "-o",
        "--output",
        type=str,
        required=True,
        help="Output LCOV .info file path (e.g. coverage_test_fcov.info).",
    )
    parser.add_argument(
        "--repo-root",
        type=str,
        default=None,
        help=(
            "Optional repository root directory used to resolve source "
            "files if grpinfo.txt paths come from another workspace."
        ),
    )
    parser.add_argument(
        "--test-name",
        type=str,
        default="vcs_fcov",
        help="Test name written to the LCOV TN: field (default: vcs_fcov).",
    )
    parser.add_argument(
        "--version",
        action="version",
        version=f"%(prog)s {VERSION}",
    )
    args = parser.parse_args()
    if not args.grpinfo and not args.vdb:
        parser.error("Either --grpinfo or --vdb must be provided.")
    if args.grpinfo and args.vdb:
        parser.error("Specify only one of --grpinfo or --vdb.")
    return args


def run_urg_to_grpinfo(vdb_arg, work_dir):
    """Run Synopsys `urg` on comma-separated .vdb paths and return grpinfo."""
    vdb_dirs = [p.strip() for p in vdb_arg.split(",") if p.strip()]
    if not vdb_dirs:
        raise ValueError("No valid .vdb directories supplied to --vdb.")
    report_dir = os.path.join(work_dir, "urgReport")
    cmd = ["urg", "-full64", "-dir"] + vdb_dirs + [
        "-format",
        "text",
        "-report",
        report_dir,
    ]
    subprocess.run(cmd, check=True)
    grpinfo_path = os.path.join(report_dir, "grpinfo.txt")
    if not os.path.isfile(grpinfo_path):
        raise FileNotFoundError(
            f"urg succeeded but {grpinfo_path} was not created."
        )
    return grpinfo_path


def expand_auto_bin_token(name_token, number_token):
    """Expand an URG uncovered auto-bin range like `[auto[0] - auto[1]]`."""
    match = AUTO_RANGE_RE.match(name_token)
    if match:
        prefix = match.group("prefix")
        start = int(match.group("start"))
        end = int(match.group("end"))
        if end >= start:
            return [f"{prefix}[{idx}]" for idx in range(start, end + 1)]
    if name_token.startswith("[") and name_token.endswith("]"):
        inner = name_token[1:-1]
        parts = [p.strip() for p in inner.split(",") if p.strip()]
        if parts:
            return parts
    try:
        count = int(number_token)
    except ValueError:
        count = 1
    if count > 1 and name_token.startswith("["):
        return [f"{name_token}_{idx}" for idx in range(count)]
    return [name_token]


def parse_variable_section(lines, start_idx):
    """Parse a `Summary for Variable <cp>` section in grpinfo.txt."""
    bins = OrderedDict()
    idx = start_idx
    mode = None

    while idx < len(lines):
        line = lines[idx].strip()
        if (
            line.startswith("Summary for Variable ")
            or line.startswith("Summary for Cross ")
            or GROUP_HEADER_RE.match(line)
            or line.startswith("Group Instance :")
            or SEPARATOR_RE.match(line)
        ):
            break

        if line == "Uncovered bins":
            mode = "uncovered"
            idx += 1
            continue
        if line in ("Covered bins", "Bins"):
            mode = "covered"
            idx += 1
            continue
        if line in ("Excluded/Illegal bins", "User Defined Bins", "CATEGORY"):
            mode = None
            idx += 1
            continue
        if (
            not line
            or line.startswith("---")
            or line.startswith("NAME ")
            or line.startswith("CATEGORY ")
            or line.startswith("User Defined Bins ")
            or line.startswith("Automatically Generated Bins ")
        ):
            idx += 1
            continue

        tokens = tokenize_urg_row(line)
        if mode == "uncovered" and len(tokens) >= 4:
            name_tok = tokens[0]
            raw_count = tokens[1]
            num_tok = tokens[3]
            hit_count = 0 if raw_count in ("--", "-") else int(raw_count)
            for expanded_name in expand_auto_bin_token(name_tok, num_tok):
                bins[expanded_name] = bins.get(expanded_name, 0) + hit_count
        elif mode == "covered" and len(tokens) >= 3:
            name_tok = tokens[0]
            raw_count = tokens[1]
            if raw_count not in ("--", "-"):
                hit_count = int(raw_count)
                bins[name_tok] = bins.get(name_tok, 0) + hit_count

        idx += 1

    return bins, idx


def expand_cross_cell(token, cp_name, cp_bins_map):
    """Expand a single cell in an URG cross table (`*`, `[a , b]`, or `a`)."""
    if token == "*":
        known = list(cp_bins_map.get(cp_name, {}).keys())
        return known if known else ["*"]
    if AUTO_RANGE_RE.match(token):
        return expand_auto_bin_token(token, "1")
    if token.startswith("[") and token.endswith("]"):
        inner = token[1:-1]
        parts = [p.strip() for p in inner.split(",") if p.strip()]
        expanded = []
        for part in parts:
            expanded.extend(expand_auto_bin_token(part, "1"))
        return expanded if expanded else [token]
    return [token]


def parse_cross_section(lines, start_idx, cp_bins_map):
    """Parse a `Summary for Cross <cross>` section in grpinfo.txt."""
    cross_bins = OrderedDict()
    crossed_cps = []
    idx = start_idx
    mode = None
    is_user_defined_cross = False

    while idx < len(lines):
        line = lines[idx].strip()
        if (
            line.startswith("Summary for Variable ")
            or line.startswith("Summary for Cross ")
            or GROUP_HEADER_RE.match(line)
            or line.startswith("Group Instance :")
            or SEPARATOR_RE.match(line)
        ):
            break

        m_samples = SAMPLES_CROSSED_RE.match(line)
        if m_samples:
            crossed_cps = m_samples.group("samples").split()
            idx += 1
            continue

        if line.startswith("Automatically Generated Cross Bins"):
            is_user_defined_cross = False
            mode = None
            idx += 1
            continue
        if line.startswith("User Defined Cross Bins"):
            is_user_defined_cross = True
            mode = None
            idx += 1
            continue

        if line in ("Element holes", "Uncovered bins"):
            mode = "uncovered"
            idx += 1
            continue
        if line in ("Covered bins", "Bins"):
            mode = "covered"
            idx += 1
            continue
        if line.startswith("Excluded/Illegal bins"):
            mode = None
            idx += 1
            continue

        if (
            not line
            or line.startswith("---")
            or line.startswith("CATEGORY ")
            or line.startswith("TOTAL ")
            or re.search(r"\bCOUNT\s+AT\s+LEAST\b", line)
            or re.search(r"\bCOUNT\s+STATUS\b", line)
        ):
            idx += 1
            continue

        tokens = tokenize_urg_row(line)
        num_cps = 1 if is_user_defined_cross else len(crossed_cps)
        if num_cps > 0 and mode == "uncovered" and len(tokens) >= num_cps + 3:
            if is_user_defined_cross:
                cross_bins.setdefault(tokens[0], 0)
            else:
                cell_lists = [
                    expand_cross_cell(tokens[i], crossed_cps[i], cp_bins_map)
                    for i in range(num_cps)
                ]
                for combo in itertools.product(*cell_lists):
                    key = "__x__".join(combo)
                    cross_bins.setdefault(key, 0)
        elif num_cps > 0 and mode == "covered" and len(tokens) >= num_cps + 2:
            raw_count = tokens[num_cps]
            if raw_count not in ("--", "-"):
                key = (
                    tokens[0]
                    if is_user_defined_cross
                    else "__x__".join(tokens[:num_cps])
                )
                cross_bins[key] = cross_bins.get(key, 0) + int(raw_count)

        idx += 1

    return crossed_cps, cross_bins, idx


def parse_grpinfo(grpinfo_path):
    """Parse URG grpinfo.txt and return aggregated covergroup data."""
    with open(grpinfo_path, "r", encoding="utf-8", errors="replace") as f:
        lines = f.readlines()

    # Key: (source_file, cg_name) -> {
    #   "variables": OrderedDict(cp_name -> OrderedDict(bin_name -> count)),
    #   "crosses": OrderedDict(cross_name -> OrderedDict(bin_name -> count)),
    # }
    groups = OrderedDict()

    idx = 0
    num_lines = len(lines)
    while idx < num_lines:
        if not SEPARATOR_RE.match(lines[idx]):
            idx += 1
            continue

        if idx + 2 >= num_lines or not SEPARATOR_RE.match(lines[idx + 2]):
            idx += 1
            continue

        header_line = lines[idx + 1].strip()
        m_group = GROUP_HEADER_RE.match(header_line)
        if not m_group:
            # Skip `Group Instance : ...` blocks so instances are not
            # double-counted.
            idx += 3
            continue

        full_name = m_group.group("full_name")
        cg_name = full_name.split("::")[-1]
        idx += 3

        # Find `Source File(s) :` inside this group section
        source_file = None
        while idx < num_lines and not SEPARATOR_RE.match(lines[idx]):
            stripped = lines[idx].strip()
            if stripped.startswith("Source File(s)"):
                idx += 1
                while idx < num_lines and not lines[idx].strip():
                    idx += 1
                if idx < num_lines:
                    source_file = lines[idx].strip()
                break
            idx += 1

        if not source_file:
            continue

        group_key = (source_file, cg_name)
        if group_key not in groups:
            groups[group_key] = {
                "variables": OrderedDict(),
                "crosses": OrderedDict(),
            }
        group_entry = groups[group_key]
        local_cp_bins = OrderedDict()

        while idx < num_lines and not SEPARATOR_RE.match(lines[idx]):
            stripped = lines[idx].strip()
            m_var = VAR_SUMMARY_RE.match(stripped)
            if m_var:
                cp_name = m_var.group("name")
                cp_bins, idx = parse_variable_section(lines, idx + 1)
                local_cp_bins[cp_name] = cp_bins
                target_cp = group_entry["variables"].setdefault(
                    cp_name, OrderedDict()
                )
                for b_name, b_cnt in cp_bins.items():
                    target_cp[b_name] = target_cp.get(b_name, 0) + b_cnt
                continue

            m_cross = CROSS_SUMMARY_RE.match(stripped)
            if m_cross:
                cross_name = m_cross.group("name")
                _, cross_bins, idx = parse_cross_section(
                    lines, idx + 1, local_cp_bins
                )
                target_cr = group_entry["crosses"].setdefault(
                    cross_name, OrderedDict()
                )
                for b_name, b_cnt in cross_bins.items():
                    target_cr[b_name] = target_cr.get(b_name, 0) + b_cnt
                continue

            idx += 1

    return groups


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


def find_covergroup_range(src_lines, cg_name):
    """Find (start_line_1based, end_line_1based) for `covergroup <cg_name>`."""
    cg_re = re.compile(rf"\bcovergroup\s+{re.escape(cg_name)}\b")
    end_re = re.compile(r"\bendgroup\b")
    start_line = None
    for idx, text in enumerate(src_lines, start=1):
        if start_line is None:
            if cg_re.search(text):
                start_line = idx
        else:
            if end_re.search(text):
                return start_line, idx
    return 1, len(src_lines)


def find_coverpoint_lines(src_lines, cg_start, cg_end, cp_name, bins_dict):
    """Map a coverpoint and each of its bins to 1-based line numbers."""
    cp_re = re.compile(rf"\b{re.escape(cp_name)}\s*:\s*coverpoint\b")
    macro_re = re.compile(rf"`\w+\s*\(\s*{re.escape(cp_name)}\s*\)")
    next_item_re = re.compile(r"\b\w+\s*:\s*(coverpoint|cross)\b|\bendgroup\b")

    cp_line = cg_start
    cp_end_line = cg_end
    found_cp = False

    for line_no in range(cg_start, cg_end + 1):
        text = src_lines[line_no - 1]
        if cp_re.search(text) or macro_re.search(text):
            cp_line = line_no
            found_cp = True
            for scan_no in range(line_no + 1, cg_end + 1):
                if next_item_re.search(src_lines[scan_no - 1]):
                    cp_end_line = scan_no - 1
                    break
            break

    bin_lines = OrderedDict()
    for bin_name in bins_dict:
        bin_line = cp_line
        if found_cp:
            bin_re = re.compile(rf"\bbins\s+{re.escape(bin_name)}\b")
            for scan_no in range(cp_line, cp_end_line + 1):
                if bin_re.search(src_lines[scan_no - 1]):
                    bin_line = scan_no
                    break
        bin_lines[bin_name] = bin_line

    return cp_line, bin_lines


def find_cross_line(src_lines, cg_start, cg_end, cross_name):
    """Map a cross declaration to its 1-based line number."""
    cross_re = re.compile(rf"\b{re.escape(cross_name)}\s*:\s*cross\b")
    for line_no in range(cg_start, cg_end + 1):
        if cross_re.search(src_lines[line_no - 1]):
            return line_no
    return cg_start


def build_lcov_records(groups, repo_root):
    """Build per-file DA and BRDA entries from parsed grpinfo groups."""
    file_records = OrderedDict()

    for (raw_sf, cg_name), cg_data in groups.items():
        resolved_sf = resolve_source_path(raw_sf, repo_root)
        if os.path.isfile(resolved_sf):
            with open(
                resolved_sf, "r", encoding="utf-8", errors="replace"
            ) as f:
                src_lines = f.readlines()
        else:
            src_lines = [""]

        record = file_records.setdefault(
            resolved_sf, {"da": OrderedDict(), "brda": []}
        )

        cg_start, cg_end = find_covergroup_range(src_lines, cg_name)

        # 1. Coverpoints and their bins
        for cp_name, bins_dict in cg_data["variables"].items():
            _, bin_lines = find_coverpoint_lines(
                src_lines, cg_start, cg_end, cp_name, bins_dict
            )
            for bin_name, hit_count in bins_dict.items():
                line_no = bin_lines.get(bin_name, cg_start)
                br_name = f"{cg_name}::{cp_name}.{bin_name}"
                record["brda"].append((line_no, br_name, hit_count))
                prev = record["da"].get(line_no, 0)
                record["da"][line_no] = prev + hit_count

        # 2. Crosses and their cross bins
        for cross_name, cross_bins in cg_data["crosses"].items():
            line_no = find_cross_line(src_lines, cg_start, cg_end, cross_name)
            for combo_name, hit_count in cross_bins.items():
                br_name = f"{cg_name}::{cross_name}.{combo_name}"
                record["brda"].append((line_no, br_name, hit_count))
                prev = record["da"].get(line_no, 0)
                record["da"][line_no] = prev + hit_count

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
    tmp_dir = None
    try:
        if args.vdb:
            tmp_dir = tempfile.mkdtemp(prefix="vcs_fcov_urg_")
            grpinfo_path = run_urg_to_grpinfo(args.vdb, tmp_dir)
        else:
            grpinfo_path = args.grpinfo

        groups = parse_grpinfo(grpinfo_path)
        file_records = build_lcov_records(groups, args.repo_root)
        write_lcov(file_records, args.output, args.test_name)
    finally:
        if tmp_dir and os.path.isdir(tmp_dir):
            shutil.rmtree(tmp_dir, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
