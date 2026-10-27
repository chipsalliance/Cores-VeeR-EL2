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
            or line.startswith("TOTAL ")
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
            try:
                hit_count = 0 if raw_count in ("--", "-") else int(raw_count)
            except ValueError:
                idx += 1
                continue
            for expanded_name in expand_auto_bin_token(name_tok, num_tok):
                bins[expanded_name] = bins.get(expanded_name, 0) + hit_count
        elif mode == "covered" and len(tokens) >= 3:
            name_tok = tokens[0]
            raw_count = tokens[1]
            if raw_count not in ("--", "-"):
                try:
                    hit_count = int(raw_count)
                except ValueError:
                    idx += 1
                    continue
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
    excluded_bins = set()
    crossed_cps = []
    idx = start_idx
    mode = None
    is_user_defined_cross = False
    has_auto_bins = False

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
            rest = line[len("Automatically Generated Cross Bins") :].strip()
            rest_tokens = rest.split()
            if not rest_tokens or rest_tokens[0] == "for":
                is_user_defined_cross = False
                mode = None
            elif rest_tokens[0] != "0":
                has_auto_bins = True
                is_user_defined_cross = False
                mode = None
            idx += 1
            continue
        if line.startswith("User Defined Cross Bins"):
            rest = line[len("User Defined Cross Bins") :].strip()
            rest_tokens = rest.split()
            if not rest_tokens or rest_tokens[0] == "for":
                is_user_defined_cross = True
                mode = None
            elif rest_tokens[0] != "0" and not has_auto_bins:
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
            mode = "excluded"
            idx += 1
            continue

        if (
            not line
            or line.startswith("---")
            or line.startswith("NAME ")
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
            raw_count = tokens[num_cps]
            if raw_count not in ("--", "-"):
                try:
                    int(raw_count)
                except ValueError:
                    idx += 1
                    continue
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
                try:
                    hit_count = int(raw_count)
                except ValueError:
                    idx += 1
                    continue
                if is_user_defined_cross:
                    cross_bins[tokens[0]] = (
                        cross_bins.get(tokens[0], 0) + hit_count
                    )
                else:
                    cell_lists = [
                        expand_cross_cell(
                            tokens[i], crossed_cps[i], cp_bins_map
                        )
                        for i in range(num_cps)
                    ]
                    for combo in itertools.product(*cell_lists):
                        key = "__x__".join(combo)
                        cross_bins[key] = cross_bins.get(key, 0) + hit_count
        elif num_cps > 0 and mode == "excluded" and len(tokens) >= num_cps + 1:
            raw_count = tokens[num_cps]
            if raw_count not in ("--", "-"):
                try:
                    int(raw_count)
                except ValueError:
                    idx += 1
                    continue
            if is_user_defined_cross:
                for ex_name in expand_cross_cell(tokens[0], "", cp_bins_map):
                    excluded_bins.add(ex_name)
            else:
                cell_lists = [
                    expand_cross_cell(tokens[i], crossed_cps[i], cp_bins_map)
                    for i in range(num_cps)
                ]
                for combo in itertools.product(*cell_lists):
                    excluded_bins.add("__x__".join(combo))

        idx += 1

    for ex_key in excluded_bins:
        cross_bins.pop(ex_key, None)

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
                after_colon = (
                    stripped.split(":", 1)[1].strip()
                    if ":" in stripped
                    else ""
                )
                idx += 1
                if after_colon:
                    source_file = after_colon
                else:
                    while idx < num_lines and not lines[idx].strip():
                        idx += 1
                    if idx < num_lines and not SEPARATOR_RE.match(lines[idx]):
                        source_file = lines[idx].strip()
                        idx += 1
                break
            idx += 1

        if not source_file:
            continue

        group_key = (source_file, cg_name)
        if group_key not in groups:
            groups[group_key] = {
                "variables": OrderedDict(),
                "crosses": OrderedDict(),
                "cross_cps": OrderedDict(),
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
                crossed_cps, cross_bins, idx = parse_cross_section(
                    lines, idx + 1, local_cp_bins
                )
                if crossed_cps:
                    group_entry["cross_cps"][cross_name] = crossed_cps
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
    if repo_root:
        norm_root = os.path.abspath(repo_root)
        for marker in ("testbench/", "verification/", "design/"):
            pos = source_file.find(marker)
            if pos != -1:
                candidate = os.path.normpath(
                    os.path.join(norm_root, source_file[pos:])
                )
                if os.path.isfile(candidate):
                    return candidate
    if os.path.isfile(source_file):
        return os.path.abspath(source_file)
    return os.path.normpath(source_file)


def find_covergroup_range(src_lines, cg_name):
    """Find (start_line_1based, end_line_1based) for `covergroup <cg_name>`."""
    cg_leaf = cg_name.split(".")[-1]
    cg_re = re.compile(rf"\bcovergroup\s+{re.escape(cg_leaf)}\b")
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


def normalize_sv_val(tok):
    """Normalize a SystemVerilog integer literal token for bin matching."""
    cleaned = tok.strip()
    m_based = re.match(
        r"^\d*'[sS]?([bBdDhHoO])([0-9a-fA-F_]+)$", cleaned
    )
    if m_based:
        base_map = {"b": 2, "d": 10, "h": 16, "o": 8}
        base = base_map[m_based.group(1).lower()]
        try:
            return str(int(m_based.group(2).replace("_", ""), base))
        except ValueError:
            return cleaned
    if cleaned.isdigit():
        return str(int(cleaned))
    return cleaned


def extract_braced_body(text, start_pos):
    """Return (header_before_brace, body_inside_braces) from start_pos."""
    depth = 0
    brace_start = None
    for idx in range(start_pos, len(text)):
        ch = text[idx]
        if ch == ";" and depth == 0:
            return None, None
        if ch == "{":
            if depth == 0:
                brace_start = idx
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0 and brace_start is not None:
                return (
                    text[start_pos:brace_start],
                    text[brace_start + 1 : idx],
                )
    return None, None


def find_sv_cross_ignored_keys(
    src_lines, cg_start, cg_end, cross_name, crossed_cps, cp_bins_map
):
    """Evaluate SV cross ignore/illegal_bins and return ignored keys."""
    if not src_lines or cg_start > len(src_lines):
        return set()

    cg_text = "".join(src_lines[cg_start - 1 : cg_end])
    cg_text = re.sub(r"/\*.*?\*/", "", cg_text, flags=re.DOTALL)
    cg_text = re.sub(r"//[^\n]*", "", cg_text)

    cross_hdr_re = re.compile(rf"\b{re.escape(cross_name)}\s*:\s*cross\b")
    m_cross = cross_hdr_re.search(cg_text)
    if not m_cross:
        return set()

    cp_list_str, cross_body = extract_braced_body(cg_text, m_cross.end())
    if cross_body is None:
        return set()

    if not crossed_cps and cp_list_str:
        crossed_cps = [
            c.strip() for c in cp_list_str.split(",") if c.strip()
        ]
    if not crossed_cps:
        return set()

    cp_known_bins = {}
    cp_bin_vals = {}
    bin_decl_re = re.compile(
        r"(?:wildcard\s+)?bins\s+(\w+)\s*(?:\[\s*\])?\s*=\s*\{([^}]*)\}"
    )
    for cp in crossed_cps:
        known = list(cp_bins_map.get(cp, {}).keys())
        vals_map = {}
        cp_hdr_re = re.compile(rf"\b{re.escape(cp)}\s*:\s*coverpoint\b")
        m_cp = cp_hdr_re.search(cg_text)
        if m_cp:
            _, cp_body = extract_braced_body(cg_text, m_cp.end())
            if cp_body:
                for m_b in bin_decl_re.finditer(cp_body):
                    b_name = m_b.group(1)
                    if b_name not in known:
                        known.append(b_name)
                    raw_tokens = [
                        t.strip()
                        for t in m_b.group(2).split(",")
                        if t.strip()
                    ]
                    vals_map[b_name] = {
                        normalize_sv_val(t) for t in raw_tokens
                    } | set(raw_tokens)
        cp_known_bins[cp] = known
        cp_bin_vals[cp] = vals_map

    ignored_keys = set()
    stmt_re = re.compile(
        r"\b(?:ignore_bins|illegal_bins)\s+\w+\s*=\s*(.*?);", flags=re.DOTALL
    )
    int_re = re.compile(
        r"(!?)\s*binsof\s*\(\s*(\w+)(?:\.(\w+))?\s*\)\s*"
        r"intersect\s*\{([^}]*)\}"
    )
    bin_re = re.compile(r"(!?)\s*binsof\s*\(\s*(\w+)\.(\w+)\s*\)")

    for m_stmt in stmt_re.finditer(cross_body):
        expr = m_stmt.group(1)
        for or_clause in expr.split("||"):
            allowed = {
                cp: list(cp_known_bins.get(cp, [])) for cp in crossed_cps
            }
            if any(not allowed[cp] for cp in crossed_cps):
                continue
            matched_constraint = False
            for and_term in or_clause.split("&&"):
                term = and_term.strip()
                m_int = int_re.search(term)
                if m_int:
                    negated = m_int.group(1) == "!"
                    cp = m_int.group(2)
                    sub_bin = m_int.group(3)
                    raw_targets = [
                        t.strip()
                        for t in m_int.group(4).split(",")
                        if t.strip()
                    ]
                    target_vals = {
                        normalize_sv_val(t) for t in raw_targets
                    } | set(raw_targets)
                    if cp in allowed:
                        candidates = (
                            [sub_bin] if sub_bin else cp_known_bins.get(cp, [])
                        )
                        matching = [
                            b
                            for b in candidates
                            if cp_bin_vals.get(cp, {}).get(b, set())
                            & target_vals
                        ]
                        term_bins = [
                            b
                            for b in cp_known_bins[cp]
                            if (
                                b not in matching
                                if negated
                                else b in matching
                            )
                        ]
                        allowed[cp] = [
                            b for b in allowed[cp] if b in term_bins
                        ]
                        matched_constraint = True
                    continue

                m_bin = bin_re.search(term)
                if m_bin:
                    negated = m_bin.group(1) == "!"
                    cp = m_bin.group(2)
                    b_target = m_bin.group(3)
                    if cp in allowed:
                        term_bins = [
                            b
                            for b in cp_known_bins[cp]
                            if (b != b_target if negated else b == b_target)
                        ]
                        allowed[cp] = [
                            b for b in allowed[cp] if b in term_bins
                        ]
                        matched_constraint = True

            if matched_constraint:
                for combo in itertools.product(
                    *(allowed[cp] for cp in crossed_cps)
                ):
                    ignored_keys.add("__x__".join(combo))

    return ignored_keys


def sanitize_brda_prefix(text):
    """Sanitize text before the single '.' separator in BRDA names."""
    cleaned = text.replace(".", "_").replace(",", "_")
    return re.sub(r"\s+", "_", cleaned).strip("_")


def sanitize_brda_bin(text):
    """Sanitize bin/combo text so ',' never breaks LCOV BRDA splitting."""
    cleaned = text.replace(",", "_")
    return re.sub(r"\s+", "_", cleaned).strip("_")


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
        safe_cg = sanitize_brda_prefix(cg_name)

        # 1. Coverpoints and their bins
        for cp_name, bins_dict in cg_data["variables"].items():
            _, bin_lines = find_coverpoint_lines(
                src_lines, cg_start, cg_end, cp_name, bins_dict
            )
            safe_cp = sanitize_brda_prefix(cp_name)
            for bin_name, hit_count in bins_dict.items():
                line_no = bin_lines.get(bin_name, cg_start)
                safe_bin = sanitize_brda_bin(bin_name)
                br_name = f"{safe_cg}::{safe_cp}.{safe_bin}"
                record["brda"].append((line_no, br_name, hit_count))
                prev = record["da"].get(line_no, 0)
                record["da"][line_no] = prev + hit_count

        # 2. Crosses and their cross bins
        for cross_name, cross_bins in cg_data["crosses"].items():
            line_no = find_cross_line(src_lines, cg_start, cg_end, cross_name)
            crossed_cps = cg_data.get("cross_cps", {}).get(cross_name, [])
            ignored_cross_keys = find_sv_cross_ignored_keys(
                src_lines,
                cg_start,
                cg_end,
                cross_name,
                crossed_cps,
                cg_data["variables"],
            )
            safe_cr = sanitize_brda_prefix(cross_name)
            for combo_name, hit_count in cross_bins.items():
                if combo_name in ignored_cross_keys:
                    continue
                safe_combo = sanitize_brda_bin(combo_name)
                br_name = f"{safe_cg}::{safe_cr}.{safe_combo}"
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
            vdb_dirs = [p.strip() for p in args.vdb.split(",") if p.strip()]
            if not vdb_dirs:
                print(
                    "Error: No valid .vdb directories supplied to --vdb.",
                    file=sys.stderr,
                )
                return 1
            for vdb_dir in vdb_dirs:
                if not os.path.exists(vdb_dir):
                    print(
                        f"Error: VDB directory not found: {vdb_dir}",
                        file=sys.stderr,
                    )
                    return 1
            tmp_dir = tempfile.mkdtemp(prefix="vcs_fcov_urg_")
            grpinfo_path = run_urg_to_grpinfo(args.vdb, tmp_dir)
        else:
            if not os.path.isfile(args.grpinfo):
                print(
                    f"Error: grpinfo file not found: {args.grpinfo}",
                    file=sys.stderr,
                )
                return 1
            grpinfo_path = args.grpinfo

        groups = parse_grpinfo(grpinfo_path)
        file_records = build_lcov_records(groups, args.repo_root)
        write_lcov(file_records, args.output, args.test_name)
        return 0
    except (OSError, subprocess.CalledProcessError, ValueError) as exc:
        print(
            f"Error converting VCS functional coverage: {exc}",
            file=sys.stderr,
        )
        return 1
    finally:
        if tmp_dir and os.path.isdir(tmp_dir):
            shutil.rmtree(tmp_dir, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
