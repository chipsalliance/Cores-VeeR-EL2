"""Run the block-level cocotb tests under Metabole in shadow mode.

Every test runs exactly as `nox -s <block>_verify` would run it (same make
command, same seed); Metabole only records each test's inputs and result and
reports which runs it would have reused from the previous run on main. It
never skips a test in shadow mode.

usage: python .github/scripts/metabole_shadow.py <block> [<block> ...]
"""

import ast
import os
import subprocess
import sys
import uuid

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
BLOCK = os.path.join(ROOT, "verification", "block")
STORE = os.environ.get("METABOLE_STORE", os.path.join(ROOT, ".metabole", "store"))
PRINT_MK = "print-sources:\n\t@echo $(VERILOG_SOURCES)\n\t@echo INCS $(EXTRA_ARGS)\n"


def tests(block):
    """Test modules of a block, from the nox sessions."""
    src = open(os.path.join(BLOCK, "noxfile.py")).read()
    for fn in ast.walk(ast.parse(src)):
        if not isinstance(fn, ast.FunctionDef):
            continue
        params = {}
        for d in fn.decorator_list:
            if (
                isinstance(d, ast.Call)
                and getattr(d.func, "attr", "") == "parametrize"
                and len(d.args) >= 2
                and isinstance(d.args[0], ast.Constant)
                and d.args[0].value in ("blockName", "testName")
            ):
                params[d.args[0].value] = ast.literal_eval(d.args[1])
        if block in params.get("blockName", []):
            return params.get("testName", [])
    return []


def filelist(block, out):
    """Verilog sources and include dirs of a block, without the generated snapshot."""
    mk = os.path.join(out, "print.mk")
    open(mk, "w").write(PRINT_MK)
    p = subprocess.run(
        [
            "make",
            "-s",
            "-C",
            os.path.join(BLOCK, block),
            "-f",
            "Makefile",
            "-f",
            mk,
            "print-sources",
        ],
        capture_output=True,
        text=True,
        check=True,
    )
    lines = [line for line in p.stdout.splitlines() if line.strip()]
    srcs = [s for s in lines[-2].split() if "/snapshots/" not in s]
    incs = [t[2:] for t in lines[-1].split()[1:] if t.startswith("-I") and "/snapshots/" not in t]
    incs.append(os.path.join(ROOT, "design", "include"))
    fl = os.path.join(out, f"{block}.f")
    with open(fl, "w") as f:
        f.write("\n".join(srcs + [f"+incdir+{d}" for d in incs]) + "\n")
    return fl


def run(block, test, out):
    bdir = os.path.join(BLOCK, block)
    files = subprocess.run(
        ["git", "-C", ROOT, "ls-files", "configs", "tools", "verification/block/common"],
        capture_output=True,
        text=True,
        check=True,
    ).stdout.split()
    files += [
        "verification/block/common.mk",
        "verification/block/config.vlt",
        "verification/block/requirements.txt",
    ]
    for f in sorted(os.listdir(bdir)):
        path = os.path.join(bdir, f)
        if (
            os.path.isfile(path)
            and (not f.startswith("test_") or f == f"{test}.py")
            and not f.endswith((".xml", ".log", ".vcd", ".dat"))
        ):
            files.append(os.path.relpath(path, ROOT))
    cmd = [
        "metabole",
        "run",
        "--mode",
        "shadow",
        "--store",
        STORE,
        "--root",
        ROOT,
        "--test-id",
        f"{block}/{test}",
        "--sim",
        "verilator",
        "--value",
        f"seed={os.environ.get('RANDOM_SEED', '')}",
        "--result",
        os.path.join(bdir, f"{test}.xml"),
        "-f",
        filelist(block, out),
    ]
    for f in files:
        if os.path.isfile(os.path.join(ROOT, f)):
            cmd += ["--file", f]
    cmd += ["--", "make", "-C", bdir, "all", f"MODULE={test}", f"COCOTB_RESULTS_FILE={test}.xml"]
    return subprocess.call(cmd)


def main(blocks):
    # as in test-uarch.yml: the configuration generator needs RV_ROOT
    os.environ.setdefault("RV_ROOT", ROOT)
    # one run for all tests (CI sets GITHUB_RUN_ID, which Metabole uses)
    if not os.environ.get("GITHUB_RUN_ID"):
        os.environ.setdefault("METABOLE_RUN_ID", uuid.uuid4().hex[:12])
    out = os.path.join(ROOT, ".metabole", "work")
    os.makedirs(out, exist_ok=True)
    failed = [f"{b}/{t}" for b in blocks for t in tests(b) if run(b, t, out) != 0]
    subprocess.call(
        [
            "metabole",
            "stats",
            "--store",
            STORE,
            "--run",
            os.environ.get("GITHUB_RUN_ID") or os.environ["METABOLE_RUN_ID"],
        ]
    )
    if failed:
        sys.exit(f"failed: {', '.join(failed)}")


if __name__ == "__main__":
    main(sys.argv[1:])
