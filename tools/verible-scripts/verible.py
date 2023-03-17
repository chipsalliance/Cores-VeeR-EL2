#!/usr/bin/env python

import argparse
import os


def main():
    """
    Parse arguments
    """
    parser = argparse.ArgumentParser(description="VeeR Coding Standard")
    parser.add_argument(
        "--only_discover",
        action="store_true",
        help="Lists all found {.v|.sv|...} files ",
    )
    parser.add_argument("--tool", default="lint", help="Select: {format|lint}")
    parser.add_argument(
        "--restore_git", action="store_true", help="Restore only {.v|.sv|...} files"
    )
    parser.add_argument("--linter", default="verible-verilog-lint", help="Tool")
    args = parser.parse_args()

    """
        Check if RV_ROOT exists
    """
    RV_ROOT = os.getenv("RV_ROOT")
    if not RV_ROOT:
        raise ValueError("RV_ROOT must be set")
    """
        Discover all {v,sv,...} files
    """
    paths = []
    file_extensions = [".v", ".vh", ".sv", ".svi", ".svh"]
    for root, dirs, files in os.walk(RV_ROOT):
        for file in files:
            for extension in file_extensions:
                if file.endswith(extension):
                    paths.append(os.path.join(root, file))

    if args.only_discover:
        for path in paths:
            print(path)
        print("Exiting early; only-discover")
        return

    """
        Restore git
    """
    if args.restore_git:
        for file in paths:
            git_cmd = "git restore " + file
            print(f"[GIT RESTORE] {git_cmd}")
            os.system(git_cmd)
        print("Exiting early; git restore")
        return

    """
        Run selected verible tool on all files
         - Lint https://github.com/chipsalliance/verible/tree/master/verilog/tools/lint
         - Format https://github.com/chipsalliance/verible/tree/master/verilog/formatting
    """
    if args.tool == "lint":
        verible_tool = "verible-verilog-lint "
        verible_tool_opts = " --waiver_files=" + RV_ROOT + "/violations.waiver "
        verible_tool_opts += " --rules=line-length=length:100 "
        verible_tool_opts += " --autofix=inplace "
    if args.tool == "format":
        verible_tool = "verible-verilog-format "
        verible_tool_opts = " --inplace"

    for file in paths:
        tool_cmd = verible_tool + verible_tool_opts + " " + file
        print(f"[RUN CMD] {tool_cmd}")
        os.system(tool_cmd)


if __name__ == "__main__":
    main()
