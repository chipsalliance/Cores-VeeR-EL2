from io import TextIOWrapper
import logging
import subprocess
from pathlib import Path
from shutil import copy2
from typing import List, Optional

from .common import args_on_debug_logger, main_func_log, styles_dir, get_logger
from .genhtml import genhtml, get_common_src_path, parse_infos

logger = get_logger(__name__)


def obtain_stdout(filename) -> TextIOWrapper | int:
    """Checks whether the logger is in debug mode. If it is
    then returns a file descriptor to the file with the given filename.
    Otherwise, returns subprocess.DEVNULL."""
    if logger.getEffectiveLevel() <= logging.DEBUG:
        return open(filename, "w+")
    return subprocess.DEVNULL


def lcov_merge(input_files: List[str], output_file: str):
    """Invokes lcov tool to add `input_file` into the tracefile.
    `output_file` becomes then an aggregate of *.info files."""
    lcov_command = ["lcov", "-o", output_file]

    for input_file in input_files:
        lcov_command += ["-a", input_file]

    subprocess.run(
        lcov_command,
        stdout=obtain_stdout(f"{output_file}_merge.log"),
    )


@args_on_debug_logger(logger=logger)
def lcov_genhtml(
    info_files,
    path_prefix,
    lcov_report_dir="lcov_report",
    log_output_path="lcov_genhtml.log",
):
    """Invokes lcov's genhtml tool to generate source file views for the coverage report."""
    command = ["genhtml", "--output-dir", lcov_report_dir, *info_files]

    if not path_prefix:
        subprocess.run(
            command,
            stdout=obtain_stdout(log_output_path),
        )
    else:
        command += ["--prefix", str(Path(path_prefix).resolve())]
        subprocess.run(
            command,
            stdout=obtain_stdout(log_output_path),
        )


@args_on_debug_logger(logger=logger)
def generate_coverage_reports(
    output_dir,
    src_path,
    src_pattern="*",
    src_remove_pattern=None,
    logo_src=None,
    logo_href=None,
    info_report_dir=None,
    project_name="Project",
    info_pattern="coverage*.info",
):
    """Iterates over available *.info files, merges them & generates summaries
    for each coverage type with the use of lcov.
    Calls `genhtml` to generate coverage dashboards for individual tests as
    well as for the all tests combined."""
    curr_dir = Path.cwd()
    if not info_report_dir:
        info_report_dir = curr_dir

    if not Path(src_path).exists():
        raise ValueError(f"Sources path doesn't exist {src_path}")

    # Extract coverage info files
    info_files = list(Path(info_report_dir).glob(f"**/{info_pattern}"))
    processed_info = False

    for info_file in info_files:
        logger.debug(f"Preprocessing {info_file}")
        lcov_extract_command = ["lcov", "--extract", info_file, src_pattern, "-o", info_file]

        data = parse_infos([str(info_file)])
        if len(data.keys()) == 0:
            logger.warning(f"No data found in .info file: {info_file}")
            continue

        processed_info = True
        path_prefix = get_common_src_path(data.keys())
        resolved_src_path = Path(src_path).resolve()

        # Align paths to end in the same directory:
        parts = path_prefix.parts
        src_dir_parts = resolved_src_path.name
        for i in reversed(range(len(parts))):
            if parts[i] == src_dir_parts:
                break
            path_prefix = path_prefix.parent

        resolved_path_prefix = Path(path_prefix).resolve()
        logger.debug(f"Deduced source path prefix: {path_prefix}")
        if resolved_src_path != resolved_path_prefix:
            logger.debug(f"Substituting prefix: {path_prefix} -> {resolved_src_path}")
            lcov_extract_command += [
                "--substitute",
                f"s|{path_prefix}|{resolved_src_path}|",
            ]

        subprocess.run(
            lcov_extract_command,
            stdout=obtain_stdout(f"{info_file}_extraction.log"),
        )
        if src_remove_pattern is not None:
            subprocess.run(
                ["lcov", "--remove", info_file, *src_remove_pattern, "-o", info_file],
                stdout=obtain_stdout(f"{info_file}_remove.log"),
            )

    if not processed_info:
        logger.error("No valid 'coverage*.info' data files were found.")
        logger.error(f"Searched directory: {info_report_dir} and all subdirectories.")
        raise Exception("No valid 'coverage*.info' data files were found.")

    # Run LCOV's genhtml to gather source-file pages
    branch_merged = Path("./merged_branch.info")
    toggle_merged = Path("./merged_toggle.info")
    lcov_genhtml_output_merged_log = Path("./lcov_genhtml_merged.out")

    # Find and classify coverage files
    branch_files, toggle_files = {}, {}
    files = Path(info_report_dir).glob("**/coverage_*.info")
    file_names = set()

    for file in files:
        if file.name.endswith("_branch.info"):
            file_names.add(file.name.removesuffix("_branch.info"))
            branch_files[file.name.removesuffix("_branch.info")] = file
        elif file.name.endswith("_toggle.info"):
            file_names.add(file.name.removesuffix("_toggle.info"))
            toggle_files[file.name.removesuffix("_toggle.info")] = file

    # Generate reports for each coverage file set
    for name_body in file_names:
        input_files = []
        if name_body in toggle_files:
            input_files.append(str(toggle_files[name_body]))
        if name_body in branch_files:
            input_files.append(str(branch_files[name_body]))
        test_name = name_body.removeprefix("coverage_")

        test_output_dir = Path(output_dir) / f"all_{test_name}"
        (test_output_dir / "_static").mkdir(parents=True, exist_ok=True)

        info_files = Path(info_report_dir).glob(f"**/*{test_name}*.info")
        lcov_html_dir = curr_dir / "lcov_report"

        lcov_genhtml_output_name = Path(f"./lcov_genhtml_{test_name}.log")
        lcov_genhtml(info_files, src_path, lcov_html_dir, lcov_genhtml_output_name)
        genhtml(
            input_files=input_files,
            output_dir=test_output_dir,
            src_path=src_path,
            project_name=project_name,
            test_name=test_name,
            logo_src=logo_src,
            logo_href=logo_href,
            html_src_dir=lcov_html_dir,
        )

        copy2(styles_dir / "main.css", test_output_dir)
        copy2(styles_dir / "cov.css", test_output_dir)
        copy2(
            styles_dir / "assets" / "chips-alliance-logo-mono.svg",
            test_output_dir / "_static" / "white.svg",
        )

    # Merge branch files
    merged_input_files = []

    if branch_files:
        lcov_merge(branch_files.values(), branch_merged)
        merged_input_files.append(str(branch_merged))

    # Merge toggle files
    if toggle_files:
        lcov_merge(toggle_files.values(), toggle_merged)
        merged_input_files.append(str(toggle_merged))

    # Generate final combined report
    final_output_dir = Path(output_dir) / "all"
    (final_output_dir / "_static").mkdir(parents=True, exist_ok=True)

    lcov_genhtml(
        merged_input_files,
        src_path,
        lcov_html_dir,
        lcov_genhtml_output_merged_log,
    )
    genhtml(
        input_files=merged_input_files,
        output_dir=final_output_dir,
        src_path=src_path,
        project_name=project_name,
        test_name="all",
        logo_src=logo_src,
        logo_href=logo_href,
        html_src_dir=lcov_html_dir,
    )

    copy2(styles_dir / "main.css", final_output_dir)
    copy2(styles_dir / "cov.css", final_output_dir)
    copy2(
        styles_dir / "assets" / "chips-alliance-logo-mono.svg",
        final_output_dir / "_static" / "white.svg",
    )


@main_func_log(logger, "Generate Coverage Reports")
def main(args):
    # Set output directory and create it if it doesn't exist
    report_dir = Path(args.report_dir)
    report_dir.mkdir(parents=True, exist_ok=True)

    generate_coverage_reports(
        output_dir=report_dir,
        src_pattern=args.src_pattern,
        src_remove_pattern=args.src_remove_pattern,
        src_path=args.src_path,
        logo_src=args.logo_src,
        logo_href=args.logo_href,
        info_report_dir=args.info_report_dir,
        project_name=args.src_project_name,
    )
