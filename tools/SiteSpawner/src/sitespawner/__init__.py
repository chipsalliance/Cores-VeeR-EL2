import argparse
import logging
from importlib.metadata import PackageNotFoundError, version
from pathlib import Path

from .common import root_dir, get_logger, set_loglevel
from .convert_data import convert_data
from .gen_coverage_report import main as gen
from .update_webpage import update_webpage

try:
    dist_name = "SiteSpawner"
    __version__ = version(dist_name)
except PackageNotFoundError:
    __version__ = "unknown"
finally:
    del version, PackageNotFoundError

logger = get_logger(__name__)


def create_subparser(subparsers, name, description, help, args_list, handler):
    """
    Helper function to create a subparser with given arguments and handler.

    Parameters
    ----------
    subparsers : _SubParsersAction
        Subparsers of parent's parser where the new subparser will be added.
    name : str
        Name for the subparser.
    description : str
        Description for the subparser.
    help : str
        The help text for the subparser.
    args_list: list
        A list of dictionaries, each containing argument settings.
    handler : Callable[Namespace]
        Function to be executed for this subparser.
    """
    parser = subparsers.add_parser(name, help=help, description=description)
    for arg in args_list:
        parser.add_argument(arg["name"], **arg["options"])
    parser.set_defaults(handler=handler)


def convert_handler(args):
    convert_data(args)


def reports_handler(args):
    if Path(root_dir).absolute == Path(args.report_dir).absolute:
        raise ValueError(f"Existing webpage root and output paths mustn't be the same: {args.root}")
    gen(args)


def webpage_handler(args):
    update_webpage(
        args.loc_github_ref_name,
        args.loc_github_event_name,
        args.pr_number,
        args.doc_project_name,
        args.include_documentation,
        args.page_url,
    )


def all_handler(args):
    # Convert Data
    logger.info("Step 1/3: Convert data")
    convert_handler(args)

    # Generate reports
    logger.info("Step 2/3: Generate coverage reports")
    reports_handler(args)

    # Generate final pages, update styles for webpage, copy static elements
    logger.info("Step 3/3: Update / Create webpage")
    webpage_handler(args)


def setup_parser():
    parser = argparse.ArgumentParser(
        description="Generating coverage reports with Verilator's *.dat files."
    )
    parser.add_argument(
        "--version",
        action="version",
        version=f"SiteSpawner {__version__}",
    )
    parser.add_argument(
        "-v",
        "--verbose",
        dest="loglevel",
        help="set loglevel to INFO",
        action="store_const",
        const=logging.INFO,
    )
    parser.add_argument(
        "-d",
        "--debug",
        dest="loglevel",
        help="set loglevel to DEBUG",
        action="store_const",
        const=logging.DEBUG,
    )

    dat_dir = {
        "name": "--dat-dir",
        "options": {
            "metavar": "dat_dir",
            "type": str,
            "help": "Path to directory containing *.dat files",
            "required": True,
        },
    }
    info_dir = {
        "name": "--info-dir",
        "options": {
            "metavar": "info_dir",
            "type": str,
            "help": (
                "Path to directory where *.info files will be stored.\n"
                "If not specified, *.info will be stored where its *.dat counterpart is."
            ),
        },
    }

    subparsers = parser.add_subparsers(dest="cmd")
    convert_args = [dat_dir, info_dir]
    create_subparser(
        subparsers=subparsers,
        name="convert",
        description="Convert Coverage Data",
        help="Convert Verilator's *.dat coverage files into *.info files",
        args_list=convert_args,
        handler=convert_handler,
    )

    logo_src = {
        "name": "--logo-src",
        "options": {
            "metavar": "logo_src",
            "type": str,
            "default": "_static/white.svg",
            "help": "Path to logo to be attached with the report, relative to index.html file in the destination dir.",
        },
    }
    logo_href = {
        "name": "--logo-href",
        "options": {
            "metavar": "logo_href",
            "default": "index.html",
            "type": str,
            "help": "URL to be associated with the logo.",
        },
    }
    report_dir = {
        "name": "--report-dir",
        "options": {
            "metavar": "report_dir",
            "default": "report",
            "type": str,
            "help": "Coverage dashboard directory",
        },
    }
    src_pattern = {
        "name": "--src-pattern",
        "options": {
            "metavar": "src_pattern",
            "default": "*",
            "type": str,
            "help": "Pattern used for designs' source file extraction.",
        },
    }
    src_remove_pattern = {
        "name": "--src-remove-pattern",
        "options": {
            "metavar": "src_remove_pattern",
            "action": "append",
            "default": None,
            "type": str,
            "help": "Pattern used for removing designs' source files from coverage report generation.",
        },
    }
    src_path = {
        "name": "src_path",
        "options": {
            "metavar": "src_path",
            "default": None,
            "type": str,
            "help": (
                "Path to design's source code. "
                "Last segment of path will be displayed in the report. "
                "If not specified, the source code path will be "
                "the longest common path of reported source files."
            ),
        },
    }
    info_report_dir = {
        "name": "--info-report-dir",
        "options": {
            "metavar": "info_report_dir",
            "type": str,
            "help": (
                "Path to directory with *.info coverage files.\n"
                "If not specified will recursively search from current directory."
            ),
        },
    }
    src_project_name = {
        "name": "--src-project-name",
        "options": {
            "metavar": "src_project_name",
            "type": str,
            "default": "Project",
            "help": ("Name of the project that is displayed in the webpage for sources."),
        },
    }
    reports_args = [
        logo_src,
        logo_href,
        report_dir,
        src_pattern,
        src_path,
        info_report_dir,
        src_remove_pattern,
        src_project_name,
    ]
    create_subparser(
        subparsers=subparsers,
        name="reports",
        description="Generate Coverage Reports",
        help=("Gathers *.info files and generates the collective HTML coverage dashboard."),
        args_list=reports_args,
        handler=reports_handler,
    )

    ref_name = {
        "name": "--loc-github-ref-name",
        "options": {
            "type": str,
            "metavar": "loc_github_ref_name",
            "help": "GitHub ref name, use ${{ github.ref }}",
            "required": True,
        },
    }
    event_name = {
        "name": "--loc-github-event-name",
        "options": {
            "type": str,
            "metavar": "loc_github_event_name",
            "help": "GitHub event name, use ${{ github.event_name }}",
            "required": True,
        },
    }
    pr_number = {
        "name": "--pr-number",
        "options": {
            "type": int,
            "metavar": "pr_number",
            "help": "Number of the PR, e.g., 42",
            "required": True,
        },
    }
    page_url = {
        "name": "--page-url",
        "options": {
            "type": str,
            "metavar": "page_url",
            "help": "Base URL of the website. Otherwise, will apply relative reference for redirect.",
        },
    }
    doc_project_name = {
        "name": "--doc-project-name",
        "options": {
            "metavar": "doc_project_name",
            "type": str,
            "default": "Project",
            "help": ("Name of the project used in documentation."),
        },
    }
    include_documentation = {
        "name": "--include-documentation",
        "options": {
            "action": "store_true",
            "dest": "include_documentation",
            "help": "Whethet to include documentation in the built webpage",
        },
    }
    webpage_args = [
        ref_name,
        event_name,
        pr_number,
        page_url,
        doc_project_name,
        include_documentation,
    ]
    create_subparser(
        subparsers=subparsers,
        name="webpage",
        description="Update / assemble webpage with coverage reports",
        help="Update webpage based on GitHub refs and events.",
        args_list=webpage_args,
        handler=webpage_handler,
    )

    create_subparser(
        subparsers=subparsers,
        name="all",
        description="Execute all steps consecutively.",
        help="Perform data conversion, coverage dashboard generation and assemble the webpage.",
        args_list=convert_args + reports_args + webpage_args,
        handler=all_handler,
    )

    return parser


def main():
    parser = setup_parser()
    args = parser.parse_args()

    if args.loglevel:
        set_loglevel(args.loglevel)

    if args.cmd:
        args.handler(args)
    else:
        parser.print_help()


if __name__ == "__main__":
    main()
