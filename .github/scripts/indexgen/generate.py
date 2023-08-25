#!/usr/bin/env python3
import argparse
import os
import shutil

import jinja2

# ==============================================================================


def render_template(src, dst, **kwargs):
    """
    Renders a jinja2 template file to another file
    """
    with open(src, "r") as fp:
        tpl = jinja2.Template(fp.read())
    with open(dst, "w") as fp:
        fp.write(tpl.render(**kwargs))

# ==============================================================================


def make_coverage_report_index(branch, root, output, templates):
    """
    Prepares coverage report index page
    """

    keys = ["all", "branch", "toggle", "functional"]
    path = os.path.join(root, "coverage_dashboard")

    # Collect summary reports
    summary = {k: None for k in keys}
    for key in keys:
        file = key
        fname = os.path.join(path, file)
        if os.path.isdir(fname):
            summary[key] = file

    # Collect individual test reports
    individual = {k: dict() for k in keys}
    for key in keys:
        pfx = key + "_"

        if not os.path.isdir(path):
            continue

        for file in sorted(os.listdir(path)):
            fname = os.path.join(path, file)
            if not os.path.isdir(fname):
                continue
            if not file.startswith(pfx):
                continue

            # Extract test name
            test_name = file[len(pfx):]

            # Append the report
            individual[key][test_name] = file

    # Render the template
    params = {
        "ref":          branch + "_coverage_dashboard",
        "summary":      summary,
        "individual":   individual,
    }

    os.makedirs(output, exist_ok=True)
    render_template(
        os.path.join(templates, "coverage_dashboard.md"),
        os.path.join(output,    "coverage_dashboard.md"),
        **params
    )


def make_verification_report_index(branch, root, output, templates):
    """
    Prepares verification tests report index page
    """

    path = os.path.join(root, "verification_dashboard")

    # Collect tests
    tests = set()

    if os.path.isdir(path):
        for file in sorted(os.listdir(path)):
            if not file.startswith("webpage_"):
                continue

            test_name = file.replace("webpage_", "")
            tests.add(test_name)

    # Render the template
    params = {
        "ref":          branch + "_verification_dashboard",
        "tests":        tests,
    }

    os.makedirs(output, exist_ok=True)
    render_template(
        os.path.join(templates, "verification_dashboard.md"),
        os.path.join(output,    "verification_dashboard.md"),
        **params
    )


def make_dev_index(branches, output, templates):
    """
    Prepares the branch/pr index page
    """

    params = {
        "branches": branches,
    }

    render_template(
        os.path.join(templates, "dev.md"),
        os.path.join(output,    "dev.md"),
        **params
    )

# ==============================================================================


def main():

    # Parse args
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--template",
        type=str,
        required=True,
        help="Templates path",
    )
    parser.add_argument(
        "--root",
        type=str,
        default=None,
        help="Existing webpage root path",
    )
    parser.add_argument(
        "--output",
        type=str,
        required=True,
        help="Output path",
    )

    args = parser.parse_args()

    # Check
    if os.path.abspath(args.root) == os.path.abspath(args.output):
        print("Error: Existing webpage root and output paths mustn't be the same")
        exit(-1)

    # Reports for the main branch
    make_coverage_report_index(
        "main",
        os.path.join(args.root,   "main"),
        os.path.join(args.output, "main"),
        args.template
    )

    make_verification_report_index(
        "main",
        os.path.join(args.root,   "main"),
        os.path.join(args.output, "main"),
        args.template
    )

    # Reports for development branches / pull requests
    branches = []
    path = os.path.join(args.root, "dev")

    if os.path.isdir(path):
        for file in os.listdir(path):
            if not os.path.isdir(os.path.join(path, file)):
                continue
            branches.append(file)

            make_coverage_report_index(
                file,
                os.path.join(args.root,   "dev", file),
                os.path.join(args.output, "dev", file),
                args.template
            )

            make_verification_report_index(
                file,
                os.path.join(args.root,   "dev", file),
                os.path.join(args.output, "dev", file),
                args.template
            )

    # Prepare the branch/pr index page
    make_dev_index(branches, args.output, args.template)

    # Copy other files/pages
    files = [
        "conf.py",
        "main.md",
        "index.md",
    ]
    for file in files:
        shutil.copy(
            os.path.join(args.template, file),
            os.path.join(args.output,   file),
        )


if __name__ == "__main__":
    main()
