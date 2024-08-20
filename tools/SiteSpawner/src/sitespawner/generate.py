from pathlib import Path
from shutil import copy

import jinja2

from .common import args_on_debug_logger, get_logger

logger = get_logger(__name__)


def render_template(src, dst, **kwargs):
    """
    Renders a jinja2 template file to another file
    """
    with open(src, "r") as fr, open(dst, "w") as fw:
        tpl = jinja2.Template(fr.read())
        fw.write(tpl.render(**kwargs))


@args_on_debug_logger(logger)
def make_coverage_report_index(branch, root, output, templates):
    """Prepares coverage report index page."""
    # Coverage types individual dashboards accumulate
    # Coverage dashboard displays coverage types side-by-side
    # on singular page; all files are prefixed with 'all'.
    cov_dashboards = ["all"]
    path = Path(root) / "coverage_dashboard"

    # Collect summary reports
    summary = {k: k if (path / k).is_dir() else None for k in cov_dashboards}

    # Collect individual test reports
    individual = {k: dict() for k in cov_dashboards}
    for key in cov_dashboards:
        pfx = f"{key}_"

        if not path.exists():
            logger.warning(f"Not found {path}...")
            logger.warning("Skipping")
            continue

        for file in sorted(path.iterdir()):
            if not file.is_dir():
                continue

            fname = file.name
            if not fname.startswith(pfx):
                continue

            # Extract test name
            test_name = fname.removeprefix(pfx)

            # Append the report
            individual[key][test_name] = fname

    # Render the template
    params = {
        "ref": branch + "_coverage_dashboard",
        "summary": summary,
        "individual": individual,
    }

    output.mkdir(parents=True, exist_ok=True)
    render_template(
        templates / "coverage_dashboard.md",
        output / "coverage_dashboard.md",
        **params,
    )


@args_on_debug_logger(logger)
def make_dev_index(branches, output, templates):
    """Prepares the branch/pr index page."""
    params = {"branches": branches}
    render_template(templates / "dev.md", output / "dev.md", **params)


def generate(template, root, output):
    """Processes webpage *.md templates."""
    template = Path(template)
    root = Path(root)
    output = Path(output)

    # Reports for the main branch
    make_coverage_report_index("main", root / "main", output / "main", template)

    # Reports for development branches / pull requests
    branches = []

    path = root / "dev"

    if path.is_dir():
        for filepath in path.iterdir():
            if not filepath.is_dir():
                continue

            fname = filepath.name
            branches.append(fname)
            make_coverage_report_index(
                fname, root / "dev" / fname, output / "dev" / fname, template
            )

    # Prepare the branch/pr index page
    make_dev_index(branches, output, template)

    # Copy other files/pages
    files = ["conf.py", "main.md", "index.md"]
    for file in files:
        copy(template / file, output / file)
