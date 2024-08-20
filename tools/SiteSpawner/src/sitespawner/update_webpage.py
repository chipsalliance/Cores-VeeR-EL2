import os
import subprocess
from pathlib import Path
from shutil import copy2, copytree, rmtree
from jinja2 import Environment, FileSystemLoader

from .common import (
    args_on_debug_logger,
    main_func_log,
    webpage_template_dir,
    template_dir,
    get_logger,
)
from .generate import generate
from .update_style import update_style

logger = get_logger(__name__)


@args_on_debug_logger(logger)
def replace_dir(src_dir, dst_dir):
    """Removes the destination directory, creates an empty destination directory,
    and copies contents of source directory to destination directory."""
    src_path = Path(src_dir)
    dst_path = Path(dst_dir)

    if not src_path.is_dir():
        return logger.warning("Source directory not present!")

    # Replace existing pages with new ones
    if dst_path.exists():
        rmtree(dst_path)
    dst_path.mkdir(parents=True, exist_ok=True)

    # Copy items to the new directory
    for item in src_path.iterdir():
        copytree(item, dst_path / item.name, dirs_exist_ok=True)


@main_func_log(logger, "Update webpage")
@args_on_debug_logger(logger)
def update_webpage(loc_github_ref_name, loc_github_event_name, pr_number, page_url=None):
    """Updates the public part of the gh-pages based on git refs, github events, and PR numbers."""
    # Determine the directory based on the GitHub ref and event
    if loc_github_ref_name == "main":
        directory = "main"
    elif loc_github_event_name == "pull_request":
        directory = f"dev/{pr_number}"
    elif loc_github_event_name == "push":
        directory = f'dev/{loc_github_ref_name.replace("/", "_")}'
    else:
        logger.error(f"Invalid event type: {loc_github_event_name} on ref: {loc_github_ref_name}")
        raise ValueError("Unknown deployment type")

    md_source_dir = Path("source")
    legacy_page_dir = Path("public.old")
    new_page_dir = Path("public.new")

    replace_dir("coverage_dashboard", legacy_page_dir / "html" / directory / "coverage_dashboard")

    if md_source_dir.exists():
        rmtree(md_source_dir)
    else:
        md_source_dir.mkdir(parents=True)

    logger.info("Syncing directories...")

    for root, dirs, files in os.walk(legacy_page_dir):
        root = Path(root)
        relative_path = root.relative_to(legacy_page_dir)
        dst_dir = new_page_dir / relative_path
        # Create directories in destination
        for dir_name in dirs:
            (dst_dir / dir_name).mkdir(parents=True, exist_ok=True)
        # Copy files to destination
        for fname in files:
            src_file = root / fname
            dst_file = dst_dir / fname
            copy2(src_file, dst_file)

    generate(webpage_template_dir, str(legacy_page_dir / "html"), str(md_source_dir))

    SPHINXBUILD = os.getenv("SPHINXBUILD", "sphinx-build")
    SPHINXOPTS = os.getenv("SPHINXOPTS")

    logger.info("Building the HTML documentation using Sphinx...")

    cmd = [SPHINXBUILD, "-M", "html", str(md_source_dir), str(new_page_dir)]

    if SPHINXOPTS:
        cmd.append(SPHINXOPTS)

    subprocess.run(cmd, cwd=legacy_page_dir.parent, check=True)

    update_style(new_page_dir)

    if not page_url:
        page_url = "."
    else:
        page_url = page_url.rstrip("//")

    env = Environment(loader=FileSystemLoader(template_dir))
    redirect = env.get_template("redirect.html").render(page_url=page_url)

    with open(new_page_dir / "index.html", "w") as f:
        print(redirect, file=f)
