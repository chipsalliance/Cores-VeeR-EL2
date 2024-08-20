from pathlib import Path
from shutil import copy

from .common import args_on_debug_logger, main_func_log, styles_dir, get_logger

logger = get_logger(__name__)


def copy_files(source, search_pattern, build_dir):
    files = list(build_dir.rglob(search_pattern))
    for file in files:
        logger.debug(f"Copy {source} to {file}")
        copy(source, file)


@main_func_log(logger, "Update webpage styles")
@args_on_debug_logger(logger)
def update_style(build_dir):
    """Replaces styles for sphinx build and injects assets into the `build_dir`."""

    build_dir = Path(build_dir)
    copy(
        styles_dir / "main.css",
        build_dir / "html" / "_static",
    )

    copy(
        styles_dir / "assets" / "chips-alliance-logo-mono.svg",
        build_dir / "html" / "_static" / "white.svg",
    )

    chips_cov_css = styles_dir / "cov.css"
    copy_files(chips_cov_css, chips_cov_css.name, build_dir)
