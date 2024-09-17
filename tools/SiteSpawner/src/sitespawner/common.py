import logging
from functools import wraps
from pathlib import Path
import sys

from termcolor import colored
from typing import Any


class CustomFormatter(logging.Formatter):
    grey = "\x1b[37m"
    blue = "\x1b[1;36m"
    yellow = "\x1b[33;20m"
    red = "\x1b[31;20m"
    bold_red = "\x1b[31;1m"
    reset = "\x1b[0m"
    logformat = "[%(asctime)s] %(levelname)s:%(name)s:%(message)s"

    FORMATS = {
        logging.DEBUG: grey + logformat + reset,
        logging.INFO: blue + logformat + reset,
        logging.WARNING: yellow + logformat + reset,
        logging.ERROR: red + logformat + reset,
        logging.CRITICAL: bold_red + logformat + reset,
    }

    def format(self, record):
        log_fmt = self.FORMATS.get(record.levelno)
        formatter = logging.Formatter(log_fmt, "%Y-%m-%d %H:%M:%S")
        return formatter.format(record)


# Resolve paths to package resources
root_dir = Path(__file__).parent.parent
template_dir = root_dir / "template"
coverage_dashboard_template_dir = template_dir / "coverage_report"
webpage_template_dir = template_dir / "webpage"
styles_dir = root_dir / "styles"


def get_logger(name: str) -> logging.Logger:
    """Returns a logger with the specified name.

    It also makes sure that the root logger
    is initialised with a proper handler."""
    logger = logging.getLogger(name)

    # Make sure that the root logger is initialised
    setup_root_logger(stream=sys.stdout)
    return logger


def setup_root_logger(stream: Any):
    """Setups the root logger by setting its verbosity and adding
    a handler with custom formatting to it."""
    # Obtaining the root logger
    logger = logging.getLogger()

    # If custom handler does exist, it means it was already initialised
    if not logger.hasHandlers():
        ch = logging.StreamHandler(stream=stream)
        ch.setFormatter(CustomFormatter())
        logger.addHandler(ch)


def set_loglevel(loglevel: int):
    """Set the log level of the root logger."""
    logger = logging.getLogger()
    logger.setLevel(loglevel)


def args_on_debug_logger(logger):
    def _args_on_debug_logger(func):
        @wraps(func)
        def wrapper(*args, **kwargs):
            logger.debug(f"{func.__name__}: Args: {args} Kwargs: {kwargs}")
            return func(*args, **kwargs)

        return wrapper

    return _args_on_debug_logger


def main_func_log(logger, step_name):
    def _main_func_log(func):
        @wraps(func)
        def wrapper(*args, **kwargs):
            logger.info(step_name)
            try:
                res = func(*args, **kwargs)
                logger.info(f'{func.__name__} {colored("SUCCESS", "green")}')
                return res
            except Exception as e:
                logger.error(f'{func.__name__} {colored("FAILED", "red")}')
                raise e

        return wrapper

    return _main_func_log
