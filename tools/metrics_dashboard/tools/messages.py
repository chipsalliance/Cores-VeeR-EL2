#!/usr/bin/env python3

import sys


class Messages:
    def __init__(self):
        self.errors, self.warnings, self.infos = [], [], []

    def add(self, other, prefix=""):
        for mine, theirs in ((self.errors, other.errors), (self.warnings, other.warnings), (self.infos, other.infos)):
            mine += [f"{prefix}{m}" for m in theirs]

    def print(self, verbose):
        for level, msgs in (("Info", self.infos if verbose else []), ("Warning", self.warnings), ("Error", self.errors)):
            for m in msgs:
                print(f"{level}: {m}", file=sys.stderr)


def add_message_arguments(parser):
    parser.add_argument("-v", "--verbose", action="store_true", help="show infos")
