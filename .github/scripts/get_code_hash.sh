#!/bin/bash
# This script is responsible for computing hash for RISCV-DV generated programs
# cache.

HASHES=()
HASHES+=(`git submodule status third_party/riscv-dv | cut -d\  -f2`)
HASHES+=(`sha256sum tools/riscv-dv/code_fixup.py | cut -d\  -f1`)
HASHES+=(`sha256sum tools/riscv-dv/Makefile | cut -d\  -f1`)

echo ${HASHES[@]} | sha256sum | cut -d\  -f1
