#!/bin/bash
# This script is responsible for computing hash for RISCV-DV generated programs
# cache.

HASHES=()
HASHES+=($(git submodule status third_party/riscv-dv | cut -d\  -f2))
HASHES+=($(sha256sum tools/riscv-dv/code_fixup.py | cut -d\  -f1))
HASHES+=($(sha256sum tools/riscv-dv/testlist.yaml | cut -d\  -f1))
HASHES+=($(sha256sum tools/riscv-dv/riscv_core_setting.sv | cut -d\  -f1))
HASHES+=($(sha256sum tools/riscv-dv/Makefile | cut -d\  -f1))
HASHES+=($(sha256sum tools/riscv-dv/user_extension.svh | cut -d\  -f1))
HASHES+=($(sha256sum tools/riscv-dv/veer_directed_instr_lib.sv | cut -d\  -f1))

echo ${HASHES[@]} | sha256sum | cut -d\  -f1
