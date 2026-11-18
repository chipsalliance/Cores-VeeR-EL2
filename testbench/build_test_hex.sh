#!/usr/bin/env bash
# tools/build_test_hex.sh <TEST> [make args...]   e.g. csr_access target=default USER_MODE=1
set -euo pipefail
test_name=$1; shift
export RV_ROOT=$(cd "$(dirname "$0")/.." && pwd)
work=$(mktemp -d); trap 'rm -rf "$work"' EXIT
output_dir=${PROGRAM_OUTPUT_DIR:-"$RV_ROOT/programs"}
mkdir -p "$output_dir"
( cd "$work" && make -f "$RV_ROOT/tools/Makefile" program.hex TEST="$test_name" "$@" )
if [ -n "${PROGRAM_OUTPUT_DIR:-}" ]; then
  cp "$work/program.hex" "$output_dir/$test_name.hex"
  if [ -f "$work/$test_name.sym" ]; then cp "$work/$test_name.sym" "$output_dir/$test_name.sym"
  else : > "$output_dir/$test_name.dat"; fi
else
  cp "$work/program.hex" "$output_dir/program.hex"
  if [ -f "$work/$test_name.sym" ]; then cp "$work/$test_name.sym" "$output_dir/program.sym"
  else : > "$output_dir/program.sym"; fi
fi
