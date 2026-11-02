#!/usr/bin/env bash

set -euo pipefail

prefix_macros="$1"
output="$2"
prefix="$3"
snapshot_directory="$4"
shift 4

while [ "$#" -gt 0 ]; do
    source="$1"
    destination="$output/$2"
    mkdir -p "$(dirname "$destination")"
    cp "$source" "$destination"
    shift 2
done

RV_ROOT="$output" \
DEFINES_PATH="$output/$snapshot_directory" \
DESIGN_DIR="$output/design" \
PREFIX="$prefix" \
"$prefix_macros"
