#!/bin/bash
# This script is responsible for computing hash for OpenOCD test
# cache.

FILES=$(find design testbench \
        -name "*.c" -o \
        -name "*.h" -o \
        -name "*.v" -o \
        -name "*.sv" -o \
        -name "*.vh")

HASHES=()

for file in $FILES; do
    HASHES+=($(sha256sum $file | cut -d\  -f1))
done

echo ${HASHES[@]} | sha256sum | cut -d\  -f1
