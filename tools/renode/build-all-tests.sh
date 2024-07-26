#!/usr/bin/env bash
set -x
set -e

test_dir=${RV_ROOT}/testbench/tests/
tests="csr_access csr_misa csr_mstatus dhry insns irq modesw perf_counters pmp"

mkdir -p build
cd build
for test in ${tests}; do
    test_name=$(basename ${test})
    make CFLAGS=-DUSE_HTIF=false -f ${RV_ROOT}/tools/Makefile TEST=${test_name} program.hex
    mv ${test_name}.exe ../${test_name}.elf
    make -f ${RV_ROOT}/tools/Makefile clean
done
cd -
