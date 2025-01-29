#!/bin/bash
# Expected usage:
# export RV_ROOT=/path/to/cores-veer-el2
# bash tools/hex_canned_update.sh

if [[ -z "$RV_ROOT" ]]; then
    echo "RV_ROOT is not set" 1>&2
    exit 1
fi

ASM=($(find $RV_ROOT/testbench/asm -maxdepth 1 -regex ".*\.\(s\|mki\)" -printf "%f\n" | sed 's/\.\(s\|mki\)$//' | grep -vE "(common|crt0)"))
CT=($(find $RV_ROOT/testbench/tests -mindepth 1 -type d -printf "%f\n"))
TESTS=("${ASM[@]}" "${CT[@]}")
echo "Detected tests:"
echo "---------------"
echo "${TESTS[@]}"
echo "---------------"

USER_MODES=("0" "1")

MAKE_CMD="make -f $RV_ROOT/tools/Makefile"
HEX_DIR=testbench/hex

# Clear old hex files
rm -rdf $HEX_DIR/*

PARAMS=""
for umode in ${USER_MODES[@]}; do
    mkdir -p $HEX_DIR/user_mode$umode
    for test in ${TESTS[@]}; do
        if [[ "$umode" == "1" ]]; then
            PARAMS="-set=user_mode=1 -set=smepmp=1 $PARAMS"
        # csr_mseccfg test is only available in user mode
        elif [[ "$test" == "csr_mseccfg" ]]; then
            continue
        fi
        $MAKE_CMD clean >/dev/null
        $MAKE_CMD program.hex CONF_PARAMS="$PARAMS" TEST=$test >/dev/null
        HEX_PATH="$HEX_DIR/user_mode$umode/$test.hex"
        echo "TEST = " $test
        if [ -f "program.hex" ]; then
            echo "Copying $test:program.hex to ["$HEX_PATH"]"
            cp program.hex $HEX_PATH
        else
            echo "program.hex not found. Possible build error."
            exit 1
        fi
    done
done
exit 0
