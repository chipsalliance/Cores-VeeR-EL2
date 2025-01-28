#!/bin/bash
# Expected usage:
# export RV_ROOT=/path/to/cores-veer-el2
# bash tools/hex_canned_update.sh

if [[ -z "$RV_ROOT" ]]; then
   echo "RV_ROOT is not set" 1>&2
   exit 1
fi

ASM=( $(find $RV_ROOT/testbench/asm -maxdepth 1 -type f -regex ".*\.s" -printf "%f\n" | sed 's/\.s$//' | grep -vE "(common|crt0)") )
CT=( $(find $RV_ROOT/testbench/tests/ -mindepth 1 -type d -printf "%f\n") )
TESTS=( "${ASM[@]}" "${CT[@]}" )

MAKE_CMD="make -f $RV_ROOT/tools/Makefile"
HEX_DIR=testbench/hex
PARAMS=""

for test in ${TESTS[@]}; do
    if [[ "${test}" == "csr_mseccfg" ]]; then
        PARAMS="-set=user_mode=1 -set=smepmp=1 ${PARAMS}"
    fi
   $MAKE_CMD clean > /dev/null
   $MAKE_CMD program.hex CONF_PARAMS="${PARAMS}" TEST=$test > /dev/null
   echo "TEST = " $test
   if [ -f "program.hex" ]; then
       echo "Copying $test:program.hex to ["$HEX_DIR/$test.hex"]"
       cp program.hex $HEX_DIR/$test.hex
   else
       echo "program.hex not found. Possible build error."
       exit 1
   fi
done

exit 0

