#!/bin/bash
# Expected usage:
# Inside `cores-veer-el2` directory run:
# bash tools/hex_canned_update.sh

export RV_ROOT=$(pwd)
echo "RV_ROOT =" $RV_ROOT

TESTS=(hello_world hello_world_dccm hello_world_iccm cmark cmark_dccm cmark_iccm dhry)
MAKE_CMD="make -f $RV_ROOT/tools/Makefile"
HEX_DIR=testbench/hex

for test in ${TESTS[@]}; do
    $MAKE_CMD clean > /dev/null
    $MAKE_CMD program.hex TEST=$test > /dev/null
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

