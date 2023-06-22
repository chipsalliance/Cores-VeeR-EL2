#!/bin/bash

SELF_DIR="$(dirname $(readlink -f ${BASH_SOURCE[0]}))"
. ${SELF_DIR}/common.inc.sh

run_regression_test(){
    # Run a regression test with coverage collection enabled
    # Args:
    # RESULTS_DIR -
    # NAME -
    # COVERAGE -
    check_args_count $# 3
    RESULTS_DIR=$1
    NAME=$2
    COVERAGE=$3
    echo -e "${COLOR_WHITE}========== running test '${NAME}' =========${COLOR_CLEAR}"
    echo -e "${COLOR_WHITE} RESULTS_DIR = ${RESULTS_DIR}${COLOR_CLEAR}"
    echo -e "${COLOR_WHITE} NAME        = ${NAME}${COLOR_CLEAR}"
    echo -e "${COLOR_WHITE} COVERAGE    = ${COVERAGE}${COLOR_CLEAR}"

    mkdir -p ${RESULTS_DIR}
    LOG="${RESULTS_DIR}/test_${NAME}_${COVERAGE}.log"
    touch ${LOG}
    DIR="run_${NAME}_${COVERAGE}"

    # Run the test
    mkdir -p ${DIR}
    make -j`nproc` -C ${DIR} -f $RV_ROOT/tools/Makefile verilator TEST=${NAME} COVERAGE=${COVERAGE} 2>&1 | tee ${LOG}
    if [ ! -f "${DIR}/coverage.dat" ]; then
        echo -e "${COLOR_WHITE}Test '${NAME}' ${COLOR_RED}FAILED${COLOR_CLEAR}"
        exit 1
    else
        mv ${DIR}/coverage.dat ${RESULTS_DIR}/
        echo -e "${COLOR_WHITE}Test '${NAME}' ${COLOR_GREEN}SUCCEEDED${COLOR_CLEAR}"
        exit 0
    fi
}

# Example usage
# RESULTS_DIR=results
# NAME=hello_world
# COVERAGE=branch
# run_regression_test.sh $RESULTS_DIR $NAME $COVERAGE

check_args_count $# 3
run_regression_test "$@"



