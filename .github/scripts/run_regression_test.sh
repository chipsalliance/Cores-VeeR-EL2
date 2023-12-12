#!/bin/bash

SELF_DIR="$(dirname $(readlink -f ${BASH_SOURCE[0]}))"
. ${SELF_DIR}/common.inc.sh

run_regression_test(){
    # Run a regression test with coverage collection enabled
    # Args:
    # RESULTS_DIR -
    # BUS -
    # NAME -
    # COVERAGE -
    check_args_count $# 4
    RESULTS_DIR=$1
    BUS=$2
    NAME=$3
    COVERAGE=$4
    echo -e "${COLOR_WHITE}========== running test '${NAME}' =========${COLOR_CLEAR}"
    echo -e "${COLOR_WHITE} RESULTS_DIR = ${RESULTS_DIR}${COLOR_CLEAR}"
    echo -e "${COLOR_WHITE} SYSTEM BUS  = ${BUS}${COLOR_CLEAR}"
    echo -e "${COLOR_WHITE} NAME        = ${NAME}${COLOR_CLEAR}"
    echo -e "${COLOR_WHITE} COVERAGE    = ${COVERAGE}${COLOR_CLEAR}"

    if [[ "${BUS}" == "axi" ]]; then
        PARAMS="-set build_axi4"
    elif [[ "${BUS}" == "ahb" ]]; then
        PARAMS="-set build_ahb_lite"
    else
        echo -e "${COLOR_RED}Unknown system bus type '${BUS}'${COLOR_CLEAR}"
        exit 1
    fi

    mkdir -p ${RESULTS_DIR}
    LOG="${RESULTS_DIR}/test_${NAME}_${COVERAGE}.log"
    touch ${LOG}
    DIR="run_${NAME}_${COVERAGE}"

    # Run the test
    mkdir -p ${DIR}
    make -j`nproc` -C ${DIR} -f $RV_ROOT/tools/Makefile verilator CONF_PARAMS="${PARAMS}" TEST=${NAME} COVERAGE=${COVERAGE} 2>&1 | tee ${LOG}
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
# BUS=axi
# NAME=hello_world
# COVERAGE=branch
# run_regression_test.sh $RESULTS_DIR $BUS $NAME $COVERAGE

check_args_count $# 4
run_regression_test "$@"



