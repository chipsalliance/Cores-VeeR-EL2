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
    # USER_MODE - '1' for user mode, '0' for without user mode
    check_args_count $# 5
    RESULTS_DIR=$1
    BUS=$2
    NAME=$3
    COVERAGE=$4
    USER_MODE=$5
    echo -e "${COLOR_WHITE}========== running test '${NAME}' =========${COLOR_CLEAR}"
    echo -e "${COLOR_WHITE} RESULTS_DIR = ${RESULTS_DIR}${COLOR_CLEAR}"
    echo -e "${COLOR_WHITE} SYSTEM BUS  = ${BUS}${COLOR_CLEAR}"
    echo -e "${COLOR_WHITE} NAME        = ${NAME}${COLOR_CLEAR}"
    echo -e "${COLOR_WHITE} COVERAGE    = ${COVERAGE}${COLOR_CLEAR}"
    echo -e "${COLOR_WHITE} USER_MODE   = ${USER_MODE}${COLOR_CLEAR}"

    COMMON_PARAMS=""

    if [[ "${USER_MODE}" == "1" ]]; then
        COMMON_PARAMS="-set=user_mode=1 -set=smepmp=1 ${COMMON_PARAMS}"
    fi

    if [[ "${BUS}" == "axi" ]]; then
        PARAMS="-set build_axi4 ${COMMON_PARAMS}"
    elif [[ "${BUS}" == "ahb" ]]; then
        PARAMS="-set build_ahb_lite ${COMMON_PARAMS}"
    else
        echo -e "${COLOR_RED}Unknown system bus type '${BUS}'${COLOR_CLEAR}"
        exit 1
    fi

    echo -e "${COLOR_WHITE} CONF PARAMS = ${PARAMS}${COLOR_CLEAR}"

    mkdir -p ${RESULTS_DIR}
    LOG="${RESULTS_DIR}/test_${NAME}_${COVERAGE}_${USER_MODE}.log"
    touch ${LOG}
    DIR="run_${NAME}_${COVERAGE}_${USER_MODE}"

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
# USER_MODE=1
# run_regression_test.sh $RESULTS_DIR $BUS $NAME $COVERAGE $USER_MODE

check_args_count $# 5
run_regression_test "$@"
