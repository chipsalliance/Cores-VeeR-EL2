#!/bin/bash

SELF_DIR="$(dirname $(readlink -f ${BASH_SOURCE[0]}))"
. ${SELF_DIR}/common.inc.sh

trap report_status EXIT

report_status(){
    rc=$?
    if [ $rc != 0 ]; then
        echo -e "${COLOR_WHITE}Test '${NAME}' ${COLOR_RED}FAILED${COLOR_CLEAR}"
    else
        mv ${DIR}/coverage.dat ${RESULTS_DIR}/
        echo -e "${COLOR_WHITE}Test '${NAME}' ${COLOR_GREEN}SUCCEEDED${COLOR_CLEAR}"
    fi
    exit $rc
}

run_regression_test(){
    # Run a regression test with coverage collection enabled
    # Args:
    # RESULTS_DIR -
    # BUS -
    # NAME -
    # COVERAGE -
    # USER_MODE - '1' for user mode, '0' for without user mode
    # CACHE WAYPACK -
    check_args_count $# 6
    RESULTS_DIR=$1
    BUS=$2
    NAME=$3
    COVERAGE=$4
    USER_MODE=$5
    ICACHE_WAYPACK=$6
    echo -e "${COLOR_WHITE}========== running test '${NAME}' =========${COLOR_CLEAR}"
    echo -e "${COLOR_WHITE} RESULTS_DIR    = ${RESULTS_DIR}${COLOR_CLEAR}"
    echo -e "${COLOR_WHITE} SYSTEM BUS     = ${BUS}${COLOR_CLEAR}"
    echo -e "${COLOR_WHITE} NAME           = ${NAME}${COLOR_CLEAR}"
    echo -e "${COLOR_WHITE} COVERAGE       = ${COVERAGE}${COLOR_CLEAR}"
    echo -e "${COLOR_WHITE} USER_MODE      = ${USER_MODE}${COLOR_CLEAR}"
    echo -e "${COLOR_WHITE} ICACHE_WAYPACK = ${ICACHE_WAYPACK}${COLOR_CLEAR}"

    COMMON_PARAMS="-set bitmanip_zba -set bitmanip_zbb -set bitmanip_zbc -set bitmanip_zbe -set bitmanip_zbf -set bitmanip_zbp -set bitmanip_zbr -set bitmanip_zbs -set=fpga_optimize=0"

    if [[ "${USER_MODE}" == "1" ]]; then
        COMMON_PARAMS="-set=user_mode=1 -set=smepmp=1 ${COMMON_PARAMS}"
    fi

    # DLCS_ENABLE may not be set
    set +u
    if [[ -z "${DCLS_ENABLE}" ]]; then
        DCLS_ENABLE="0"
    fi
    set -u

    if [[ "${DCLS_ENABLE}" ==  "1" ]]; then
        COMMON_PARAMS="-set lockstep_enable=1 -set lockstep_regfile_enable=1 ${COMMON_PARAMS}"
    fi

    COMMON_PARAMS="-set=icache_waypack=${ICACHE_WAYPACK} ${COMMON_PARAMS}"

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

    if [ "$NAME" = "pmp_random" ]; then
        EXTRA_ARGS='TB_MAX_CYCLES=8000000'
    else
        EXTRA_ARGS=
    fi

    # Run the test
    mkdir -p ${DIR}
    make -j`nproc` -C ${DIR} -f $RV_ROOT/tools/Makefile verilator $EXTRA_ARGS CONF_PARAMS="${PARAMS}" TEST=${NAME} COVERAGE=${COVERAGE} 2>&1 | tee ${LOG}
}

# Example usage
# RESULTS_DIR=results
# BUS=axi
# NAME=hello_world
# COVERAGE=branch
# USER_MODE=1
# run_regression_test.sh $RESULTS_DIR $BUS $NAME $COVERAGE $USER_MODE

check_args_count $# 6
run_regression_test "$@"
