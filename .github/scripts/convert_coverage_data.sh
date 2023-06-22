#!/bin/bash

SELF_DIR="$(dirname $(readlink -f ${BASH_SOURCE[0]}))"
. ${SELF_DIR}/common.inc.sh

convert_coverage_data(){
    # This function uses verilator_coverage module to convert a coverage .dat file:
    #   ${DAT_DIR}/coverage.dat
    # into an .info file:
    #   ${RESULTS_DIR}/${FILE_PREFIX}_${COVERAGE}.info
    # Args:
    #   COVERAGE : type of coverage
    #   DAT_DIR: path to dir containing coverage.dat file
    #   RESULTS_DIR: path to dir, where .info file will be placed
    #   FILE_PREFIX: prefix used in the name of coverage_.info
    check_args_count $# 4
    COVERAGE=$1
    DAT_DIR=$2
    RESULTS_DIR=$3
    FILE_PREFIX=$4
    echo -e "${COLOR_WHITE}======= convert_coverage_data =======${COLOR_CLEAR}"
    echo -e "${COLOR_WHITE}COVERAGE    = ${COVERAGE}"
    echo -e "${COLOR_WHITE}DAT_DIR     = ${DAT_DIR}"
    echo -e "${COLOR_WHITE}RESULTS_DIR = ${RESULTS_DIR}"
    echo -e "${COLOR_WHITE}FILE_PREFIX = ${FILE_PREFIX}"
    echo -e "${COLOR_WHITE}========== ${COVERAGE} coverage ==========${COLOR_CLEAR}"

    # Function body
    if ! [ -f "${DAT_DIR}/coverage.dat" ]; then
        echo -e "${COLOR_WHITE}coverage.dat not found in dir=${DAT_DIR} ${COLOR_RED}FAIL${COLOR_CLEAR}"
        exit -1
    else
        mkdir -p ${RESULTS_DIR}
        cp ${DAT_DIR}/coverage.dat ${RESULTS_DIR}/${FILE_PREFIX}_${COVERAGE}.dat
        verilator_coverage --write-info ${RESULTS_DIR}/${FILE_PREFIX}_${COVERAGE}.info ${RESULTS_DIR}/${FILE_PREFIX}_${COVERAGE}.dat
        echo -e "${COLOR_WHITE}Conversion: ${DAT_DIR}/coverage.dat -> ${RESULTS_DIR}/${FILE_PREFIX}_${COVERAGE}.info ${COLOR_GREEN}SUCCEEDED${COLOR_CLEAR}"
    fi
}

# Example usage
# RESULTS_DIR="results"
# COVERAGE="branch"
# DAT_DIR="."
# FILE_PREFIX="coverage_test"
#
# convert_coverage_data $COVERAGE $DAT_DIR $RESULTS_DIR $FILE_PREFIX

check_args_count $# 4
convert_coverage_data "$@"
