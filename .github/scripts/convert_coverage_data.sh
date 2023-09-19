#!/bin/bash

SELF_DIR="$(dirname $(readlink -f ${BASH_SOURCE[0]}))"
. ${SELF_DIR}/common.inc.sh

convert_coverage_data(){
    # This function uses verilator_coverage module to convert a coverage .dat
    # file(s) into an .info file(s) for further processing.
    # Args:
    #   DAT_DIR: path to dir containing coverage.dat file(s)
    DAT_DIR="${1:-results_verification}"
    echo -e "${COLOR_WHITE}======= Parse arguments =======${COLOR_CLEAR}"
    echo -e "${COLOR_WHITE}DAT_DIR = ${DAT_DIR}"
    echo -e "${COLOR_WHITE}===============================${COLOR_CLEAR}"

    # Function body
    FILES=`find ${DAT_DIR} -name "coverage*.dat"`
    if [ -z "$FILES" ]; then
        echo -e "${COLOR_RED}ERROR: No coverage data files were found${COLOR_CLEAR}"
        echo -e "${COLOR_RED}ERROR: Searched directory: `realpath ${DAT_DIR}`${COLOR_CLEAR}"
        echo -e "${COLOR_RED}ERROR: convert_coverage_data ended with errors${COLOR_CLEAR}"
        exit -1
    else
        for dat_file in ${FILES}; do
            info_file=`basename -s .dat ${dat_file}`.info
            info_realpath=`realpath \`dirname ${dat_file}\``
            info_file=${info_realpath}/${info_file}
            verilator_coverage --write-info ${info_file} ${dat_file}
            echo -e "${COLOR_WHITE}Conversion: ${dat_file} -> ${info_file} ${COLOR_GREEN}SUCCEEDED${COLOR_CLEAR}"
        done
    fi
}

# Example usage
# DAT_DIR="results_verification"
#
# convert_coverage_data $DAT_DIR

echo -e "${COLOR_WHITE}========== convert_coverage_data ==============${COLOR_CLEAR}"

convert_coverage_data "$@"

echo -e "${COLOR_WHITE}convert_coverage_data ${COLOR_GREEN}SUCCEEDED${COLOR_CLEAR}"
echo -e "${COLOR_WHITE}========== convert_coverage_data ==============${COLOR_CLEAR}"
