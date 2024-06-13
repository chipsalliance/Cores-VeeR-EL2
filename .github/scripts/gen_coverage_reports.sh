#!/bin/bash

#--------------#
#    LCOV
#--------------#
generate_coverage_reports(){
    # This function creates...
    # Args
    # OUTPUT_DIR - directory, where index.html will be placed
    # GIT_SHA - git revision
    check_args_count $# 2
    OUTPUT_DIR=$1
    GENHTML_OPTS=$2
    echo -e "${COLOR_WHITE}========== generate_coverage_reports =========${COLOR_CLEAR}"
    echo -e "${COLOR_WHITE}OUTPUT_DIR      = ${OUTPUT_DIR}${COLOR_CLEAR}"
    echo -e "${COLOR_WHITE}GENHTML_OPTS    = ${GENHTML_OPTS}${COLOR_CLEAR}"

    for info_file in `find . -name '*.info'`; do
        lcov --extract ${info_file} \*design\* -o ${info_file}
    done

    for COVERAGE in branch toggle all functional; do
        DIR=${OUTPUT_DIR}/${COVERAGE}
        # Summary
        mkdir -p ${DIR}
        FILES=`find . -name "coverage_*_${COVERAGE}.info" -printf "%P\n"`

        if [ -z "$FILES" ]; then
            echo -e "${COLOR_WHITE}There are no files for coverage ${COVERAGE} ${COLOR_YELLOW}WARNING${COLOR_CLEAR}"
        else
            # genhtml -o ${DIR} -t "all" ${GENHTML_OPTS} ${FILES}
            genhtml -o ${DIR} -t "all" --header-title "RTL ${COVERAGE} coverage report" ${GENHTML_OPTS} ${FILES}
            find ${DIR}/ -name "*.html" -exec sed -i "s/Line Coverage/${COVERAGE^} Coverage/g" {} +

            # Individual per-test
            for FILE in ${FILES}; do
                TEST=${FILE/coverage_/}
                TEST=${TEST/_${COVERAGE}.info/}

                mkdir -p ${DIR}_${TEST}
                # genhtml -o ${DIR}_${TEST} -t ${TEST} ${GENHTML_OPTS} ${FILE}
                genhtml -o ${DIR}_${TEST} -t ${TEST} --header-title "RTL ${COVERAGE} coverage report" ${GENHTML_OPTS} ${FILE}
                find ${DIR}_${TEST}/ -name "*.html" -exec sed -i "s/Line Coverage/${COVERAGE^} Coverage/g" {} +
            done
        fi
    done
}

#--------------#
#    Script
#--------------#
SELF_DIR="$(dirname $(readlink -f ${BASH_SOURCE[0]}))"
. ${SELF_DIR}/common.inc.sh

# Get revision
GIT_SHA=`git describe --always`
if [ $? -ne 0 ]; then
    GIT_SHA="unknown"
fi
set -e
OUTPUT_DIR=report
mkdir -p ${OUTPUT_DIR}
GENHTML_OPTS="--no-function-coverage --no-source"

echo -e "${COLOR_WHITE}========== gen_coverage_reports ==============${COLOR_CLEAR}"

generate_coverage_reports ${OUTPUT_DIR} "${GENHTML_OPTS}"

echo -e "${COLOR_WHITE}gen_coverage_reports ${COLOR_GREEN}SUCCEEDED${COLOR_CLEAR}"
echo -e "${COLOR_WHITE}========== gen_coverage_reports ==============${COLOR_CLEAR}"
