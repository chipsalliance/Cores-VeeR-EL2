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
#    HTML
#--------------#
generate_index_header(){
    # This function creates a basic index html dashboard, which enables navigation
    # Args
    # OUTPUT_DIR - directory, where index.html will be placed
    # GIT_SHA - git revision
    check_args_count $# 2
    OUTPUT_DIR=$1
    GIT_SHA=$2
    echo -e "${COLOR_WHITE}========== generate_index_header =============${COLOR_CLEAR}"
    echo -e "${COLOR_WHITE}OUTPUT_DIR = ${OUTPUT_DIR}${COLOR_CLEAR}"
    echo -e "${COLOR_WHITE}GIT_SHA    = ${GIT_SHA}${COLOR_CLEAR}"

    # Function Body
    set +x
    rm -rf ${OUTPUT_DIR}/index.html

    # Header
    echo -n "<!DOCTYPE html>
    <html>
    <body>
    <h2>RISC-V VeeR EL2</h2>
    <h3>Coverage Dashboard</h3>
    <p>Revision: ${GIT_SHA}</p>
    " >>${OUTPUT_DIR}/index.html

    # Summary reports
    echo -e "\n<hr>" >>${OUTPUT_DIR}/index.html
    echo -e "\n<h3>Summary reports (all tests)</h3>" >>${OUTPUT_DIR}/index.html
}

generate_index_body(){
    # This function creates a body for the index html
    # Args
    # OUTPUT_DIR - directory, where index.html will be placed
    check_args_count $# 1
    OUTPUT_DIR=$1
    echo -e "${COLOR_WHITE}========== generate_index_body ===============${COLOR_CLEAR}"
    echo -e "${COLOR_WHITE}OUTPUT_DIR = ${OUTPUT_DIR}${COLOR_CLEAR}"

    echo "<h3>Coverage:</h3>" >>${OUTPUT_DIR}/index.html
    echo "<ul>" >>${OUTPUT_DIR}/index.html
    for COVERAGE in branch toggle all functional; do
        PAGES=`find ${OUTPUT_DIR}/ -type d -name "${COVERAGE}_*" -printf "%P\n" | sort`
        if [ -z "$PAGES" ]; then
            echo "<li><em>${COVERAGE} report</em> (not enabled) </li>" >>${OUTPUT_DIR}/index.html
        else
            echo "<li><a href=\"${COVERAGE}/index.html\"><em>${COVERAGE} report</em></a></li>" >>${OUTPUT_DIR}/index.html
        fi
    done
    echo "</ul>" >>${OUTPUT_DIR}/index.html

    # Per-test reports
    echo -e "\n<hr>" >>${OUTPUT_DIR}/index.html
    echo -e "\n<h3>Individual test reports</h3>" >>${OUTPUT_DIR}/index.html

    echo "<h3>Coverage:</h3>" >>${OUTPUT_DIR}/index.html

    for COVERAGE in branch toggle all functional; do
        echo "<h4>${COVERAGE}</h4>" >>${OUTPUT_DIR}/index.html
        echo "<ul>" >>${OUTPUT_DIR}/index.html
        PAGES=`find ${OUTPUT_DIR}/ -type d -name "${COVERAGE}_*" -printf "%P\n" | sort`
        if [ -z "$PAGES" ]; then
            echo -e "${COLOR_WHITE}There are no reports for coverage ${COVERAGE} ${COLOR_YELLOW}WARNING${COLOR_CLEAR}"
            echo "<li>No data to display</li>" >>${OUTPUT_DIR}/index.html
        fi
        for PAGE in ${PAGES}; do
            TEST=${PAGE/${COVERAGE}_/}
            echo "<li><a href=\"${COVERAGE}_${TEST}/index.html\">${TEST}</a></li>" >>${OUTPUT_DIR}/index.html
        done
        echo "</ul>" >>${OUTPUT_DIR}/index.html
    done

}

generate_index_footer(){
    # This function creates a footer for the index html
    # Args
    # OUTPUT_DIR - directory, where index.html will be placed
    check_args_count $# 1
    OUTPUT_DIR=$1
    echo -e "${COLOR_WHITE}========== generate_index_footer =============${COLOR_CLEAR}"
    echo -e "${COLOR_WHITE}OUTPUT_DIR = ${OUTPUT_DIR}${COLOR_CLEAR}"

    echo -n "
    <hr>
    <p> Copyright 2023 Antmicro</p>
    </body>
    </html>
    " >>${OUTPUT_DIR}/index.html
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
generate_index_header ${OUTPUT_DIR} ${GIT_SHA}
generate_index_body ${OUTPUT_DIR}
generate_index_footer ${OUTPUT_DIR}

echo -e "${COLOR_WHITE}gen_coverage_reports ${COLOR_GREEN}SUCCEEDED${COLOR_CLEAR}"
echo -e "${COLOR_WHITE}========== gen_coverage_reports ==============${COLOR_CLEAR}"
