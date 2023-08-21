#!/bin/bash

SELF_DIR="$(dirname $(readlink -f ${BASH_SOURCE[0]}))"
. ${SELF_DIR}/../common.inc.sh

style_pytest_report(){
    check_args_count $# 3
    SRC_DIR=$1
    DST_DIR=$2
    HTML_FILE=$3
    echo -e "${COLOR_WHITE}========== style_pytest_report =========${COLOR_CLEAR}"
    echo -e "${COLOR_WHITE} SRC_DIR   = ${SRC_DIR}${COLOR_CLEAR}"
    echo -e "${COLOR_WHITE} DST_DIR   = ${DST_DIR}${COLOR_CLEAR}"
    echo -e "${COLOR_WHITE} HTML_FILE = ${HTML_FILE}${COLOR_CLEAR}"

    # Copy assets

    cp ${SRC_DIR}/assets/* ${DST_DIR}/assets/

    # Add bar above h1.title

    SEARCH="<h1>"
    REPLACE=`cat ${SRC_DIR}/bar.html | tr '\n' ' '`
    REPLACE="$REPLACE $SEARCH"
    filename="${DST_DIR}/${HTML_FILE}"

    sed -i "s@$SEARCH@$REPLACE@" $filename

    # Copy JS script to build dir

    cp -r ${SRC_DIR}/script ${DST_DIR}

    echo -e "${COLOR_WHITE}Style pytest report ${COLOR_GREEN}SUCCEEDED${COLOR_CLEAR}"
    echo -e "${COLOR_WHITE}========== style_pytest_report =========${COLOR_CLEAR}"
}

check_args_count $# 3
style_pytest_report "$@"
