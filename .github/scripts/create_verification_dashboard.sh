#!/bin/bash

SELF_DIR="$(dirname $(readlink -f ${BASH_SOURCE[0]}))"
. ${SELF_DIR}/common.inc.sh

create_verification_dashboard(){
    # This function creates a verification dashboard with links to tests:
    # <p><a href="webpage_test_debug/index.html">webpage_test_debug</a></p>
    # Args:
    # HTML_OUTPUT_FILE - name of the output file, scripts assumes
    # that it will be placed in verifcation dir
    check_args_count $# 2
    HTML_OUTPUT_FILE=$1
    VERIFICATION_DASHBOARD_DIR=$2
    echo -e "${COLOR_WHITE}========== create_verification_dashboard args =========${COLOR_CLEAR}"
    echo -e "${COLOR_WHITE}HTML_OUTPUT_FILE = ${HTML_OUTPUT_FILE}"
    echo -e "${COLOR_WHITE}VERIFICATION_DASHBOARD_DIR = ${VERIFICATION_DASHBOARD_DIR}"

    html_text="
<!DOCTYPE html>
<html>
    <head>
    <title> Verification Dashboard </title>
    </head>
    <body>
        <h2>RISC-V VeeR EL2</h2>
        <h3>Verification dashboard</h3>
        <hr>
        <h3>Test reports</h3>
            <verification_links>
        <hr>
        <p> Copyright 2023 Antmicro</p>
    </body>
</html>
"
    verification_list=`find ./ -maxdepth 1 -type d -name "webpage_*" -printf "%f\n"`
    echo ${verification_list}
    if [ -z "${verification_list}" ]; then
        echo -e "${COLOR_WHITE}Found no verification webpages ${COLOR_YELLOW}WARNING${COLOR_CLEAR}"
        mkdir -p ./${VERIFICATION_DASHBOARD_DIR}
        echo ${html_text} > ${VERIFICATION_DASHBOARD_DIR}/${HTML_OUTPUT_FILE}.html
        echo -e "${COLOR_WHITE}Verification dashboard generation ended with problems ${COLOR_RED}SOFT_ERROR${COLOR_CLEAR}"
        echo -e "${COLOR_WHITE}============ create_verification_dashboard ============${COLOR_CLEAR}"
    else
        mkdir -p ./${VERIFICATION_DASHBOARD_DIR}
        html_links=()
        for i in ${verification_list}
        do
            html_page=${i#*webpage_}
            html_link="<p><a href="\"${i}"/${html_page}.html\">"${i}"</a></p>"
            html_links+=("${html_link}")
            mv ${i} ./${VERIFICATION_DASHBOARD_DIR}
            echo -e "${COLOR_WHITE}Creating link ${COLOR_GREEN}PASS${COLOR_CLEAR}"
        done
        echo -e "${COLOR_WHITE}Array of links:${COLOR_CLEAR}"

        for link in "${html_links[@]}"
        do
            echo -e "${COLOR_WHITE}${link}${COLOR_CLEAR}"
        done
        html_text=${html_text/"<verification_links>"/${html_links[*]}}
        echo ${html_text} > ${VERIFICATION_DASHBOARD_DIR}/${HTML_OUTPUT_FILE}
        # tidy verification/verification_dashboard.html
        echo -e "${COLOR_WHITE}Verification dashboard generation ${COLOR_GREEN}SUCCEEDED${COLOR_CLEAR}"
        echo -e "${COLOR_WHITE}============ create_verification_dashboard ============${COLOR_CLEAR}"
    fi
}

# Example usage
HTML_OUTPUT_FILE=verification_dashboard.html
VERIFICATION_DASHBOARD_DIR=verification_dashboard
create_verification_dashboard ${HTML_OUTPUT_FILE} ${VERIFICATION_DASHBOARD_DIR}
