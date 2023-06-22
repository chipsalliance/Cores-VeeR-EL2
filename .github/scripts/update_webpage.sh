#!/bin/bash

SELF_DIR="$(dirname $(readlink -f ${BASH_SOURCE[0]}))"
. ${SELF_DIR}/common.inc.sh

replace_dir(){
    # This function removes the destination dir, creates an empty destination directory,
    # copies contents of source dir to destination dir.
    # Args:
    # SRC_DIR - valid path to source directory
    # DST_DIR - valid path to destination directory
    check_args_count $# 2
    SRC_DIR=$1
    DST_DIR=$2
    echo -e "${COLOR_WHITE}=========== replace_dir args ===========${COLOR_CLEAR}"
    echo -e "${COLOR_WHITE}SRC_DIR = ${SRC_DIR}${COLOR_CLEAR}"
    echo -e "${COLOR_WHITE}DST_DIR = ${DST_DIR}${COLOR_CLEAR}"

    # Replace existing pages with new ones
    rm -rf ${DST_DIR}
    mkdir -p ${DST_DIR}
    # Copy the new one
    cp -arf ${SRC_DIR}/* ${DST_DIR}
}

generate_index(){
    # Generates the top-level index webpage
    # Args:
    # ROOT - webpage root path
    check_args_count $# 1
    ROOT=$1
    echo -e "${COLOR_WHITE}=========== generate_index args ===========${COLOR_CLEAR}"
    echo -e "${COLOR_WHITE}ROOT = ${ROOT}"

    INDEX=${ROOT}/index.html
    rm -rf ${INDEX}

    # Header
    echo -n "<!DOCTYPE html>
    <html>
    <body>

    <h2>RISC-V VeeR EL2</h2>
    <h3>Dashboard</h3>
    <hr>
    <h3>Main branch</h3>
    <ul>
    <li><a href=\"./main/verification_dashboard/verification_dashboard.html\">Verification Dashboard</a></li>
    <li><a href=\"./main/coverage_dashboard/index.html\">Coverage Dashboard</a></li>
    </ul>
    <hr>
    <h3>Feature branches / pull requests</h3>
    " >>${INDEX}

    # List subpages
    pushd ${ROOT}
    if ! SUBDIRS=`find dev/ -maxdepth 1 -type d ! -name "." ! -name ".." -printf "%P\n" | sort`; then
        echo -e "Directory dev/ not found"
    fi
    popd

    # Body
    for SUBDIR in ${SUBDIRS}; do
        echo -e "${COLOR_WHITE}Found subpage ${SUBDIR}${COLOR_CLEAR}"
        echo -n "
        <h4>${SUBDIR}</h4>
        <ul>
        <li><a href=\"dev/${SUBDIR}/verification_dashboard/verification_dashboard.html\">Verification Dashboard</a></li>
        <li><a href=\"dev/${SUBDIR}/coverage_dashboard/index.html\">Coverage Dashboard</a></li>
        </ul>
        " >>${INDEX}
    done

    # Footer
    echo -n "
    <hr>
    <p> Copyright 2023 Antmicro</p>
    </body>
    </html>

    " >>${INDEX}

    echo -e "${COLOR_WHITE}Index generation ${COLOR_GREEN}SUCCEEDED${COLOR_CLEAR}"
}

update_webpage(){
    # This function updates the public part of the gh-pages, which contain
    # coverage and verification reports. Different destination directory is
    # selected based on git refs, github events and pr numbers
    # Args:
    # LOC_GITHUB_REF_NAME - use ${{ github.ref }}
    # LOC_GITHUB_EVENT_NAME - use ${{ github.event_name }}
    # PR_NUMBER - number of the PR, e.g. 81
    check_args_count $# 3
    LOC_GITHUB_REF_NAME=$1
    LOC_GITHUB_EVENT_NAME=$2
    PR_NUMBER=$3
    echo -e "${COLOR_WHITE}========== update_webpage args =========${COLOR_CLEAR}"
    echo -e "${COLOR_WHITE}LOC_GITHUB_REF_NAME        = ${LOC_GITHUB_REF_NAME}"
    echo -e "${COLOR_WHITE}LOC_GITHUB_EVENT_NAME = ${LOC_GITHUB_EVENT_NAME}"
    echo -e "${COLOR_WHITE}PR_NUMBER             = ${PR_NUMBER}"

    # Function body
    # On main, deploy the main page
    if [ ${LOC_GITHUB_REF_NAME} = 'main' ]; then
        DIR=main
    # On a PR, deploy to a PR subdirectory
    elif [ ${LOC_GITHUB_EVENT_NAME} = 'pull_request' ]; then
        DIR=dev/${PR_NUMBER}
    # On a push, deploy to a branch subdirectory
    elif [ ${LOC_GITHUB_EVENT_NAME}  = 'push' ]; then
        # If ref_name contains slash "/", replace it with underscore "_"
        DIR=dev/${LOC_GITHUB_REF_NAME//\//_}
    # Unknown
    else
        echo -e "${COLOR_WHITE}Unknown deployment type ${COLOR_RED}FAIL${COLOR_CLEAR}"
        exit -1
    fi
    PUBLIC_DIR=./public

    replace_dir ./coverage_dashboard ${PUBLIC_DIR}/${DIR}/coverage_dashboard
    replace_dir ./verification_dashboard ${PUBLIC_DIR}/${DIR}/verification_dashboard

    generate_index ${PUBLIC_DIR}

    echo -e "${COLOR_WHITE}================= tree =================${COLOR_CLEAR}"
    tree ./public/

    echo -e "${COLOR_WHITE}Webpage update ${COLOR_GREEN}SUCCEEDED${COLOR_CLEAR}"
    echo -e "${COLOR_WHITE}============ update_webpage ============${COLOR_CLEAR}"
}

# Example usage
# mkdir -p coverage_dashboard verification_dashboard && touch coverage_dashboard/index.html verification_dashboard/index.html
# LOC_GITHUB_REF_NAME=mczyz/test
# LOC_GITHUB_EVENT_NAME=push
# PR_NUMBER=81
# update_webpage ${LOC_GITHUB_REF_NAME} ${LOC_GITHUB_EVENT_NAME} ${PR_NUMBER}

check_args_count $# 3
update_webpage "$@"
