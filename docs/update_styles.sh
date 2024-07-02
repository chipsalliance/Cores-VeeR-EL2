#!/bin/bash

SELF_DIR="$(dirname $(readlink -f ${BASH_SOURCE[0]}))"
check_args_count(){
    # Check argument count function is meant to be used to check if
    # the number of received arguments is equal to the expected.
    # If they are unequal, the function returns with error
    # Args:
    # argc_got - Number of received arguments, e.g.: $#
    # argc_expected - Number of expected arguments, e.g.: 2
    argc_got=$1
    argc_expected=$2
    if [ ${argc_got} -ne ${argc_expected} ]; then
        echo -e "${COLOR_WHITE}Expected ${argc_expected} arguments, but received ${argc_got} ${COLOR_RED}FAIL${COLOR_CLEAR}"
        echo -e "${COLOR_WHITE}Caller:${COLOR_CLEAR}" `caller`
        exit 1
    fi
}

update_styles(){
    # Update styles for Sphinx theme
    # Args:
    # BUILDDIR - path to where the webpage is made
    BUILD_DIR=$1
    echo -e "${COLOR_WHITE}========== Update styles =========${COLOR_CLEAR}"
    echo -e "${COLOR_WHITE} BUILD_DIR = ${BUILD_DIR}${COLOR_CLEAR}"

    # Replace styles for sphinx build
    cp dashboard-styles/main.css ${BUILD_DIR}/html/_static/

    # Add CHIPs logo
    cp dashboard-styles/assets/chips-alliance-logo-mono.svg ${BUILD_DIR}/html/_static/white.svg

    # Replace undesired CSS and progress bar sprites with desired style for LCOV reports
    copy_files(){
        check_args_count $# 2
        SOURCE=$1
        SEARCH=$2
        FILES=`find ${BUILD_DIR}/ -name ${SEARCH}`

        for FILE in ${FILES}; do
            echo "Copy ${SOURCE} to ${FILE}"
            cp $SOURCE $FILE
        done
    }

    CHIPS_GCOV_CSS=dashboard-styles/gcov.css
    AMBER=dashboard-styles/assets/amber.png
    RUBY=dashboard-styles/assets/ruby.png
    SNOW=dashboard-styles/assets/snow.png
    EMERALD=dashboard-styles/assets/emerald.png

    for ASSET in $CHIPS_GCOV_CSS $AMBER $RUBY $SNOW $EMERALD; do
        copy_files $ASSET $(basename "$ASSET")
    done
    echo -e "${COLOR_WHITE}Update styles ${COLOR_GREEN}SUCCEEDED${COLOR_CLEAR}"
}

check_args_count $# 1
update_styles "$@"
