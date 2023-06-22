#!/bin/bash

set -e -u -o pipefail

COLOR_CLEAR="\033[0m"
COLOR_RED="\033[0;31m"
COLOR_GREEN="\033[1;32m"
COLOR_YELLOW="\033[1;33m"
COLOR_WHITE="\033[1;37m"

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
