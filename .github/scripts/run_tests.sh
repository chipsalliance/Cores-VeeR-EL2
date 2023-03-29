#!/bin/bash
COLOR_CLEAR="\033[0m"
COLOR_WHITE="\033[1;37m"
COLOR_RED="\033[0;31m"
COLOR_GREEN="\033[1;32m"

RESULTS_DIR="results"

mkdir -p ${RESULTS_DIR}

# Configure VeeR
echo -e "${COLOR_WHITE}==================== Configuring VeeR-EL2 core  ====================${COLOR_CLEAR}"
$RV_ROOT/configs/veer.config
if [ $? -ne 0 ]; then
    echo "Failed to configure VeeR-EL2 core"
    exit -1
fi

# Run regression tests, store results
EXITCODE=0
RESULTS=()
TESTS=($TESTS)
for NAME in ${TESTS[@]}; do
    echo -e "${COLOR_WHITE}==================== running test '${NAME}' ====================${COLOR_CLEAR}"

    LOG="${RESULTS_DIR}/test_${NAME}.log"

    # Run the test
    make -f $RV_ROOT/tools/Makefile verilator TEST=${NAME} 2>&1 | tee ${LOG}
    if [ $? -ne 0 ]; then
        RES=0
        EXITCODE=-1
        echo -e "${COLOR_WHITE}Test '${NAME}' ${COLOR_RED}FAILED${COLOR_CLEAR}"
    else
        RES=1
        echo -e "${COLOR_WHITE}Test '${NAME}' ${COLOR_GREEN}SUCCEEDED${COLOR_CLEAR}"
    fi

    # Save the result
    RESULTS+=(${RES})
done

# Generate report
{
    echo "## Test results"
    echo ""
    echo "| Test name | Status |"
    echo "| --- | --- |"
    for i in ${!RESULTS[@]}; do

        if [ ${RESULTS[i]} -ne 0 ]; then
            STS=":heavy_check_mark:"
        else
            STS=":x:"
        fi

        echo "| ${TESTS[i]} | ${STS} |"
    done
} >> $GITHUB_STEP_SUMMARY

exit ${EXITCODE}
