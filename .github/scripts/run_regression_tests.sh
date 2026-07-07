#!/bin/bash
COLOR_CLEAR="\033[0m"
COLOR_WHITE="\033[1;37m"
COLOR_RED="\033[0;31m"
COLOR_GREEN="\033[1;32m"

RESULTS_DIR="regression_results"

SIMULATOR=${1:-verilator}

mkdir -p ${RESULTS_DIR}

# Configure VeeR
echo -e "${COLOR_WHITE}==================== Configuring VeeR-EL2 core  ====================${COLOR_CLEAR}"
$RV_ROOT/configs/veer.config
if [ $? -ne 0 ]; then
    echo "Failed to configure VeeR-EL2 core"
    exit -1
fi

echo -e "${COLOR_WHITE}==================== Using simulator: ${SIMULATOR} ====================${COLOR_CLEAR}"

# Run regression tests with coverage collection enabled
EXITCODE=0
SUMMARY_ROWS=()
TESTS=($TESTS)
for NAME in ${TESTS[@]}; do
    echo -e "${COLOR_WHITE}==================== running test '${NAME}' ====================${COLOR_CLEAR}"

    COVERAGE="all"

    echo -e "${COLOR_WHITE}========== ${COVERAGE} coverage ==========${COLOR_CLEAR}"
    LOG="${RESULTS_DIR}/test_${NAME}_${COVERAGE}.log"
    DIR="${RESULTS_DIR}/run_${NAME}_${COVERAGE}"

    # Run the test
    mkdir -p ${DIR}
    make -j`nproc` -C ${DIR} -f $RV_ROOT/tools/Makefile ${SIMULATOR} TEST=${NAME} COVERAGE=${COVERAGE} 2>&1 | tee ${LOG}
    RES=${PIPESTATUS[0]}

    FAILED=0
    if [ ${RES} -ne 0 ]; then
        FAILED=1
    elif [ "${SIMULATOR}" == "verilator" ] && ! [ -f "${DIR}/coverage.dat" ]; then
        FAILED=1
    fi

    if [ ${FAILED} -ne 0 ]; then
        EXITCODE=-1
        echo -e "${COLOR_WHITE}Test '${NAME}' ${COLOR_RED}FAILED${COLOR_CLEAR}"
        SUMMARY_ROWS+=("$(printf "%-30s | %-10s | ${COLOR_RED}%-8s${COLOR_CLEAR} | %s" "${NAME}" "${COVERAGE}" "FAILED" "${DIR}")")
    else
        if [ "${SIMULATOR}" == "verilator" ]; then
            # Copy and convert coverage data
            cp ${DIR}/coverage.dat ${RESULTS_DIR}/coverage_${NAME}_${COVERAGE}.dat
            verilator_coverage --write-info ${RESULTS_DIR}/coverage_${NAME}_${COVERAGE}.info ${RESULTS_DIR}/coverage_${NAME}_${COVERAGE}.dat
        fi
        echo -e "${COLOR_WHITE}Test '${NAME}' ${COLOR_GREEN}SUCCEEDED${COLOR_CLEAR}"
        SUMMARY_ROWS+=("$(printf "%-30s | %-10s | ${COLOR_GREEN}%-8s${COLOR_CLEAR} | %s" "${NAME}" "${COVERAGE}" "PASSED" "${DIR}")")
    fi
done

# Generate URG report for VCS coverage if any .vdb directories were created
if [ "${SIMULATOR}" == "vcs" ]; then
    VDB_DIRS=$(find ${RESULTS_DIR} -type d -name "*.vdb")
    if [ -n "$VDB_DIRS" ]; then
        echo -e "${COLOR_WHITE}==================== Generating URG Report ====================${COLOR_CLEAR}"
        urg -dir $VDB_DIRS -report ${RESULTS_DIR}/urgReport -format both
        
        if [ -f "${RESULTS_DIR}/urgReport/dashboard.txt" ]; then
            echo -e "\n${COLOR_WHITE}===================================================================================================${COLOR_CLEAR}"
            echo -e "${COLOR_WHITE}                                      TOTAL COVERAGE SUMMARY                                       ${COLOR_CLEAR}"
            echo -e "${COLOR_WHITE}===================================================================================================${COLOR_CLEAR}"
            grep -A 2 "Total Coverage Summary" "${RESULTS_DIR}/urgReport/dashboard.txt"
        elif [ -f "${RESULTS_DIR}/urgReport/dashboard.html" ]; then
            echo -e "\n${COLOR_WHITE}===================================================================================================${COLOR_CLEAR}"
            echo -e "${COLOR_WHITE}                                      TOTAL COVERAGE SUMMARY                                       ${COLOR_CLEAR}"
            echo -e "${COLOR_WHITE}===================================================================================================${COLOR_CLEAR}"
            sed -n '/Total Coverage Summary/,/<\/table>/p' "${RESULTS_DIR}/urgReport/dashboard.html" | sed -e 's/<[^>]*>/\t/g' -e 's/&nbsp;/ /g' | tr -s '\t' | sed '/^\s*$/d' | head -n 3
        fi
    fi
fi

# Generate merged coverage report for Verilator if any .dat files were created
if [ "${SIMULATOR}" == "verilator" ]; then
    DAT_FILES=$(find ${RESULTS_DIR} -maxdepth 1 -name "coverage_*.dat")
    if [ -n "$DAT_FILES" ]; then
        echo -e "${COLOR_WHITE}==================== Merging Verilator Coverage ====================${COLOR_CLEAR}"
        verilator_coverage --write-info ${RESULTS_DIR}/merged_coverage.info $DAT_FILES
    fi
fi

echo -e "\n${COLOR_WHITE}===================================================================================================${COLOR_CLEAR}"
echo -e "${COLOR_WHITE}                                            TEST SUMMARY                                           ${COLOR_CLEAR}"
echo -e "${COLOR_WHITE}===================================================================================================${COLOR_CLEAR}"
printf "${COLOR_WHITE}%-30s | %-10s | %-8s | %s${COLOR_CLEAR}\n" "Test Name" "Coverage" "Status" "Results Path"
echo -e "${COLOR_WHITE}-------------------------------+------------+----------+-------------------------------------------${COLOR_CLEAR}"
for row in "${SUMMARY_ROWS[@]}"; do
    echo -e "$row"
done
echo -e "${COLOR_WHITE}===================================================================================================${COLOR_CLEAR}\n"

exit ${EXITCODE}
