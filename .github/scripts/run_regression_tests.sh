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

# Run regression tests with coverage collection enabled
EXITCODE=0
TESTS=($TESTS)
for NAME in ${TESTS[@]}; do
    echo -e "${COLOR_WHITE}==================== running test '${NAME}' ====================${COLOR_CLEAR}"

    for COVERAGE in branch toggle functional; do

        echo -e "${COLOR_WHITE}========== ${COVERAGE} coverage ==========${COLOR_CLEAR}"
        LOG="${RESULTS_DIR}/test_${NAME}_${COVERAGE}.log"
        DIR="run_${NAME}_${COVERAGE}"

        # Run the test
        mkdir -p ${DIR}
        make -j`nproc` -C ${DIR} -f $RV_ROOT/tools/Makefile verilator TEST=${NAME} COVERAGE=${COVERAGE} 2>&1 | tee ${LOG}
        RES=${PIPESTATUS[0]}
        if [ ${RES} -ne 0 ] || ! [ -f "${DIR}/coverage.dat" ]; then
            EXITCODE=-1
            echo -e "${COLOR_WHITE}Test '${NAME}' ${COLOR_RED}FAILED${COLOR_CLEAR}"
        else

            # Copy and convert coverage data
            cp ${DIR}/coverage.dat ${RESULTS_DIR}/coverage_${NAME}_${COVERAGE}.dat
            verilator_coverage --write-info ${RESULTS_DIR}/coverage_${NAME}_${COVERAGE}.info ${RESULTS_DIR}/coverage_${NAME}_${COVERAGE}.dat

            echo -e "${COLOR_WHITE}Test '${NAME}' ${COLOR_GREEN}SUCCEEDED${COLOR_CLEAR}"
        fi
    done
done

exit ${EXITCODE}
