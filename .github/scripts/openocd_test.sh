#!/bin/bash
# SPDX-License-Identifier: Apache-2.0
# Copyright 2024 Antmicro <www.antmicro.com>
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
# This script runs Verilator RTL simulation in background and invokes OpenOCD
# to perform JTAG access test

SIM_LOG=`realpath sim.log`
OPENOCD_LOG=`realpath openocd.log`

set +e

if [ "$#" -lt 1 ]; then
    echo "Usage: openocd_test.sh [openocd args ...]"
    exit 1
fi
OPENOCD_ARGS=$@

# Utils
source `dirname ${BASH_SOURCE[0]}`/utils.sh

print_logs () {
    echo -e "${COLOR_WHITE}======== Simulation log ========${COLOR_OFF}"
    cat ${SIM_LOG} || true
    echo -e "${COLOR_WHITE}======== OpenOCD log ========${COLOR_OFF}"
    cat ${OPENOCD_LOG} || true
}

echo -e "${COLOR_WHITE}======== Launching interactive simulation ========${COLOR_OFF}"

# Start the simulation
echo -e "Starting simulation..."
obj_dir/Vtb_top >"${SIM_LOG}" 2>&1 &
SIM_PID=$!

# Wait
wait_for_phrase "${SIM_LOG}" "VerilatorTB: Start of sim"
if [ $? -ne 0 ]; then
    echo -e "${COLOR_RED}Failed to start the simulation!${COLOR_OFF}"
    print_logs
    terminate ${SIM_PID}; exit -1
fi
echo -e "Simulation running and ready (pid=${SIM_PID})"

# Wait a bit
sleep 2s

# Run the test
echo -e "${COLOR_WHITE}======== Running OpenOCD test '$@' ========${COLOR_OFF}"
cd ${RV_ROOT}/testbench/openocd_scripts && openocd -d2 ${OPENOCD_ARGS} >"${OPENOCD_LOG}" 2>&1
EXITCODE=$?

if [ ${EXITCODE} -eq 0 ]; then
    echo -e "${COLOR_GREEN}[PASSED]${COLOR_OFF}"
else
    echo -e "${COLOR_RED}[FAILED]${COLOR_OFF}"
fi

# Display logs
print_logs

wait $SIM_PID

# Honor the exitcode
exit ${EXITCODE}

