#!/bin/bash
# SPDX-License-Identifier: Apache-2.0
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
# This script runs Verilator RTL simulation and OpenOCD in background, invokes
# the supplied test command and shuts everything down.

SIM_LOG=`realpath sim.log`
OPENOCD_LOG=`realpath openocd.log`
GCC_PREFIX=riscv64-unknown-elf

# Ensure that RISC-V toolchain is installed
if ! which ${GCC_PREFIX}-gcc >/dev/null; then
    GCC_PREFIX=riscv32-unknown-elf
fi
if ! which ${GCC_PREFIX}-gcc >/dev/null; then
    echo "RISC-V toolchain not found, please refer to https://github.com/chipsalliance/caliptra-rtl?tab=readme-ov-file#riscv-toolchain-installation for more details."
    exit 1
fi
export GCC_PREFIX

set +e

if [ "$#" -lt 1 ]; then
    echo "Usage: gdb_test.sh <command> [args ...]"
    exit 1
fi

# Utils
source `dirname ${BASH_SOURCE[0]}`/utils.sh

terminate_all () {
    terminate ${OPENOCD_PID}
    terminate ${SIM_PID}
}

print_logs () {
    echo -e "${COLOR_WHITE}======== Simulation log ========${COLOR_OFF}"
    cat ${SIM_LOG} || true
    echo -e "${COLOR_WHITE}======== OpenOCD log ========${COLOR_OFF}"
    cat ${OPENOCD_LOG} || true
}

echo -e "${COLOR_WHITE}======== Launching interactive simulation ========${COLOR_OFF}"

# Start the simulation
echo -e "Starting simulation..."
./obj_dir/Vtb_top >"${SIM_LOG}" 2>&1 &
SIM_PID=$!

# Wait
wait_for_phrase "${SIM_LOG}" "Start of sim"
retcode=$?
if [ $retcode -ne 0 ]; then
    echo -e "${COLOR_RED}Failed to start the simulation: $retcode ${COLOR_OFF}"
    print_logs
    terminate_all; exit -1
fi
echo -e "Simulation running and ready (pid=${SIM_PID})"

# Launch OpenOCD
echo -e "Launching OpenOCD..."
cd ${RV_ROOT}/.github/scripts/openocd && openocd -d2 -f board/caliptra-verilator.cfg >"${OPENOCD_LOG}" 2>&1 &
OPENOCD_PID=$!

# Wait
wait_for_phrase "${OPENOCD_LOG}" "Listening on port 3333 for gdb connections"
if [ $? -ne 0 ]; then
    echo -e "${COLOR_RED}Failed to start OpenOCD!${COLOR_OFF}"
    print_logs
    terminate_all; exit -1
fi
echo -e "OpenOCD running and ready (pid=${OPENOCD_PID})"

# Wait a bit
sleep 1s

# Run the test
echo -e "${COLOR_WHITE}======== Running test '$@' ========${COLOR_OFF}"

bash -c "$(printf ' %q' "$@")"
EXITCODE=$?

if [ ${EXITCODE} -eq 0 ]; then
    echo -e "${COLOR_GREEN}[PASSED]${COLOR_OFF}"
else
    echo -e "${COLOR_RED}[FAILED]${COLOR_OFF}"
fi

sleep 1s

# Terminate
echo -e "${COLOR_WHITE}Terminating...${COLOR_OFF}"
terminate_all

# Display logs
print_logs

# Honor the exitcode
exit ${EXITCODE}
