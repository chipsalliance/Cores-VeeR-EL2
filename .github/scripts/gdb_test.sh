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
GDB_LOG=`realpath gdb.log`

if [ -z $GCC_PREFIX ]; then
    GCC_PREFIX=riscv64-unknown-elf
fi

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

# Utils
source `dirname ${BASH_SOURCE[0]}`/utils.sh

terminate_all () {
    terminate ${OPENOCD_PID}
    echo "waiting for the simulation to end: $SIM_PID"
    wait ${SIM_PID}
    # terminate ${SIM_PID}
}

print_logs () {
    echo -e "${COLOR_WHITE}======== OpenOCD log ========${COLOR_OFF}"
    cat ${OPENOCD_LOG} || true
    echo -e "${COLOR_WHITE}======== Simulation log ========${COLOR_OFF}"
    cat ${SIM_LOG} || true
    echo -e "${COLOR_WHITE}======== GDB log ========${COLOR_OFF}"
    cat ${GDB_LOG} || true
}

echo -e "${COLOR_WHITE}======== Launching interactive simulation ========${COLOR_OFF}"

# Start the simulation
echo -e "Starting simulation..."
if [ -f obj_dir/Vtb_top ]; then
    SIM_START_STRING="VerilatorTB: Start of sim"
    obj_dir/Vtb_top >"${SIM_LOG}" 2>&1 &
elif [ -f ./simv ]; then
    SIM_START_STRING="  remote_bitbang_port 5000"
    ./simv +vcs+lic+wait -cm line+cond+fsm+tgl+branch >"${SIM_LOG}" 2>&1 &
else
    echo "No simulation binary found, exiting"
    exit 1
fi
SIM_PID=$!

# Wait
wait_for_phrase "${SIM_LOG}" "${SIM_START_STRING}"
sleep 1s
retcode=$?
if [ $retcode -ne 0 ]; then
    echo -e "${COLOR_RED}Failed to start the simulation: $retcode ${COLOR_OFF}"
    print_logs
    terminate_all; exit -1
fi
echo -e "Simulation running and ready (pid=${SIM_PID})"

# Launch OpenOCD
echo -e "Launching OpenOCD..."
WORKDIR=$PWD
cd ${RV_ROOT}/.github/scripts/openocd
openocd -d2 --file board/caliptra-verilator.cfg > ${OPENOCD_LOG} 2>&1 &
OPENOCD_PID=$!
cd $WORKDIR

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
echo -e "${COLOR_WHITE}======== Running GDB script test.gdb ========${COLOR_OFF}"

${GCC_PREFIX}-gdb -n --batch -x ${RV_ROOT}/.github/scripts/test.gdb > "${GDB_LOG}" &
GDB_PID=$!

# The simulation must end naturally in order to produce coverage data.
wait ${SIM_PID}

# OpenOCD waits endlessly for the target (Vtb_top) to reconnect.
# Kill OpenoCD and GDB in case they're stuck
kill -s SIGKILL ${OPENOCD_PID} || true
kill -s SIGKILL ${GDB_PID} || true

# Display logs
print_logs

# Parse the log, extract register values. Skip those which change as the
# program executes since we don't know at which point we tap in.
grep -E '^ra |^sp |^gp |^tp |^t[01256] |^s[0-9]+ |^a[0-9]+ |^\$[0-9]+ |^\$ |^Hardware |^Breakpoint' "${GDB_LOG}" > gdb_test_dump.txt

gdb_output_golden=${RV_ROOT}/.github/scripts/gdb_test_golden.txt
grep -q "TEST_PASSED" "${SIM_LOG}"
tb_passed=$?
# Compare the dumps
diff -E -y ${gdb_output_golden} gdb_test_dump.txt
gdb_output_match=$?

if [ "$tb_passed" -ne 0 ]; then
    echo "Testbench failed. The test did not write 0xff to the mailbox to indicate success."
    exit 1
fi
echo "Testbench passed."

if [ "$gdb_output_match" -ne 0 ]; then 
    echo "The output from GDB doesn't match the golden reference. See ${gdb_output_golden}"
    exit 1
fi
echo "The output from GDB matches the golden reference."
echo "TEST PASSED"
