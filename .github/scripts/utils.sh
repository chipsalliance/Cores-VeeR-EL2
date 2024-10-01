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

# Colors
COLOR_OFF='\033[0m'
COLOR_RED='\033[31m'
COLOR_GREEN='\033[32m'
COLOR_WHITE='\033[1;37m'

# Waits until the given phrase appears in a log file (actively written to)
# Usage: wait_for_phrase <log_file> <phrase>
wait_for_phrase () {

    # Check if the log exists
    sleep 1s
    if ! [ -f "$1" ]; then
        echo -e "${COLOR_RED}Log file '$1' not found!${COLOR_OFF}"
        return -1
    fi

    # Wait for the phrase
    DEADLINE=$((${EPOCHSECONDS} + 30))
    while [ ${EPOCHSECONDS} -lt ${DEADLINE} ]
    do
        # Check for the phrase
        grep "$2" "$1" >/dev/null
        if [ $? -eq 0 ]; then
            return 0
        fi

        # Sleep and retry
        sleep 1s
    done

    # Timeout
    return -1
}

# Terminates a process. First via SIGINT and if this doesn't work after 10s
# retries with SIGKILL
# Usage: terminate <pid>
terminate () {

    local PID=$1

    # Gently interrupt, wait some time and then kill
    /bin/kill -s SIGINT  ${PID} || true
    sleep 10s
    /bin/kill -s SIGKILL ${PID} || true
}
