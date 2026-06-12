# SPDX-License-Identifier: Apache-2.0
# Copyright 2020 Western Digital Corporation or its affiliates.
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

# Allow snapshot override
target = default
snapshot = $(target)

# Allow tool override

SIMULATOR ?= verilator## Supported: verilator, vcs, xrun, qverilog, riviera
USER_MODE ?= 0
TEST      ?= hello_world
COVERAGE  ?= 0 ## Supported: all, branch, toggle, functional
DEBUG     ?= 0
BUS       ?= axi
RESULT_DIR ?= run_reg_test_${SIMULATOR}/$(shell date +'%Y%m%d-%H%M%S')

all: $(SIMULATOR)

# Define BUILD_TEST_DIR if TEST is set
ifdef TEST
BUILD_TEST_DIR := build/$(TEST)/$(shell date +'%Y%m%d-%H%M%S')
endif

clean:
	rm -rf *.log *.s *.hex *.dis *.tbl irun* vcs* simv* *.map snapshots \
	verilator* *.exe obj* *.o *.sym ucli.key vc_hdrs.h csrc *.csv work \
	dataset.asdb library.cfg vsimsa.cfg riviera-build wave.asdb

help:
	@echo Make sure the environment variable RV_ROOT is set.
	@echo Possible targets: verilator vcs irun vlog riviera help clean all verilator-build irun-build vcs-build riviera-build program.hex

.PHONY: help clean all verilator vcs xrun qverilog riviera irun vlog

# Automatic build directory creation based on TEST
ifdef TEST
ifneq ($(notdir $(CURDIR)),$(BUILD_TEST_DIR))
verilator vcs xrun qverilog riviera irun vlog: 
	echo $(BUILD_TEST_DIR)
	mkdir -p $(BUILD_TEST_DIR)
	cd $(BUILD_TEST_DIR) && exec $(MAKE) -f "${RV_ROOT}/tools/Makefile" snapshot=$(snapshot) TEST=$(TEST) USER_MODE=$(USER_MODE) debug=$(DEBUG) COVERAGE=$(COVERAGE) $@

endif
endif


run_reg_test: 
	.github/scripts/run_regression_test.sh ${RESULT_DIR} ${BUS} $(TEST) $(COVERAGE) $(USER_MODE) 0 ${SIMULATOR}

run_block:
	make -C verification/block/$(TEST) SIM=${SIMULATOR} WAVES=$(debug)	

#Example make command to run single test without run_regress_test.sh#
#make snapshot="caliptra-core" TEST=ecc debug=1 SIMULATOR=vcs
#
#Example make command to run single test with run_regress_test.sh#
#make run_reg_test TEST=dcls COVERAGE=all SIMULATOR=vcs
