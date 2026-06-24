#
# SPDX-License-Identifier: Apache-2.0
#
#Example make command to run single test without run_regress_test.sh#
#====================================================================
#make snapshot="caliptra-core" TEST=ecc debug=1 SIMULATOR=vcs
#
#Example make command to run block test#
#====================================================================
#make run_block_test TEST=dcls DEBUG=1 SIMULATOR=vcs
#
#Example make command to run single test(testbench/tests/$TEST)
#with $RV_ROOT/.github/scripts/run_regression_test.sh#
#====================================================================
#make run_reg_test TEST=dcls COVERAGE=all SIMULATOR=vcs
#
#Example make command to run local regression with specific workflow#
#====================================================================
#make run_regression SIMULATOR=vcs WORKFLOW=test-uarch.yml

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

BUILD_BLOCK_TEST_DIR := run_block/$(TEST)_$(shell date +'%Y%m%d-%H%M%S')
COVERAGE_TYPE := ${COVERAGE}

run_block_test:
	echo "starting block test $(TEST)"
	mkdir -p $(BUILD_BLOCK_TEST_DIR)
	cd $(BUILD_BLOCK_TEST_DIR) && ln -sf $(RV_ROOT)/verification/block/$(TEST) .
	$(MAKE) -C $(BUILD_BLOCK_TEST_DIR)/$(TEST) SIM=${SIMULATOR} WAVES=$(DEBUG) COVERAGE_TYPE=$(COVERAGE_TYPE)

BUILD_RESGRESS := run_regress_$(shell date +'%Y%m%d_%H%M%S')
WORKFLOW := 

run_regression:
	touch ${BUILD_RESGRESS}.log
	echo "starting regression with $(SIMULATOR)" >> ${BUILD_RESGRESS}.log
	python3 ${RV_ROOT}/.github/scripts/gen_ci_testlist.py --simulator ${SIMULATOR} $(if $(WORKFLOW),--workflow $(WORKFLOW)) >> ${BUILD_RESGRESS}.log
	./run_local_regression.sh  |tee run.log
	cat run.log >> ${BUILD_RESGRESS}.log
	rm run.log
