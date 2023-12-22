# SPDX-License-Identifier: Apache-2.0
# Copyright 2020 Western Digital Corporation or its affiliates.
# Copyright (c) 2023 Antmicro <www.antmicro.com>
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

NPROC = $$((`nproc`-1))

# -------------------------------------
# VeeR Configuration
# -------------------------------------
CONF_PARAMS = -set build_axi4

# Allow snapshot override
target = default
snapshot = $(target)

# Check for RV_ROOT
ifeq (,$(wildcard ${RV_ROOT}/configs/veer.config))
$(error env var RV_ROOT does not point to a valid dir! Exiting!)
endif

# Allow tool override
VEER_CONFIG = ${RV_ROOT}/configs/veer.config
BUILD_DIR = snapshots/${snapshot}

# If define files do not exist, then run veer.config.
${BUILD_DIR}/defines.h:
	BUILD_PATH=${BUILD_DIR} ${VEER_CONFIG} -target=$(target) $(CONF_PARAMS)
	echo '`undef RV_ASSERT_ON' >> ${BUILD_DIR}/common_defines.vh

# -------------------------------------
# cocotb setup
# -------------------------------------
COCOTB_DIR = ${RV_ROOT}/third_party/cocotb
COCOTB_SHARE_DIR = ${COCOTB_DIR}/cocotb/share

COCOTB_HDL_TIMEUNIT ?= 1ns
COCOTB_HDL_TIMEPRECISION ?= 1ps

# -------------------------------------
# Testbench setup
# -------------------------------------
UVM_TEST ?= test_irq.test_irq
SIM_DIR ?= sim

TOP_MODULE = veer_wrapper

VERILOG_DEFINE_FILES = $(BUILD_DIR)/common_defines.vh
VERILOG_DEFINE_FILES += ${RV_ROOT}/design/include/el2_def.sv
VERILOG_DEFINE_FILES += $(BUILD_DIR)/el2_pdef.vh

VERILOG_INCLUDE_DIRS = ${BUILD_DIR}

# -------------------------------------
# Compilation/simulation configuration
# -------------------------------------
VERILATOR = verilator
VERILATOR_SIM_DEBUG ?= 0
VERILATOR_TRACE ?= 0

EXTRA_ARGS += --timescale $(COCOTB_HDL_TIMEUNIT)/$(COCOTB_HDL_TIMEPRECISION) --timing
COMPILE_ARGS += -CFLAGS -std=c++20 --vpi --public-flat-rw --prefix Vtop -o Vtop
COMPILE_ARGS += -LDFLAGS "-Wl,-rpath,$(shell cocotb-config --lib-dir) -L$(shell cocotb-config --lib-dir) -lcocotbvpi_verilator"
COMPILE_ARGS += $(addprefix +incdir+, $(VERILOG_INCLUDE_DIRS))
WARNING_ARGS += -Wno-WIDTH -Wno-UNOPTFLAT

FLIST_FILE = ${RV_ROOT}/testbench/flist

ifeq ($(VERILATOR_SIM_DEBUG), 1)
  COMPILE_ARGS += --debug -CFLAGS "-DVL_DEBUG -DVERILATOR_SIM_DEBUG -g"
  PLUSARGS += +verilator+debug
  BUILD_ARGS += OPT_FAST=-Og OPT_SLOW=-Og OPT_GLOBAL=-Og
endif

ifeq ($(VERILATOR_TRACE),1)
  EXTRA_ARGS += --trace --trace-structs
endif

# Coverage reporting
COVERAGE ?= all
ifeq ("$(COVERAGE)", "all")
    VERILATOR_COVERAGE = --coverage
else ifeq ("$(COVERAGE)", "branch")
    VERILATOR_COVERAGE = --coverage-line
else ifeq ("$(COVERAGE)", "toggle")
    VERILATOR_COVERAGE = --coverage-toggle
else ifeq ("$(COVERAGE)", "functional")
    VERILATOR_COVERAGE = --coverage-user
else ifneq ("$(COVERAGE)", "")
    $(error Unknown COVERAGE value '$(COVERAGE)')
endif

# -------------------------------------
# Make PyUVM test with Verilator
# -------------------------------------
$(SIM_DIR):
	mkdir -p $@

$(SIM_DIR)/Vtop.mk: $(COCOTB_SHARE_DIR)/lib/verilator/verilator.cpp | $(SIM_DIR)
	$(VERILATOR) --cc --exe -Mdir $(SIM_DIR) \
	${COMPILE_ARGS} ${EXTRA_ARGS} \
	${VERILOG_DEFINE_FILES} -f ${FLIST_FILE} \
	${WARNING_ARGS} \
	--top-module $(TOP_MODULE) \
	$(VERILATOR_COVERAGE) \
	$(COCOTB_SHARE_DIR)/lib/verilator/verilator.cpp

$(SIM_DIR)/Vtop: $(SIM_DIR)/Vtop.mk
	$(MAKE) -j${NPROC} -C $(SIM_DIR) $(BUILD_ARGS) -f Vtop.mk

verilator-pyuvm: ${BUILD_DIR}/defines.h $(SIM_DIR)/Vtop.mk $(SIM_DIR)/Vtop
	MODULE=$(UVM_TEST) $(SIM_DIR)/Vtop

# -------------------------------------
# Standard recipes
# -------------------------------------

all: clean verilator-pyuvm

clean:
	rm -rf obj_dir assets sim snapshots coverage.dat results.xml console.log exec.log *.cpp.s *.dis *.exe *.o *.map *.hex trace_port.csv verilator-cocotb-build

help:
	@echo Make sure the environment variable RV_ROOT is set.
	@echo Expected usage: make verilator-pyuvm

.PHONY: help clean

