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

TOPLEVEL_LANG    = verilog
SIM             ?= verilator
WAVES           ?= 1
NPROC = $$((`nproc`-1))

#Paths
CURDIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
CFGDIR := $(abspath $(CURDIR)/snapshots/default)
CONFIG := $(RV_ROOT)/configs
# -------------------------------------
# VeeR Configuration
# -------------------------------------
CONF_PARAMS ?= -set build_axi4

# Check for RV_ROOT
ifeq (,$(wildcard ${RV_ROOT}/configs/veer.config))
$(error env var RV_ROOT does not point to a valid dir! Exiting!)
endif

# -------------------------------------
# Testbench setup
# -------------------------------------
MODULE ?= test_irq.test_irq
TEST_FILES = $(CURDIR)/test_irq/test_irq.py
TOPLEVEL = veer_wrapper
SIM_BUILD ?= sim
CM_FILE ?= cm.cfg

VERILOG_SOURCES = \
    $(CFGDIR)/common_defines.vh \
    $(RV_ROOT)/design/include/el2_def.sv \
    $(CFGDIR)/el2_pdef.vh

SIM_FLIST_FILE = $(RV_ROOT)/testbench/flist

# -------------------------------------
# Compilation/simulation configuration
# -------------------------------------

# Coverage reporting
COVERAGE_TYPE?= all
ifeq ("$(COVERAGE_TYPE)", "all")
    VERILATOR_COVERAGE = --coverage
else ifeq ("$(COVERAGE_TYPE)", "branch")
    VERILATOR_COVERAGE = --coverage-line
else ifeq ("$(COVERAGE_TYPE)", "toggle")
    VERILATOR_COVERAGE = --coverage-toggle
else ifeq ("$(COVERAGE_TYPE)", "functional")
    VERILATOR_COVERAGE = --coverage-user
else
    VERILATOR_COVERAGE = ""
endif

ifeq ($(SIM), verilator)
    COMPILE_ARGS += --coverage-max-width 20000
    COMPILE_ARGS += --timing
    COMPILE_ARGS += -Wall -Wno-fatal

    EXTRA_ARGS   += --trace --trace-structs
    EXTRA_ARGS   += $(VERILATOR_COVERAGE)
    EXTRA_ARGS   += -I$(CFGDIR) -Wno-DECLFILENAME
else ifeq ($(SIM), vcs)
    EXTRA_ARGS   += +incdir+$(CFGDIR) -assert svaext -cm line+cond+fsm+tgl+branch +vcs+lic+wait -cm_libs yv -cm_hier $(CURDIR)/$(CM_FILE)
    PLUSARGS     += +dumpon
endif

COCOTB_HDL_TIMEUNIT ?= 1ns
COCOTB_HDL_TIMEPRECISION ?= 1ps

# Build directory
ifneq ($(COVERAGE_TYPE),)
    SIM_BUILD := sim-build-$(COVERAGE_TYPE)
endif

BUILD_ARGS = -j$(NPROC)

# -------------------------------------
# Make PyUVM test with Verilator
# -------------------------------------
include $(shell cocotb-config --makefiles)/Makefile.sim

$(SIM_BUILD)/Vtop.mk: $(VERILOG_SOURCES) $(CUSTOM_COMPILE_DEPS) $(COCOTB_SHARE_DIR)/lib/verilator/verilator.cpp | $(SIM_BUILD)
	$(CMD) -cc --exe -Mdir $(SIM_BUILD) -DCOCOTB_SIM=1 $(TOPMODULE_ARG) $(COMPILE_ARGS) $(EXTRA_ARGS) $(VERILOG_SOURCES) -f $(SIM_FLIST_FILE) $(COCOTB_SHARE_DIR)/lib/verilator/verilator.cpp

$(SIM_BUILD)/simv: $(VERILOG_SOURCES) $(SIM_BUILD)/pli.tab $(CUSTOM_COMPILE_DEPS) | $(SIM_BUILD)
	cd $(SIM_BUILD) && \
	$(CMD) -top $(TOPLEVEL) $(PLUSARGS) +acc+1 +vpi -P pli.tab +define+COCOTB_SIM=1 -sverilog \
  -timescale=$(COCOTB_HDL_TIMEUNIT)/$(COCOTB_HDL_TIMEPRECISION) \
  $(EXTRA_ARGS) -debug -load $(shell cocotb-config --lib-name-path vpi vcs) \
	$(COMPILE_ARGS) $(VERILOG_SOURCES) -f $(SIM_FLIST_FILE)

$(CFGDIR)/common_defines.vh:
	cd $(CURDIR) && $(CONFIG)/veer.config -fpga_optimize=0 $(CONF_PARAMS) $(EXTRA_CONFIG_OPTS)
	echo '`undef RV_ASSERT_ON' >> $(CFGDIR)/common_defines.vh
