# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 Antmicro <www.antmicro.com>

comma := ,
empty :=
space := $(empty) $(empty)

ifndef PDK_PATH
$(warning PDK_PATH is not defined, `synth` and `faultergeist` targets will fail.)
endif
ifndef PDK_LIBS
$(warning PDK_LIBS is not defined, `synth` and `faultergeist` targets will fail.)
endif

TMR_CONF_PARAMS  = -set=triple_modular_redundancy_enable=1 -set=mubi_width=2 -set=mubi_false=0x1 -set=mubi_true=0x2
# Set DMA AXI port ID width to accommodate AXI infrastructure
TMR_CONF_PARAMS += -set=dma_bus_tag=6

YOSYS ?= yosys
FAULTERGEIST ?= faultergeist-gen
PYTHON ?= python3
GEN_CONFIG = $(PYTHON) $(RV_ROOT)/tools/gen_faultergeist_config.py
ALL_LIBS := $(shell find $(PDK_PATH) -type f -name '*.lib')
LIB_FILES := $(filter $(addprefix %/,$(PDK_LIBS)),$(ALL_LIBS))
FAULT_CAMPAIGN_FILE := $(BUILD_DIR)/fault_campaign_out.csv
CONFIG_JSON := $(BUILD_DIR)/config.json
NETLIST_JSON := $(BUILD_DIR)/netlist.json

FI_MODEL_NAME ?= random
FI_SIM_TIME ?= 10us
FI_NUM_OF_EVENTS ?= 30
FI_VEER_IDX ?= 0

ifeq ($(FI),1)
VERILATOR_FI_COMPILE_ARGS := \
	--vpi \
	$(CURDIR)/config.vlt \
	$$(pkg-config --libs faultergeist) \
	-DFAULT_INJECTION_ENABLE \
	-DFAULT_CAMPAIGN_FILE=\"$(CURDIR)/$(FAULT_CAMPAIGN_FILE)\"
VERILATOR_FI_SIM_ARGS := FI_LOG_LEVEL="info"
endif

ifneq ($(TB_MAX_CYCLES),)
	VERILATOR_TB_MAX_CYCLES := +maxCycles=$(TB_MAX_CYCLES)
endif

# Verilate and compile
$(BUILD_DIR)/obj_dir/Vtb_top_tmr: $(BUILD_DIR)/defines.h $(TB_SRCS) $(if $(findstring $(FI),1), synth faultergeist)
	$(VERILATOR) --binary --main -Mdir $(BUILD_DIR)/obj_dir \
		--autoflush \
		--timing \
		--coverage-max-width 20000 \
		-CFLAGS "$(CFLAGS)" \
		$(defines) \
		-f $(RV_ROOT)/testbench/flist \
		$(includes) -I${RV_ROOT}/testbench \
		$(VERILATOR_SKIP_WARNINGS) \
		$(TBFILES) $(VERILATOR_FI_COMPILE_ARGS) \
		--top-module tb_top_tmr \
		--timescale $(TIMESCALE) \
		$(VERILATOR_DEBUG) \
		$(VERILATOR_COVERAGE) \
		-MAKEFLAGS $(VERILATOR_MAKE_FLAGS) \
		-j $(shell nproc)

verilator-build: $(BUILD_DIR)/obj_dir/Vtb_top_tmr

verilator: $(BUILD_DIR)/obj_dir/Vtb_top_tmr program.hex
	cp program.hex $(BUILD_DIR)/
	$(VERILATOR_FI_SIM_ARGS) $(BUILD_DIR)/obj_dir/Vtb_top_tmr \
		$(VERILATOR_TB_MAX_CYCLES) $(TB_EXTRA_ARGS)

# Synthesis
LIB_ARGS := $(foreach f,$(LIB_FILES),-liberty $(f))

$(NETLIST_JSON): $(RV_ROOT)/tools/synth.tcl $(BUILD_DIR)/defines.h
	export BUILD_DIR="$(BUILD_DIR)" && \
	export LIB_FILES="$(LIB_FILES)" && \
	export LIB_ARGS="$(LIB_ARGS)" && \
	export NETLIST_JSON="$(NETLIST_JSON)" && \
	export TOP="$(TOP)" && \
	export DEFINES="$(defines)" && \
	export INCLUDES="$(includes)" && \
	$(YOSYS) -c $(RV_ROOT)/tools/synth.tcl

synth: $(NETLIST_JSON)

# Fault injection campaign
LIB_PATHS := $(subst $(space),$(comma),$(strip $(LIB_FILES)))
CONFIG_ARGS := \
	--model-name $(FI_MODEL_NAME) \
	--num-of-events $(FI_NUM_OF_EVENTS) \
	--simulation-time $(FI_SIM_TIME) \
	--sig-path-prefix tb_top_tmr.rvtop_wrapper.rvtop.tmr_complex.cores[$(FI_VEER_IDX)] \
	--top-module el2_veer\$$el2_veer_wrapper.tmr_complex.cores[$(FI_VEER_IDX)].veer \
	--top-instance veer \
	--netlist-path $(NETLIST_JSON) \
	--fault-campaign-out $(FAULT_CAMPAIGN_FILE) \
	--thread-count $(shell nproc) \
	--liberty-paths $(LIB_PATHS)

$(CONFIG_JSON):
	$(GEN_CONFIG) $(CONFIG_ARGS) -o $@

$(FAULT_CAMPAIGN_FILE): $(CONFIG_JSON)
	$(FAULTERGEIST) --config_file $(CONFIG_JSON)

faultergeist: $(FAULT_CAMPAIGN_FILE) $(NETLIST_JSON)
