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
FI_NUM_OF_EVENTS ?= 10000
FI_SIM_TIME ?= 10ms

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
$(BUILD_DIR)/obj_dir/Vtb_top_tmr: $(BUILD_DIR)/defines.h $(TB_SRCS) $(if $(findstring $(FI),1), faultergeist)
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
SLANG_ARGS := --top el2_veer_wrapper \
              --std latest --single-unit \
              --best-effort-hierarchy \
              --allow-toplevel-iface-ports \
              --allow-hierarchical-const \
              --libraries-inherit-macros \
              --no-implicit-memories \
              $(defines) \
              $(includes) \
              -F $(RV_ROOT)/design/flist

$(BUILD_DIR)/synth.ys: $(BUILD_DIR)/defines.h
	$(file  >$@,read_liberty -overwrite -setattr liberty_cell -lib $(LIB_FILES))
	$(file >>$@,read_slang $(SLANG_ARGS))
	$(file >>$@,synth -noabc -top el2_veer_wrapper)
	$(file >>$@,clean)
	$(file >>$@,rename -wire)
	$(file >>$@,dfflibmap $(LIB_ARGS))
	$(file >>$@,abc $(LIB_ARGS))
	$(file >>$@,write_verilog $(BUILD_DIR)/netlist.v)
	$(file >>$@,write_json $(NETLIST_JSON))
	$(file >>$@,check -assert -mapped)

$(NETLIST_JSON): $(BUILD_DIR)/synth.ys $(BUILD_DIR)/defines.h
	$(YOSYS) $(BUILD_DIR)/synth.ys

synth: $(NETLIST_JSON)

# Fault injection campaign
LIB_PATHS := $(subst $(space),$(comma),$(strip $(LIB_FILES)))
CONFIG_ARGS := \
	--model-name $(FI_MODEL_NAME) \
	--num-of-events $(FI_NUM_OF_EVENTS) \
	--simulation-time $(FI_SIM_TIME) \
	--sig-path-prefix tb_top_tmr.rvtop_wrapper \
	--top-module el2_veer_wrapper \
	--top-instance rvtop \
	--netlist-path $(NETLIST_JSON) \
	--fault-campaign-out $(FAULT_CAMPAIGN_FILE) \
	--thread-count $(shell nproc) \
	--liberty-paths $(LIB_PATHS)

$(CONFIG_JSON):
	$(GEN_CONFIG) $(CONFIG_ARGS) -o $@

$(FAULT_CAMPAIGN_FILE): $(CONFIG_JSON)
	$(FAULTERGEIST) --config_file $(CONFIG_JSON)

faultergeist: $(FAULT_CAMPAIGN_FILE) $(NETLIST_JSON)
