# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 Antmicro <www.antmicro.com>

ifndef PDK_PATH
$(warning PDK_PATH is not defined, `synth` target will fail.)
endif
ifndef PDK_LIBS
$(warning PDK_LIBS is not defined, `synth` target will fail.)
endif

YOSYS ?= yosys
PYTHON ?= python3
ALL_LIBS := $(shell find $(PDK_PATH) -type f -name '*.lib')
LIB_FILES := $(foreach l,$(PDK_LIBS),$(firstword $(filter %/$(l),$(ALL_LIBS))))
NETLIST_JSON := $(BUILD_DIR)/netlist.json

# Synthesis
LIB_ARGS := $(foreach f,$(LIB_FILES),-liberty $(f))
SLANG_ARGS := --top el2_veer_wrapper \
              --std latest --single-unit \
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
	$(YOSYS) -l $(BUILD_DIR)/synth.log $(BUILD_DIR)/synth.ys

synth: $(NETLIST_JSON)
