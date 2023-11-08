all: simulate

# -------------------------------------
# Testbench setup
# -------------------------------------
# Check for RV_ROOT
ifeq (,$(wildcard ${RV_ROOT}/configs/veer.config))
$(error env var RV_ROOT does not point to a valid dir! Exiting!)
endif

VERILATOR ?= verilator
ifdef VERILATOR_ROOT
VERILATOR := $(VERILATOR_ROOT)/bin/verilator
endif

# Check for Verilator
ifeq ($(shell which $(VERILATOR)),)
$(error Verilator not found! Exiting!)
endif

# Check Verilator version
VERILATOR_VERSION := $(shell $(VERILATOR) --version)
VERILATOR_RECOMMENDED_COMMIT := df36e9ca2
ifeq ($(findstring $(VERILATOR_RECOMMENDED_COMMIT),$(VERILATOR_VERSION)),)
$(warning Using $(VERILATOR_VERSION))
$(warning It is recommended to use Verilator revision: https://github.com/antmicro/verilator-1/commit/$(VERILATOR_RECOMMENDED_COMMIT))
endif

UVM_ROOT ?= uvm
UVM_TEST ?= mem_wr_rd_test
SNAPSHOT = verilator-uvm

VERILOG_DEFINE_FILES = \
    ${UVM_ROOT}/src/uvm.sv \
    ${RV_ROOT}/snapshots/$(SNAPSHOT)/common_defines.vh \
    ${RV_ROOT}/design/include/el2_def.sv \
	${RV_ROOT}/snapshots/$(SNAPSHOT)/el2_pdef.vh

VERILOG_INCLUDE_DIRS = \
    hdl \
    ${UVM_ROOT}/src \
    ${RV_ROOT}/design/include \
	${RV_ROOT}/snapshots/$(SNAPSHOT)

VERILOG_SOURCES = \
    ${RV_ROOT}/design/lib/beh_lib.sv \
    ${RV_ROOT}/design/lib/mem_lib.sv \
	$(SIM_DIR)/el2_lsu_dccm_mem.sv \
	hdl/tbench_top.sv

# -------------------------------------
# Compilation/simulation configuration
# -------------------------------------
SIM_NAME ?= mem_tb
SIM_DIR := $(SIM_NAME)-sim
COMPILE_ARGS += --top-module tbench_top
COMPILE_ARGS += -DUVM_NO_DPI
COMPILE_ARGS += --prefix $(SIM_NAME) -o $(SIM_NAME)
COMPILE_ARGS += $(addprefix +incdir+, $(VERILOG_INCLUDE_DIRS))
EXTRA_ARGS += --timescale 1ns/1ps --error-limit 100 --trace --trace-structs
WARNING_ARGS += -Wno-lint \
	-Wno-style \
	-Wno-SYMRSVDWORD \
	-Wno-IGNOREDRETURN \
	-Wno-CONSTRAINTIGN \
	-Wno-ZERODLY

# -------------------------------------
#  Fetch UVM
# -------------------------------------
$(UVM_ROOT):
	git clone https://github.com/antmicro/uvm-verilator -b current-patches $(UVM_ROOT)

# -------------------------------------
# Configure VeeR EL-2
# -------------------------------------
$(RV_ROOT)/snapshots/$(SNAPSHOT)/el2_param.vh:
	$(RV_ROOT)/configs/veer.config -snapshot=$(SNAPSHOT) -fpga_optimize=0

# FIXME: Patch source to disable "ifdef VERILATOR". Can't undef it as it has to be set for UVM sources.
$(SIM_DIR)/el2_lsu_dccm_mem.sv:
	mkdir -p $(SIM_DIR)
	sed 's/ifdef VERILATOR/ifdef XXXX/g' $(RV_ROOT)/design/lsu/el2_lsu_dccm_mem.sv > $(SIM_DIR)/el2_lsu_dccm_mem.sv

# -------------------------------------
# Make UVM test with Verilator
# -------------------------------------
verilate: ${UVM_ROOT} $(RV_ROOT)/snapshots/$(SNAPSHOT)/el2_param.vh $(VERILOG_SOURCES) $(wildcard hdl/*.sv)
	$(VERILATOR) --cc --exe --main --timing -Mdir $(SIM_DIR) \
	${COMPILE_ARGS} ${EXTRA_ARGS} \
	${VERILOG_DEFINE_FILES} \
	${VERILOG_SOURCES} \
	${WARNING_ARGS}

build: verilate
	$(MAKE) -C $(SIM_DIR) $(BUILD_ARGS) -f $(SIM_NAME).mk

simulate: build
	$(SIM_DIR)/$(SIM_NAME) +UVM_TESTNAME=$(UVM_TEST)

clean:
	rm -rf snapshots
	rm -rf simv*.daidir csrc
	rm -rf csrc* simv*
	rm -rf *.vcd *.fst
	rm -rf $(SIM_DIR)
	rm -rf $(UVM_DIR)


.PHONY: verilate build simulate clean
