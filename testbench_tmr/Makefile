# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 Antmicro <www.antmicro.com>

# Check for RV_ROOT
ifeq (,$(wildcard $(RV_ROOT)/configs/veer.config))
$(error env var RV_ROOT does not point to a valid dir! Exiting!)
endif

BUILD_DIR ?= build

CONF_PARAMS ?= -set build_axi4
CONF_TARGET ?= default

TB_EXTRA_ARGS ?=

# Enable TMR
CONF_PARAMS := $(CONF_PARAMS) -set=triple_modular_redundancy_enable=1 -set=mubi_width=2 -set=mubi_false=0x1 -set=mubi_true=0x2

# Allow tool override
VEER_CONFIG = $(RV_ROOT)/configs/veer.config
VERILATOR = verilator

# Directorues
CONF_DIR = $(BUILD_DIR)/snapshots/$(CONF_TARGET)

# Testbench DPI sources
TB_DPI_SRCS = $(RV_ROOT)/testbench/jtagdpi/jtagdpi.c \
              $(RV_ROOT)/testbench/tcp_server/tcp_server.c

TB_DPI_INCS := $(addprefix -I$(TBDIR)/,$(dir $(TB_DPI_SRCS)))

# VeeR Config sources
CONF_SRCS = $(CONF_DIR)/common_defines.vh \
            $(RV_ROOT)/design/include/el2_def.sv \
            $(CONF_DIR)/el2_pdef.vh

# Testbench RTL sources
TB_SRCS = $(RV_ROOT)/testbench/tb_top_if.sv \
          $(RV_ROOT)/testbench/tb_top_pkg.sv \
          $(RV_ROOT)/testbench/ahb_sif.sv \
          $(RV_ROOT)/testbench/jtagdpi/jtagdpi.sv \
          $(RV_ROOT)/testbench/ahb_lite_2to1_mux.sv \
          $(RV_ROOT)/testbench/ahb_lsu_dma_bridge.sv \
          $(RV_ROOT)/testbench/axi4_mux/axi_crossbar_wrap_2x1.v \
          $(RV_ROOT)/testbench/axi4_mux/arbiter.v \
          $(RV_ROOT)/testbench/axi4_mux/axi_crossbar_addr.v \
          $(RV_ROOT)/testbench/axi4_mux/axi_crossbar_rd.v \
          $(RV_ROOT)/testbench/axi4_mux/axi_crossbar.v \
          $(RV_ROOT)/testbench/axi4_mux/axi_crossbar_wr.v \
          $(RV_ROOT)/testbench/axi4_mux/axi_register_rd.v \
          $(RV_ROOT)/testbench/axi4_mux/axi_register_wr.v \
          $(RV_ROOT)/testbench/axi4_mux/priority_encoder.v \
          $(RV_ROOT)/testbench_tmr/tb_top.sv

# Testbench includes
TB_INCS = -I$(BUILD_DIR) \
          -I$(RV_ROOT)/testbench/axi4_mux

CM_HIER_FILE = $(RV_ROOT)/cm.cfg

# Setup compilation flags
CFLAGS += -std=c++14

# =============================================================================

# Build/run directory
$(BUILD_DIR):
	mkdir -p $@

# Config
$(CONF_DIR)/defines.h: | $(BUILD_DIR)
	BUILD_PATH=$(CONF_DIR) $(VEER_CONFIG) -target $(CONF_TARGET) $(CONF_PARAMS)

# Verilate and compile
$(BUILD_DIR)/obj_dir/Vtb_top: $(CONF_DIR)/defines.h $(TB_SRCS) | $(BUILD_DIR)
	$(VERILATOR) --binary --main -Mdir $(BUILD_DIR)/obj_dir \
		--autoflush \
		--timing \
		--coverage-max-width 20000 \
		-CFLAGS "${CFLAGS}" \
		-I$(CONF_DIR) \
		$(CONF_SRCS) \
		-f $(RV_ROOT)/testbench/flist \
		$(TB_INCS) \
		$(TB_SRCS) \
		--top-module tb_top \
		-j 0 \
		--Wno-fatal --trace

build: $(BUILD_DIR)/obj_dir/Vtb_top 

# Run
run: $(BUILD_DIR)/obj_dir/Vtb_top
	cd $(BUILD_DIR) && obj_dir/Vtb_top $(TB_EXTRA_ARGS)

clean:
	rm -rf $(BUILD_DIR)

.PHONY: clean build run
