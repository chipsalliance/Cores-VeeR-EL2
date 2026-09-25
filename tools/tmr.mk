# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 Antmicro <www.antmicro.com>

CONF_PARAMS := $(CONF_PARAMS) -set build_axi4 -set=triple_modular_redundancy_enable=1 -set=mubi_width=2 -set=mubi_false=0x1 -set=mubi_true=0x2
TB_TOP ?= tb_top_tmr

# Verilate and compile
$(BUILD_DIR)/obj_dir/Vtb_top_tmr: $(BUILD_DIR)/defines.h $(TB_SRCS)
	$(VERILATOR) --binary --main -Mdir $(BUILD_DIR)/obj_dir \
		--autoflush \
		--timing \
		--coverage-max-width 20000 \
		-CFLAGS "$(CFLAGS)" \
		$(defines) \
		-f $(RV_ROOT)/testbench/flist \
		$(includes) -I${RV_ROOT}/testbench \
		$(VERILATOR_SKIP_WARNINGS) \
		$(TBFILES) \
		--top-module tb_top_tmr \
		-j 0 \
		$(VERILATOR_DEBUG)

verilator-build: $(BUILD_DIR)/obj_dir/Vtb_top_tmr

verilator: $(BUILD_DIR)/obj_dir/Vtb_top_tmr
	cd $(BUILD_DIR) && obj_dir/Vtb_top_tmr $(TB_EXTRA_ARGS)
