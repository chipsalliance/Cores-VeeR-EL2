RISCV_DV_PATH   = $(RV_ROOT)/third_party/riscv-dv
RISCV_DV_TEST  ?= instr_base_test

WORK_DIR       ?= work
TEST_DIR        = $(WORK_DIR)/test_$(RISCV_DV_TEST)

UVM_VERBOSITY   = NONE
SEED            = 10
INSTR_COUNT     = 100

VEER_TARGET     = default
VEER_CONF       = -set build_axi4 \
                  -set reset_vec=0x2000

VERILATOR       = verilator
VERILATOR_CFLAGS= "-std=c++11"
VERILATOR_INC   = -I$(WORK_DIR) -I$(RV_ROOT)/testbench 
VERILATOR_EXE   = $(RV_ROOT)/testbench/test_tb_top.cpp

GCC_PREFIX      = riscv64-unknown-elf
ARCH            = rv32imc
ABI             = ilp32
#LDSCRIPT        = $(RV_ROOT)/testbench/link.ld
LDSCRIPT        = link.ld

HDL_FILES = $(WORK_DIR)/common_defines.vh \
            $(WORK_DIR)/el2_pdef.vh \
            $(RV_ROOT)/testbench/tb_top.sv \
            $(RV_ROOT)/testbench/ahb_sif.sv \
            $(RV_ROOT)/design/include/el2_def.sv

# Directory rules
$(WORK_DIR):
	mkdir -p $@

$(TEST_DIR):
	mkdir -p $@

# VeeR config
$(WORK_DIR)/defines.h: | $(WORK_DIR)
	BUILD_PATH=$(WORK_DIR) $(RV_ROOT)/configs/veer.config -target=$(VEER_TARGET) $(VEER_CONF)
	echo '`undef RV_ASSERT_ON' >> $(WORK_DIR)/common_defines.vh

# Verilated testbench rules
$(WORK_DIR)/verilator/Vtb_top.mk: $(WORK_DIR)/defines.h
	$(VERILATOR) --cc -CFLAGS $(VERILATOR_CFLAGS) $(VERILATOR_INC) \
        $(HDL_FILES) -f $(RV_ROOT)/testbench/flist --top-module tb_top \
		-exe $(VERILATOR_EXE) -Wno-WIDTH -Wno-UNOPTFLAT --autoflush \
		-Mdir $(WORK_DIR)/verilator

$(WORK_DIR)/verilator/Vtb_top: $(WORK_DIR)/verilator/Vtb_top.mk
	$(MAKE) -C $(WORK_DIR)/verilator -f Vtb_top.mk OPT_FAST="-O3"

# Generation rules
$(TEST_DIR)/program.s: | $(TEST_DIR)
	LD_LIBRARY_PATH=$(RISCV_DV_PATH)/euvm/build $(RISCV_DV_PATH)/euvm/build/riscv_instr_gen \
		+UVM_VERBOSITY=$(UVM_VERBOSITY) +random_seed=$(SEED) +instr_cnt=$(INSTR_COUNT) \
		+asm_file_name=$@ \
		+UVM_TESTNAME=riscv.test.riscv_instr_base_test.riscv_instr_base_test
	mv $@_0.S $@
	touch $(TEST_DIR)/user_define.h
	touch $(TEST_DIR)/user_init.s

# Compilation rules
$(TEST_DIR)/program.elf: $(TEST_DIR)/program.s $(LDSCRIPT)
	$(GCC_PREFIX)-gcc -march=$(ARCH) -mabi=$(ABI) -O0 -T$(LDSCRIPT) -I$(TEST_DIR) -static -nostdlib -nostartfiles $< -o $@
	$(GCC_PREFIX)-objdump -S $@ > $(basename $@).lst

$(TEST_DIR)/program.hex: $(TEST_DIR)/program.elf
	$(GCC_PREFIX)-objcopy -O verilog $< $@

# Run the ISS simulation
$(TEST_DIR)/iss_run.log: $(TEST_DIR)/program.elf
	spike -m0x2000:0x100000 --isa=$(ARCH) --log=$@ -l $<

# Run the HDL simulation
$(TEST_DIR)/hdl_run.log: $(WORK_DIR)/verilator/Vtb_top $(TEST_DIR)/program.hex
	cd $(TEST_DIR) && $(abspath $(WORK_DIR)/verilator/Vtb_top) 2>&1 | tee hdl_run.log

run: $(TEST_DIR)/run.log

clean:
	rm -rf $(WORK_DIR)

.PHONY: clean run
