RISCV_DV_PATH   = $(RV_ROOT)/third_party/riscv-dv
RISCV_DV_TEST  ?= instr_base_test

WORK_DIR       ?= work
TEST_DIR        = $(WORK_DIR)/test_$(RISCV_DV_TEST)

UVM_VERBOSITY   = NONE
SEED            = 10
INSTR_COUNT     = 100

VEER_TARGET     = default
VEER_CONF       = -set build_axi4 \
                  -set reset_vec=0x2000 # Needed for spike

VERILATOR       = verilator
VERILATOR_CFLAGS= "-std=c++11"
VERILATOR_INC   = -I$(WORK_DIR) -I$(RV_ROOT)/testbench 
VERILATOR_EXE   = $(RV_ROOT)/testbench/test_tb_top.cpp

GCC_PREFIX      = riscv64-unknown-elf
ARCH            = rv32imc
ABI             = ilp32
LDSCRIPT        = link.ld

HDL_FILES = $(WORK_DIR)/common_defines.vh \
            $(WORK_DIR)/el2_pdef.vh \
            $(RV_ROOT)/testbench/tb_top.sv \
            $(RV_ROOT)/testbench/ahb_sif.sv \
            $(RV_ROOT)/design/include/el2_def.sv

all: compare

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
$(TEST_DIR)/program.s: code_fixup.py | $(TEST_DIR)
	riscv_instr_gen \
		+UVM_VERBOSITY=$(UVM_VERBOSITY) +random_seed=$(SEED) +instr_cnt=$(INSTR_COUNT) \
		+asm_file_name=$@ \
		+UVM_TESTNAME=riscv.test.riscv_instr_base_test.riscv_instr_base_test \
		+num_of_tests=1 \
		+start_idx=0 \
		+num_of_sub_programs=0 \
		+instr_cnt=10 \
		+no_branch_jump=true \
		+no_csr_instr=true \
		+no_fence=true \
		+no_data_page=true
	python3 code_fixup.py -i $@_0.S -o $@
	touch $(TEST_DIR)/user_define.h
	touch $(TEST_DIR)/user_init.s

# Compilation rules
$(TEST_DIR)/program.elf: $(TEST_DIR)/program.s $(LDSCRIPT)
	$(GCC_PREFIX)-gcc -march=$(ARCH) -mabi=$(ABI) -O0 -T$(LDSCRIPT) -I$(TEST_DIR) -static -nostdlib -nostartfiles $< -o $@
	$(GCC_PREFIX)-objdump -S $@ > $(basename $@).lst
	$(GCC_PREFIX)-nm -n $@ > $(basename $@).sym

$(TEST_DIR)/program.hex: $(TEST_DIR)/program.elf
	$(GCC_PREFIX)-objcopy -O verilog $< $@

# Run the ISS simulation
$(TEST_DIR)/iss_trace.log: $(TEST_DIR)/program.elf
	timeout --foreground 10s spike -m0x2000:0x100000 --isa=$(ARCH) --misaligned --log=$@ --log-commits -l $< || true

$(TEST_DIR)/iss_trace.csv: $(TEST_DIR)/iss_trace.log
	python3 $(RISCV_DV_PATH)/scripts/spike_log_to_trace_csv.py --log $< --csv $@

# Run the HDL simulation
$(TEST_DIR)/hdl_trace.log: $(WORK_DIR)/verilator/Vtb_top $(TEST_DIR)/program.hex
	cd $(TEST_DIR) && $(abspath $(WORK_DIR)/verilator/Vtb_top)
	mv $(TEST_DIR)/exec.log $@

$(TEST_DIR)/hdl_trace.csv: $(TEST_DIR)/hdl_trace.log veer_log_to_trace_csv.py
	PYTHONPATH=$(RISCV_DV_PATH)/scripts python3 veer_log_to_trace_csv.py --log $< --csv $@

$(TEST_DIR)/comparison.log: $(TEST_DIR)/iss_trace.csv $(TEST_DIR)/hdl_trace.csv
	rm -rf $@
	python3 $(RISCV_DV_PATH)/scripts/instr_trace_compare.py \
		--csv_file_1 $(TEST_DIR)/iss_trace.csv --csv_name_1 ISS --csv_file_2 $(TEST_DIR)/hdl_trace.csv --csv_name_2 HDL \
		--in_order_mode 1 --log $@ --verbose 10 --mismatch_print_limit 20

compare: $(TEST_DIR)/comparison.log
	@grep "\[PASSED\]" $<

clean:
	rm -rf $(TEST_DIR)

fullclean:
	rm -rf $(WORK_DIR)

.PHONY: clean fullclean compare
