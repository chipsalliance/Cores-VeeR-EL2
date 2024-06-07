RISCV_DV_PATH   = $(RV_ROOT)/third_party/riscv-dv
RISCV_DV_SIM   ?= pyflow
RISCV_DV_ISS   ?= spike
RISCV_DV_TEST  ?= riscv_arithmetic_basic_test
RISCV_DV_SEED  ?= 999
RISCV_DV_ITER  ?= 1
RISCV_DV_BATCH ?= 1

WORK_DIR       ?= work
TEST_DIR        = $(WORK_DIR)/test_$(RISCV_DV_TEST)
SIM_DIR         = $(TEST_DIR)/hdl_sim

VEER_TARGET     = default
VEER_CONF       = -set build_axi4 \
                  -set reset_vec=0x80000000

# Coverage reporting
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

VERILATOR       = verilator
VERILATOR_CFLAGS= "-std=c++14"
VERILATOR_INC   = -I$(WORK_DIR) -I$(RV_ROOT)/testbench 
VERILATOR_EXE   = $(RV_ROOT)/testbench/test_tb_top.cpp

HDL_FILES = $(WORK_DIR)/common_defines.vh \
            $(WORK_DIR)/el2_pdef.vh \
            $(RV_ROOT)/testbench/tb_top.sv \
            $(RV_ROOT)/testbench/ahb_sif.sv \
            $(RV_ROOT)/design/include/el2_def.sv

# riscv-dv args
RISCV_DV_ARGS = \
    --simulator $(RISCV_DV_SIM) \
    --test $(RISCV_DV_TEST) \
    --iss $(RISCV_DV_ISS) \
    --iss_timeout 60 \
    --start_seed $(RISCV_DV_SEED) \
    --iterations $(RISCV_DV_ITER) \
    --batch_size $(RISCV_DV_BATCH) \
    --isa rv32imc --mabi ilp32 \
    --custom_target $(PWD) \
    --testlist $(PWD)/testlist.yaml \
    -v -o $(TEST_DIR)

MAKEFILE  = $(abspath $(MAKEFILE_LIST))

all:
	@echo "Use 'make run'"

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
		-exe $(VERILATOR_EXE) -Wno-WIDTH -Wno-UNOPTFLAT -Wno-IMPLICITSTATIC --autoflush \
		$(VERILATOR_COVERAGE) \
		-Mdir $(WORK_DIR)/verilator

$(WORK_DIR)/verilator/Vtb_top: $(WORK_DIR)/verilator/Vtb_top.mk
	$(MAKE) -C $(WORK_DIR)/verilator -f Vtb_top.mk OPT_FAST="-O3"

# Code generation
$(TEST_DIR)/generate.log: | $(TEST_DIR)
	PYTHONPATH=$(RISCV_DV_PATH)/pygen python3 $(RISCV_DV_PATH)/run.py $(RISCV_DV_ARGS) \
    --steps gen
	@touch $@

# Code patching & compilation
$(TEST_DIR)/compile.log: $(TEST_DIR)
	# Patch the code
	find $(TEST_DIR)/asm_test -name "*.S" -exec python3 code_fixup.py -i {} -o {} \;
	# Compile, simulate
	PYTHONPATH=$(RISCV_DV_PATH)/pygen python3 $(RISCV_DV_PATH)/run.py $(RISCV_DV_ARGS) \
    --steps gcc_compile 2>&1 | tee $@

# ISS simulation
$(TEST_DIR)/iss_sim.log: $(TEST_DIR)/compile.log | $(TEST_DIR)
	# Compile, simulate
	PYTHONPATH=$(RISCV_DV_PATH)/pygen python3 $(RISCV_DV_PATH)/run.py $(RISCV_DV_ARGS) \
    --steps iss_sim 2>&1 | tee $@

$(TEST_DIR)/asm_test/%.hex: $(TEST_DIR)/asm_test/%.o
	$(RISCV_NM) -B -n $< > $(basename $@).sym
	$(RISCV_OBJCOPY) -O verilog $< $@

# HDL simulation
$(SIM_DIR)/%.log: $(TEST_DIR)/asm_test/%.hex $(WORK_DIR)/verilator/Vtb_top
	mkdir -p $(basename $@)
	cp $< $(basename $@)/program.hex
	cp $(basename $<).sym $(basename $@)/program.sym
	cd $(basename $@) && $(abspath $(WORK_DIR)/verilator/Vtb_top) --symbols program.sym --mailbox-sym tohost
	mv $(basename $@)/exec.log $@
	if [ -f "$(basename $@)/coverage.dat" ]; then mv $(basename $@)/coverage.dat $(basename $@)-coverage.dat; fi

# Log conversion rules
$(TEST_DIR)/spike_sim/%.csv: $(TEST_DIR)/spike_sim/%.log
	python3 $(RISCV_DV_PATH)/scripts/spike_log_to_trace_csv.py --log $< --csv $@

$(TEST_DIR)/whisper_sim/%.csv: $(TEST_DIR)/whisper_sim/%.log
	python3 $(RISCV_DV_PATH)/scripts/whisper_log_trace_csv.py --log $< --csv $@

$(TEST_DIR)/renode_sim/%.csv: $(TEST_DIR)/renode_sim/%.log
	python3 $(RISCV_DV_PATH)/scripts/renode_log_to_trace_csv.py --log $< --csv $@

$(SIM_DIR)/%.csv: $(SIM_DIR)/%.log veer_log_to_trace_csv.py
	PYTHONPATH=$(RISCV_DV_PATH)/scripts python3 veer_log_to_trace_csv.py --log $< --csv $@

# Trace comparison
$(TEST_DIR)/comp_%.log: $(TEST_DIR)/$(RISCV_DV_ISS)_sim/%.csv $(SIM_DIR)/%.csv
	rm -rf $@
	python3 $(RISCV_DV_PATH)/scripts/instr_trace_compare.py \
		--csv_file_1 $(word 1, $^) --csv_name_1 ISS --csv_file_2 $(word 2, $^) --csv_name_2 HDL \
		--in_order_mode 1 --log $@ --verbose 10 --mismatch_print_limit 20
	cat $@

# Coverage data aggregation
$(WORK_DIR)/coverage.dat:
	FILES=`find $(SIM_DIR)/ -name "*coverage.dat"`; \
	if [ "$${FILES}" != "" ]; then \
		verilator_coverage -write $@ $${FILES}; \
	else \
		touch $@ ; \
	fi

%.sv: %.py
	./$< $(RISCV_DV_PATH) $(RV_ROOT) > $@

generate:
	# Generate *.sv configuration
	#$(MAKE) -f $(MAKEFILE) riscv_core_setting.sv
	
	# Run RISC-V DV code generation
	$(MAKE) -f $(MAKEFILE) $(TEST_DIR)/generate.log

run:
	# Run RISC-V DV compilation and simulation
	$(MAKE) -f $(MAKEFILE) $(TEST_DIR)/iss_sim.log
	# Run HDL simulation(s) and trace comparison
	find $(TEST_DIR)/$(RISCV_DV_ISS)_sim -name "*.log" | sed 's|sim/|sim/../comp_|g' | xargs realpath --relative-to=$(PWD) | xargs $(MAKE) -f $(MAKEFILE)
	# Check for errors
	for F in $(TEST_DIR)/comp_*.log; do grep "\[PASSED\]" $$F; if [ $$? -ne 0 ]; then exit 255; fi; done
	# Aggregate coverage data
	$(MAKE) $(WORK_DIR)/coverage.dat

clean:
	rm -rf $(TEST_DIR)

fullclean:
	rm -rf $(WORK_DIR)

.PHONY: all generate run clean fullclean
.SECONDARY:
