# SPDX-License-Identifier: Apache-2.0
# Copyright 2020 Western Digital Corporation or its affiliates.
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

# Check for RV_ROOT
ifeq (,$(wildcard ${RV_ROOT}/configs/swerv.config))
$(error env var RV_ROOT does not point to a valid dir! Exiting!)
endif

# Allow snapshot override
target = default
snapshot = $(target)

# Allow tool override
SWERV_CONFIG = ${RV_ROOT}/configs/swerv.config
IRUN = xrun
VCS = vcs
VLOG = qverilog
VERILATOR = verilator
GCC_PREFIX = riscv64-unknown-elf
BUILD_DIR = snapshots/${snapshot}
TBDIR = ${RV_ROOT}/testbench

# Define test name
TEST = hello_world

# Define test name
TEST_DIR = ${TBDIR}/asm
HEX_DIR = ${TBDIR}/hex

ifdef debug
 DEBUG_PLUS = +dumpon
 IRUN_DEBUG = -access +rc
 IRUN_DEBUG_RUN = -input ${RV_ROOT}/testbench/input.tcl
 VERILATOR_DEBUG = --trace
endif

# provide specific link file
ifeq (,$(wildcard $(TEST_DIR)/$(TEST).ld))
	LINK = $(TBDIR)/link.ld
else
	LINK = $(TEST_DIR)/$(TEST).ld
endif

VPATH = $(TEST_DIR) $(BUILD_DIR) $(TBDIR)
TBFILES = $(TBDIR)/tb_top.sv $(TBDIR)/ahb_sif.sv

defines  = $(BUILD_DIR)/common_defines.vh
defines += ${RV_ROOT}/design/include/el2_def.sv
defines += $(BUILD_DIR)/el2_pdef.vh
includes = -I${BUILD_DIR}

# CFLAGS for verilator generated Makefiles. Without -std=c++11 it
# complains for `auto` variables
CFLAGS += "-std=c++11"

# Optimization for better performance; alternative is nothing for
# slower runtime (faster compiles) -O2 for faster runtime (slower
# compiles), or -O for balance.
VERILATOR_MAKE_FLAGS = OPT_FAST="-O2"

# Targets
all: clean verilator

clean:
	rm -rf *.log *.s *.hex *.dis *.tbl irun* vcs* simv* snapshots swerv* \
	verilator* *.exe obj* *.o ucli.key vc_hdrs.h csrc *.csv work

# If define files do not exist, then run swerv.config.
${BUILD_DIR}/defines.h :
	BUILD_PATH=${BUILD_DIR} ${RV_ROOT}/configs/swerv.config -target=$(target) $(CONF_PARAMS)

verilator-build: ${TBFILES} ${BUILD_DIR}/defines.h test_tb_top.cpp
	echo '`undef ASSERT_ON' >> ${BUILD_DIR}/common_defines.vh
	$(VERILATOR) '-UASSERT_ON' --cc -CFLAGS ${CFLAGS} $(defines) \
	  $(includes) -I${RV_ROOT}/testbench -f ${RV_ROOT}/testbench/flist \
	  -Wno-WIDTH -Wno-UNOPTFLAT ${TBFILES} --top-module tb_top \
	  -exe test_tb_top.cpp --autoflush $(VERILATOR_DEBUG)
	cp ${RV_ROOT}/testbench/test_tb_top.cpp obj_dir/
	$(MAKE) -C obj_dir/ -f Vtb_top.mk $(VERILATOR_MAKE_FLAGS)
	touch verilator-build

vcs-build: ${TBFILES} ${BUILD_DIR}/defines.h
	$(VCS) -full64 -assert svaext -sverilog +define+RV_OPENSOURCE \
	  +error+500 +incdir+${RV_ROOT}/design/lib \
	  +incdir+${RV_ROOT}/design/include ${BUILD_DIR}/common_defines.vh \
	  +incdir+$(BUILD_DIR)  +libext+.v $(defines) \
	  -f ${RV_ROOT}/testbench/flist ${TBFILES} -l vcs.log
	touch vcs-build

irun-build: ${TBFILES} ${BUILD_DIR}/defines.h
	$(IRUN) -64bit -elaborate $(IRUN_DEBUG) -q -sv -sysv  -nowarn CUVIHR \
	  -xmlibdirpath . -xmlibdirname swerv.build \
	  -incdir ${RV_ROOT}/design/lib -incdir ${RV_ROOT}/design/include \
	  -vlog_ext +.vh+.h $(defines) -incdir $(BUILD_DIR) \
	  -f ${RV_ROOT}/testbench/flist -top tb_top  ${TBFILES} \
	  -I${RV_ROOT}/testbench -elaborate  -snapshot ${snapshot}
	touch irun-build

verilator: program.hex verilator-build
	./obj_dir/Vtb_top

irun: program.hex irun-build
	$(IRUN) -64bit -abvglobalfailurelimit 1 +lic_queue -licqueue \
	  -status -xmlibdirpath . -xmlibdirname swerv.build \
	  -snapshot ${snapshot} -r $(snapshot) $(IRUN_DEBUG_RUN)

vcs: program.hex vcs-build
	./simv $(DEBUG_PLUS) +vcs+lic+wait  -l vcs.log

vlog: program.hex ${TBFILES} ${BUILD_DIR}/defines.h
	$(VLOG) -l vlog.log -sv -mfcu +incdir+${BUILD_DIR}+${RV_ROOT}/design/include+${RV_ROOT}/design/lib\
        $(defines) -f ${RV_ROOT}/testbench/flist ${TBFILES} -R ${DEBUG_PLUS}


ifeq ($(shell which $(GCC_PREFIX)-gcc 2> /dev/null),)
program.hex: ${BUILD_DIR}/defines.h
	@echo " !!! No $(GCC_PREFIX)-gcc in path, using canned hex files !!"
	cp ${HEX_DIR}/$(TEST).program.hex program.hex
	cp ${HEX_DIR}/$(TEST).data.hex data.hex
else
ifneq (,$(wildcard $(TEST_DIR)/$(TEST).makefile))
program.hex:
	$(MAKE) -f $(TEST_DIR)/$(TEST).makefile
else
program.hex: $(TEST).o $(LINK)
	@echo Building $(TEST)
	$(GCC_PREFIX)-ld -m elf32lriscv --discard-none -T$(LINK) -o $(TEST).exe $(TEST).o
	$(GCC_PREFIX)-objcopy -O verilog --only-section ".data*" --change-section-lma .data*-0x10000 $(TEST).exe data.hex
	$(GCC_PREFIX)-objcopy -O verilog --only-section ".text*"  $(TEST).exe program.hex
	$(GCC_PREFIX)-objdump -S  $(TEST).exe > $(TEST).dis
	$(GCC_PREFIX)-nm -f posix -C $(TEST).exe > $(TEST).tbl
	@echo Completed building $(TEST)


%.o : %.s ${BUILD_DIR}/defines.h
	$(GCC_PREFIX)-cpp -I${BUILD_DIR}  $<  > $(TEST).cpp.s
	$(GCC_PREFIX)-as -march=rv32gc $(TEST).cpp.s -o $(TEST).o

TEST_CFLAGS = -g -O3 -funroll-all-loops
ABI = -mabi=ilp32 -march=rv32imc

%.o : %.c ${BUILD_DIR}/defines.h
	$(GCC_PREFIX)-gcc -I${BUILD_DIR} ${TEST_CFLAGS} ${ABI} -nostdlib -c $< -o $@	
endif
endif


help:
	@echo Make sure the environment variable RV_ROOT is set.
	@echo Possible targets: verilator vcs irun vlog help clean all verilator-build irun-build vcs-build program.hex

.PHONY: help clean verilator vcs irun vlog
