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

CONF_PARAMS = -set build_axi4

TEST_CFLAGS = -g -O3 -funroll-all-loops
ABI = -mabi=ilp32 -march=rv32imac

# Check for RV_ROOT
ifeq (,$(wildcard ${RV_ROOT}/configs/veer.config))
$(error env var RV_ROOT does not point to a valid dir! Exiting!)
endif

# Allow snapshot override
target = default
snapshot = $(target)

# Allow tool override
VEER_CONFIG = ${RV_ROOT}/configs/veer.config
IRUN = xrun
VCS = vcs
VLOG = qverilog
VERILATOR = verilator
RIVIERA = riviera
GCC_PREFIX = riscv64-unknown-elf
BUILD_DIR = snapshots/${snapshot}
TBDIR = ${RV_ROOT}/testbench
PICOLIBC_DIR = ${RV_ROOT}/third_party/picolibc/install

# Define test name
TEST = hello_world
TEST_DIR = ${TBDIR}/asm
HEX_DIR = ${TBDIR}/hex

# Determine test directory
ifneq (,$(wildcard $(TBDIR)/tests/$(TEST)))
  TEST_DIR = $(TBDIR)/tests/$(TEST)
endif

OFILES = $(TEST).o

ifdef debug
 DEBUG_PLUS = +dumpon
 IRUN_DEBUG = -access +rc
 IRUN_DEBUG_RUN = -input ${RV_ROOT}/testbench/input.tcl
 VCS_DEBUG = -debug_access
 VERILATOR_DEBUG = --trace
 RIVIERA_DEBUG = +access +r
endif

# provide specific link file
ifeq (,$(wildcard $(TEST_DIR)/$(TEST).ld))
	LINK = $(BUILD_DIR)/link.ld
else
	LINK = $(TEST_DIR)/$(TEST).ld
endif

VPATH = $(TEST_DIR) $(BUILD_DIR) $(TBDIR)

-include $(TEST_DIR)/$(TEST).mki


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
VERILATOR_MAKE_FLAGS = OPT_FAST="-Os"

# Targets
all: clean verilator

clean:
	rm -rf *.log *.s *.hex *.dis *.tbl irun* vcs* simv* *.map snapshots veer* \
	verilator* *.exe obj* *.o ucli.key vc_hdrs.h csrc *.csv work\
	dataset.asdb  library.cfg vsimsa.cfg  riviera-build wave.asdb



############ Model Builds ###############################

# If define files do not exist, then run veer.config.
${BUILD_DIR}/defines.h:
	BUILD_PATH=${BUILD_DIR} ${RV_ROOT}/configs/veer.config -target=$(target) $(CONF_PARAMS)

verilator-build: ${TBFILES} ${BUILD_DIR}/defines.h test_tb_top.cpp
	echo '`undef RV_ASSERT_ON' >> ${BUILD_DIR}/common_defines.vh
	$(VERILATOR)  --cc -CFLAGS ${CFLAGS} $(defines) \
	  $(includes) -I${RV_ROOT}/testbench -f ${RV_ROOT}/testbench/flist \
	  -Wno-WIDTH -Wno-UNOPTFLAT ${TBFILES} --top-module tb_top \
	  -exe test_tb_top.cpp --autoflush $(VERILATOR_DEBUG)
	cp ${RV_ROOT}/testbench/test_tb_top.cpp obj_dir/
	$(MAKE) -j -e -C obj_dir/ -f Vtb_top.mk $(VERILATOR_MAKE_FLAGS)
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
	  -xmlibdirpath . -xmlibdirname veer.build \
	  -incdir ${RV_ROOT}/design/lib -incdir ${RV_ROOT}/design/include \
	  -vlog_ext +.vh+.h $(defines) -incdir $(BUILD_DIR) \
	  -f ${RV_ROOT}/testbench/flist -top tb_top  ${TBFILES} \
	  -I${RV_ROOT}/testbench -elaborate  -snapshot ${snapshot} $(profile)
	touch irun-build

riviera-build: ${TBFILES} ${BUILD_DIR}/defines.h
	vlib work
	vlog -work work \
		+incdir+${RV_ROOT}/design/lib \
		+incdir+${RV_ROOT}/design/include \
		+incdir+${BUILD_DIR} \
		-y ${RV_ROOT}/design/lib +libext+.v+.vh \
		$(defines) \
		-f ${RV_ROOT}/testbench/flist \
		${TBFILES}
	touch riviera-build

############ TEST Simulation ###############################

verilator: program.hex verilator-build
	./obj_dir/Vtb_top

irun: program.hex irun-build
	$(IRUN) -64bit -abvglobalfailurelimit 1 +lic_queue -licqueue \
	  -status -xmlibdirpath . -xmlibdirname veer.build \
	  -snapshot ${snapshot} -r $(snapshot) $(IRUN_DEBUG_RUN) $(profile)

vcs: program.hex vcs-build
	./simv $(DEBUG_PLUS) +vcs+lic+wait  -l vcs.log

vlog: program.hex ${TBFILES} ${BUILD_DIR}/defines.h
	$(VLOG) -l vlog.log -sv -mfcu +incdir+${BUILD_DIR}+${RV_ROOT}/design/include+${RV_ROOT}/design/lib\
        $(defines) -f ${RV_ROOT}/testbench/flist ${TBFILES}  -R +nowarn3829 +nowarn2583 ${DEBUG_PLUS}

riviera: program.hex riviera-build
	vsim -c -lib work ${DEBUG_PLUS} ${RIVIERA_DEBUG} tb_top -do "run -all; exit" -l riviera.log



############ TEST build ###############################

picolibc:
	$(MAKE) -f ${RV_ROOT}/tools/picolibc.mk all

ifeq ($(shell which $(GCC_PREFIX)-gcc 2> /dev/null),)
program.hex: picolibc ${BUILD_DIR}/defines.h
	@echo " !!! No $(GCC_PREFIX)-gcc in path, using canned hex files !!"
	cp ${HEX_DIR}/$(TEST).hex program.hex
else
ifneq (,$(wildcard $(TEST_DIR)/$(TEST).makefile))
program.hex: picolibc
	@echo Building $(TEST) via $(TEST_DIR)/$(TEST).makefile
	$(MAKE) -f $(TEST_DIR)/$(TEST).makefile
else
program.hex: picolibc $(OFILES) $(LINK)
	@echo Building $(TEST)
	$(GCC_PREFIX)-gcc $(ABI) --verbose -Wl,-Map=$(TEST).map -T$(LINK) --specs=$(PICOLIBC_DIR)/picolibc.specs $(TEST_LIBS) -nostartfiles $(OFILES) -o $(TEST).exe
	$(GCC_PREFIX)-objcopy -O verilog  $(TEST).exe program.hex
	$(GCC_PREFIX)-objdump -S  $(TEST).exe > $(TEST).dis
	@echo Completed building $(TEST)


%.o : %.s ${BUILD_DIR}/defines.h
	$(GCC_PREFIX)-cpp -I${BUILD_DIR}  $<  > $*.cpp.s
	$(GCC_PREFIX)-as ${ABI} $*.cpp.s -o $@


%.o : %.c picolibc ${BUILD_DIR}/defines.h
	$(GCC_PREFIX)-gcc ${includes} --specs=$(PICOLIBC_DIR)/picolibc.specs ${TEST_CFLAGS} -DCOMPILER_FLAGS="\"${TEST_CFLAGS}\"" ${ABI} -c $< -o $@

endif
endif


help:
	@echo Make sure the environment variable RV_ROOT is set.
	@echo Possible targets: verilator vcs irun vlog riviera help clean all verilator-build irun-build vcs-build riviera-build program.hex

.PHONY: help clean picolibc verilator vcs irun vlog riviera

