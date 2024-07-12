# SPDX-License-Identifier: Apache-2.0
# Copyright 2020 Western Digital Corporation or its affiliates.
# Copyright 2024 Antmicro <www.antmicro.com>
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

ifeq ($(USER_MODE),1)
USER_MODE_OPTS = -set=user_mode=1
else
USER_MODE_OPTS =
endif

CONF_PARAMS ?= -set build_axi4 $(USER_MODE_OPTS)

TEST_CFLAGS = -g -gdwarf -O3 -funroll-all-loops
ABI = -mabi=ilp32
LD_ABI = $(ABI) -march=rv32imac

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

# Override march depending on used GCC version
ifneq ($(shell which $(GCC_PREFIX)-gcc 2> /dev/null),)
	GCCVERSIONGT11 := $(shell expr `$(GCC_PREFIX)-gcc -dumpversion | cut -f1 -d.` \>= 11)
	ifeq "$(GCCVERSIONGT11)" "1"
		CC_ABI = $(ABI) -march=rv32imc_zicsr_zifencei_zba_zbb_zbc_zbs
	else
		CC_ABI = $(ABI) -march=rv32imc
	endif
endif

# Determine verilator version if possible. Set the flag accordingly. Since
# version v5.006 -Wno-IMPLICIT was renamed to -Wno-IMPLICITSTATIC
VERILATOR_NOIMPLICIT := -Wno-IMPLICITSTATIC
VERILATOR_VERSION    := $(subst .,,$(word 2,$(shell $(VERILATOR) --version)))

ifeq ("$(.SHELLSTATUS)", "0")
    $(shell test $(VERILATOR_VERSION) -lt 5006)
    ifeq ("$(.SHELLSTATUS)", "0")
        VERILATOR_NOIMPLICIT := -Wno-IMPLICIT
    endif
endif

VERILATOR_SKIP_WARNINGS = $(VERILATOR_NOIMPLICIT) -Wno-TIMESCALEMOD -Wno-ASCRANGE \
	-Wno-CASEINCOMPLETE -Wno-INITIALDLY -Wno-WIDTH -Wno-UNOPTFLAT

# Define test name
TEST = hello_world
TEST_DIR = ${TBDIR}/asm
HEX_DIR = ${TBDIR}/hex

# Coverage reporting
# TODO: Set flags for other tools here as well
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

ifdef assert
 ASSERT_DEFINES = +define+RV_ASSERT_ON
endif

# provide specific link file
ifeq (,$(wildcard $(TEST_DIR)/$(TEST).ld))
	LINK = $(BUILD_DIR)/link.ld
else
	LINK = $(TEST_DIR)/$(TEST).ld
endif

VPATH = $(TEST_DIR) $(BUILD_DIR) $(TBDIR)

-include $(TEST_DIR)/$(TEST).mki

# Testbench DPI sources
TB_DPI_SRCS = jtagdpi/jtagdpi.c \
              tcp_server/tcp_server.c

TB_DPI_INCS := $(addprefix -I$(TBDIR)/,$(dir $(TB_DPI_SRCS)))
# Add testbench include paths
CFLAGS += $(TB_DPI_INCS)

TB_DPI_SRCS := $(addprefix $(TBDIR)/,$(TB_DPI_SRCS))

# Testbench sources
TB_VERILATOR_SRCS = $(TBDIR)/test_tb_top.cpp $(TB_DPI_SRCS)

TBFILES = $(TBDIR)/tb_top_pkg.sv \
          $(TBDIR)/tb_top.sv \
          $(TBDIR)/ahb_sif.sv \
          $(TBDIR)/jtagdpi/jtagdpi.sv \
          $(TBDIR)/ahb_lite_2to1_mux.sv

defines  = $(BUILD_DIR)/common_defines.vh
defines += ${RV_ROOT}/design/include/el2_def.sv
defines += $(BUILD_DIR)/el2_pdef.vh
includes = -I${BUILD_DIR} -I$(TBDIR)/axi4_mux

# Verilator supports only C++14 and newer
CFLAGS += -std=c++14

# Optimization for better performance; alternative is nothing for
# slower runtime (faster compiles) -O2 for faster runtime (slower
# compiles), or -O for balance.
VERILATOR_MAKE_FLAGS = OPT_FAST="-Os"

# Targets
all: clean verilator

clean:
	rm -rf *.log *.s *.hex *.dis *.tbl irun* vcs* simv* *.map snapshots veer* \
	verilator* *.exe obj* *.o *.sym ucli.key vc_hdrs.h csrc *.csv work \
	dataset.asdb library.cfg vsimsa.cfg riviera-build wave.asdb



############ Model Builds ###############################

# If define files do not exist, then run veer.config.
${BUILD_DIR}/defines.h:
	BUILD_PATH=${BUILD_DIR} ${RV_ROOT}/configs/veer.config -target=$(target) $(CONF_PARAMS)

verilator-build: ${TBFILES} ${BUILD_DIR}/defines.h $(TB_VERILATOR_SRCS)
	$(VERILATOR)  --cc -CFLAGS "${CFLAGS}" $(defines) \
	  $(includes) -I${RV_ROOT}/testbench -f ${RV_ROOT}/testbench/flist \
	  $(VERILATOR_SKIP_WARNINGS) ${TBFILES} --top-module tb_top \
	  -exe $(TB_VERILATOR_SRCS) --autoflush --timing $(VERILATOR_DEBUG) $(VERILATOR_COVERAGE)
	cp ${RV_ROOT}/testbench/test_tb_top.cpp obj_dir/
	$(MAKE) -e -C obj_dir/ -f Vtb_top.mk $(VERILATOR_MAKE_FLAGS)
	touch verilator-build

vcs-build: ${TBFILES} ${BUILD_DIR}/defines.h
	$(VCS) -full64 -assert svaext -sverilog +define+RV_OPENSOURCE $(ASSERT_DEFINES) \
	  +error+500 +incdir+${RV_ROOT}/design/lib \
	  +incdir+${RV_ROOT}/design/include ${BUILD_DIR}/common_defines.vh \
	  +incdir+$(BUILD_DIR)  +libext+.v $(defines) \
	  -f ${RV_ROOT}/testbench/flist ${TBFILES} -l vcs.log
	touch vcs-build

irun-build: ${TBFILES} ${BUILD_DIR}/defines.h
	$(IRUN) -64bit -elaborate $(IRUN_DEBUG) $(ASSERT_DEFINES) -q -sv -sysv -nowarn CUVIHR \
	  -xmlibdirpath . -xmlibdirname veer.build \
	  -incdir ${RV_ROOT}/design/lib -incdir ${RV_ROOT}/design/include \
	  -vlog_ext +.vh+.h $(defines) -incdir $(BUILD_DIR) \
	  -f ${RV_ROOT}/testbench/flist -top tb_top  ${TBFILES} \
	  -I${RV_ROOT}/testbench -elaborate  -snapshot ${snapshot} $(profile)
	touch irun-build

riviera-build: ${TBFILES} ${BUILD_DIR}/defines.h
	vlib work
	vlog -work work ${ASSERT_DEFINES} \
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
	# FIXME: Assuming here that either begin_signature or end_signature implies
	# that both symbols are present.
	grep -E "(begin|end)_signature" $(TEST).sym >/dev/null 2>&1; \
	if [ $$? -eq 0 ]; then \
		BEG=`grep "begin_signature" $(TEST).sym | cut -d\  -f 1`;\
		END=`grep "end_signature"   $(TEST).sym | cut -d\  -f 1`;\
		./obj_dir/Vtb_top --mem-signature $${BEG} $${END}; \
	else \
		./obj_dir/Vtb_top; \
	fi

irun: program.hex irun-build
	$(IRUN) -64bit -abvglobalfailurelimit 1 +lic_queue -licqueue \
	  -status -xmlibdirpath . -xmlibdirname veer.build \
	  -snapshot ${snapshot} -r $(snapshot) $(IRUN_DEBUG_RUN) $(profile)

vcs: program.hex vcs-build
	./simv $(DEBUG_PLUS) +vcs+lic+wait  -l vcs.log

vlog: program.hex ${TBFILES} ${BUILD_DIR}/defines.h
	$(VLOG) -l vlog.log -sv -mfcu +incdir+${BUILD_DIR}+${RV_ROOT}/design/include+${RV_ROOT}/design/lib \
        $(ASSERT_DEFINES) $(defines) -f ${RV_ROOT}/testbench/flist ${TBFILES} -R +nowarn3829 +nowarn2583 ${DEBUG_PLUS}

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
program.hex: picolibc $(OFILES) ${BUILD_DIR}/defines.h
	@echo Building $(TEST)
	$(GCC_PREFIX)-gcc $(LD_ABI) --verbose -Wl,-Map=$(TEST).map -T$(LINK) --specs=$(PICOLIBC_DIR)/picolibc.specs $(TEST_LIBS) -nostartfiles $(OFILES) -o $(TEST).exe
	$(GCC_PREFIX)-objcopy -O verilog  $(TEST).exe program.hex
	$(GCC_PREFIX)-objdump -S  $(TEST).exe > $(TEST).dis
	$(GCC_PREFIX)-nm -B -n $(TEST).exe > $(TEST).sym
	@echo Completed building $(TEST)


%.o : %.s ${BUILD_DIR}/defines.h
	$(GCC_PREFIX)-cpp -I${BUILD_DIR}  $<  > $*.cpp.s
	$(GCC_PREFIX)-as ${CC_ABI} $*.cpp.s -o $@


%.o : %.c picolibc ${BUILD_DIR}/defines.h
	$(GCC_PREFIX)-gcc ${includes} --specs=$(PICOLIBC_DIR)/picolibc.specs ${TEST_CFLAGS} -DCOMPILER_FLAGS="\"${TEST_CFLAGS}\"" ${CC_ABI} -c $< -o $@

endif
endif


help:
	@echo Make sure the environment variable RV_ROOT is set.
	@echo Possible targets: verilator vcs irun vlog riviera help clean all verilator-build irun-build vcs-build riviera-build program.hex

.PHONY: help clean picolibc verilator vcs irun vlog riviera

