
null  :=
space := $(null) #
comma := ,

TEST_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
SRCDIR := $(abspath $(TEST_DIR)../../../../design)

TEST_FILES   = $(sort $(wildcard test_*.py))

MODULE      ?= $(subst $(space),$(comma),$(subst .py,,$(TEST_FILES)))
TOPLEVEL     = el2_ifu_iccm_mem_wrapper

VERILOG_SOURCES  = \
    $(SRCDIR)/lib/el2_mem_if.sv \
    $(TEST_DIR)/el2_ifu_iccm_mem_wrapper.sv \
    $(SRCDIR)/ifu/el2_ifu_iccm_mem.sv \
    $(SRCDIR)/lib/mem_lib.sv

# Undefine the VERILATOR macro to make the code use actual RAM cells instead
# of simulation models
EXTRA_ARGS += -UVERILATOR

include $(TEST_DIR)/../common.mk
