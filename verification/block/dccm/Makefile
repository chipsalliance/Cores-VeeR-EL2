
null  :=
space := $(null) #
comma := ,

CURDIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
SRCDIR := $(abspath $(CURDIR)../../../../design)

TEST_FILES   = $(sort $(wildcard test_*.py))

MODULE      ?= $(subst $(space),$(comma),$(subst .py,,$(TEST_FILES)))
TOPLEVEL     = el2_lsu_dccm_mem_wrapper

VERILOG_SOURCES  = \
    $(CURDIR)/dccm/el2_lsu_dccm_mem_wrapper.sv \
    $(SRCDIR)/lsu/el2_lsu_dccm_mem.sv \
    $(SRCDIR)/lib/mem_lib.sv

# Undefine the VERILATOR macro to make the code use actual RAM cells instead
# of simulation models
EXTRA_ARGS += -UVERILATOR

include $(CURDIR)/../common.mk
